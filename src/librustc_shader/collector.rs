// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::hir;
use rustc::hir::def_id::DefId;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use rustc::ty::subst::Substs;
use rustc::util::common::time;
use rustc::util::nodemap::{DefIdMap, FxHashSet};
use rustc_trans;
use rustc_trans::collector::def_id_to_string;
use rustc_trans::common::{def_ty, instance_ty};
use rustc_trans::context::SharedCrateContext;
use rustc_trans::monomorphize::Instance;
use TransItem;

pub fn collect_crate_translation_items<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>)
    -> FxHashSet<TransItem<'tcx>>
{
    // We are not tracking dependencies of this pass as it has to be re-executed
    // every time no matter what.
    scx.tcx().dep_graph.with_ignore(|| {
        let roots = collect_roots(scx);

        debug!("Building translation item graph, beginning at roots");
        let mut visited = FxHashSet();
        let mut recursion_depths = DefIdMap();

        for root in roots {
            collect_items_rec(scx,
                              root,
                              &mut visited,
                              &mut recursion_depths);
        }

        visited
    })
}

// Collect all monomorphized translation items reachable from `starting_point`
fn collect_items_rec<'a, 'tcx: 'a>(scx: &SharedCrateContext<'a, 'tcx>,
                                   starting_point: TransItem<'tcx>,
                                   visited: &mut FxHashSet<TransItem<'tcx>>,
                                   recursion_depths: &mut DefIdMap<usize>) {
    if !visited.insert(starting_point.clone()) {
        // We've been here already, no need to search again.
        return;
    }
    debug!("BEGIN collect_items_rec({})", starting_point.to_string(scx.tcx()));

    let mut neighbors = Vec::new();
    let recursion_depth_reset;

    match starting_point {
        TransItem::Static(node_id) => {
            let def_id = scx.tcx().hir.local_def_id(node_id);
            let instance = Instance::mono(scx.tcx(), def_id);

            // TODO: we inline everything!
            // Sanity check whether this ended up being collected accidentally
            // debug_assert!(should_trans_locally(scx.tcx(), &instance));

            let ty = instance_ty(scx, &instance);
            // TODO:
            // visit_drop_use(scx, ty, true, &mut neighbors);

            recursion_depth_reset = None;

            collect_neighbours(scx, instance, &mut neighbors);
        }
        TransItem::Fn(instance) => {
            // TODO: we inline everything!
            // Sanity check whether this ended up being collected accidentally
            // debug_assert!(should_trans_locally(scx.tcx(), &instance));

            // Keep track of the monomorphization recursion depth
            recursion_depth_reset =
                Some(rustc_trans::collector::check_recursion_limit(scx.tcx(),
                                                               instance,
                                                               recursion_depths));
            rustc_trans::collector::check_type_length_limit(scx.tcx(), instance);

            collect_neighbours(scx, instance, &mut neighbors);
        }
    }

    for neighbour in neighbors {
        collect_items_rec(scx, neighbour, visited, recursion_depths);
    }

    if let Some((def_id, depth)) = recursion_depth_reset {
        recursion_depths.insert(def_id, depth);
    }

    debug!("END collect_items_rec({})", starting_point.to_string(scx.tcx()));
}

// Find all non-generic items by walking the HIR. These items serve as roots to
// start monomorphizing from.
pub fn collect_roots<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>)
                               -> Vec<TransItem<'tcx>>
{
    debug!("Collecting roots");
    let mut roots = Vec::new();

    {
        let mut visitor = RootCollector {
            scx: scx,
            output: &mut roots,
        };

        scx.tcx().hir.krate().visit_all_item_likes(&mut visitor);
    }

    // We can only translate items that are instantiable - items all of
    // whose predicates hold. Luckily, items that aren't instantiable
    // can't actually be used, so we can just skip translating them.
    // roots.retain(|root| root.is_instantiable(scx.tcx())); TODO:
    roots
}

struct RootCollector<'b, 'a: 'b, 'tcx: 'a + 'b> {
    scx: &'b SharedCrateContext<'a, 'tcx>,
    output: &'b mut Vec<TransItem<'tcx>>,
}

impl<'b, 'a, 'v> ItemLikeVisitor<'v> for RootCollector<'b, 'a, 'v> {
    fn visit_item(&mut self, item: &'v hir::Item) {
        match item.node {
            hir::ItemExternCrate(..) |
            hir::ItemUse(..)         |
            hir::ItemForeignMod(..)  |
            hir::ItemTy(..)          |
            hir::ItemDefaultImpl(..) |
            hir::ItemTrait(..)       |
            hir::ItemMod(..)         => {
                // Nothing to do, just keep recursing...
            }

            hir::ItemImpl(..) => {
                create_trans_items_for_default_impls(self.scx,
                                                     item,
                                                     self.output);
            }

            hir::ItemEnum(_, ref generics) |
            hir::ItemStruct(_, ref generics) |
            hir::ItemUnion(_, ref generics) => {
                if !generics.is_parameterized() {
                    let def_id = self.scx.tcx().hir.local_def_id(item.id);
                    debug!("RootCollector: ADT drop-glue for {}",
                           def_id_to_string(self.scx.tcx(), def_id));

                    let ty = def_ty(self.scx, def_id, Substs::empty());
                    // visit_drop_use(self.scx, ty, true, self.output); TODO: ?
                }
            }
            hir::ItemGlobalAsm(..) => {
                debug!("Unsupported asm item");
                // TODO
            }
            hir::ItemStatic(..) => {
                debug!("RootCollector: ItemStatic({})",
                       def_id_to_string(self.scx.tcx(),
                                        self.scx.tcx().hir.local_def_id(item.id)));
                self.output.push(TransItem::Static(item.id));
            }
            hir::ItemConst(..) => {
                // const items only generate translation items if they are
                // actually used somewhere. Just declaring them is insufficient.
            }
            hir::ItemFn(.., ref generics, _) => {
                if !generics.is_type_parameterized() {
                    let def_id = self.scx.tcx().hir.local_def_id(item.id);

                    debug!("RootCollector: ItemFn({})",
                           def_id_to_string(self.scx.tcx(), def_id));

                    let instance = Instance::mono(self.scx.tcx(), def_id);
                    self.output.push(TransItem::Fn(instance));
                }
            }
        }
    }

    fn visit_trait_item(&mut self, _: &'v hir::TraitItem) {
        // Even if there's a default body with no explicit generics,
        // it's still generic over some `Self: Trait`, so not a root.
    }

    fn visit_impl_item(&mut self, ii: &'v hir::ImplItem) {
        match ii.node {
            hir::ImplItemKind::Method(hir::MethodSig {
                ref generics,
                ..
            }, _) => {
                let hir_map = &self.scx.tcx().hir;
                let parent_node_id = hir_map.get_parent_node(ii.id);
                let is_impl_generic = match hir_map.expect_item(parent_node_id) {
                    &hir::Item {
                        node: hir::ItemImpl(_, _, _, ref generics, ..),
                        ..
                    } => {
                        generics.is_type_parameterized()
                    }
                    _ => {
                        bug!()
                    }
                };

                if !generics.is_type_parameterized() && !is_impl_generic {
                    let def_id = self.scx.tcx().hir.local_def_id(ii.id);

                    debug!("RootCollector: MethodImplItem({})",
                           def_id_to_string(self.scx.tcx(), def_id));

                    let instance = Instance::mono(self.scx.tcx(), def_id);
                    self.output.push(TransItem::Fn(instance));
                }
            }
            _ => { /* Nothing to do here */ }
        }
    }
}

fn create_trans_items_for_default_impls<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                                  item: &'tcx hir::Item,
                                                  output: &mut Vec<TransItem<'tcx>>) {
    /*
    let tcx = scx.tcx();
    match item.node {
        hir::ItemImpl(_,
                      _,
                      _,
                      ref generics,
                      ..,
                      ref impl_item_refs) => {
            if generics.is_type_parameterized() {
                return
            }

            let impl_def_id = tcx.hir.local_def_id(item.id);

            debug!("create_trans_items_for_default_impls(item={})",
                   def_id_to_string(tcx, impl_def_id));

            if let Some(trait_ref) = tcx.impl_trait_ref(impl_def_id) {
                let callee_substs = tcx.erase_regions(&trait_ref.substs);
                let overridden_methods: FxHashSet<_> =
                    impl_item_refs.iter()
                                  .map(|iiref| iiref.name)
                                  .collect();
                for method in tcx.provided_trait_methods(trait_ref.def_id) {
                    if overridden_methods.contains(&method.name) {
                        continue;
                    }

                    if !tcx.generics_of(method.def_id).types.is_empty() {
                        continue;
                    }

                    let instance =
                        monomorphize::resolve(scx, method.def_id, callee_substs);

                    let trans_item = create_fn_trans_item(instance);
                    if trans_item.is_instantiable(tcx) && should_trans_locally(tcx, &instance) {
                        output.push(trans_item);
                    }
                }
            }
        }
        _ => {
            bug!()
        }
    }
    */
}

fn collect_neighbours<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>,
                                instance: Instance<'tcx>,
                                output: &mut Vec<TransItem<'tcx>>)
{
    // TODO:
    /*
    let mir = scx.tcx().instance_mir(instance.def);

    let mut visitor = MirNeighborCollector {
        scx: scx,
        mir: &mir,
        output: output,
        param_substs: instance.substs
    };

    visitor.visit_mir(&mir);
    for promoted in &mir.promoted {
        visitor.mir = promoted;
        visitor.visit_mir(promoted);
    }
    */
}