// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[macro_use]
extern crate log;
#[macro_use]
extern crate rustc;
extern crate rustc_incremental;
extern crate rustc_trans;
extern crate syntax;

mod collector;

use rustc::session::config::OutputFilenames;
use rustc::ty::{self, Ty, TyCtxt};
use rustc::util::common::time;
use rustc::util::nodemap::FxHashSet;
use rustc_incremental::IncrementalHashesMap;
use rustc_trans::{base, back};
use rustc_trans::context::SharedCrateContext;
use rustc_trans::monomorphize::Instance;
use rustc_trans::trans_item::DefPathBasedNames;
use syntax::ast::NodeId;

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum TransItem<'tcx> {
    Fn(Instance<'tcx>),
    Static(NodeId),
}

impl<'a, 'tcx> TransItem<'tcx> {
    pub fn to_string(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>) -> String {
        let hir_map = &tcx.hir;

        return match *self {
            TransItem::Fn(instance) => {
                to_string_internal(tcx, "fn ", instance)
            },
            TransItem::Static(node_id) => {
                let def_id = hir_map.local_def_id(node_id);
                let instance = Instance::new(def_id, tcx.intern_substs(&[]));
                to_string_internal(tcx, "static ", instance)
            },
        };

        fn to_string_internal<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                        prefix: &str,
                                        instance: Instance<'tcx>)
                                        -> String {
            let mut result = String::with_capacity(32);
            result.push_str(prefix);
            let printer = DefPathBasedNames::new(tcx, false, false);
            printer.push_instance_as_string(instance, &mut result);
            result
        }
    }
}

pub fn trans_crate<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    analysis: ty::CrateAnalysis,
    incremental_hashes_map: &IncrementalHashesMap,
    output_filenames: &OutputFilenames,
) {
    let ty::CrateAnalysis { reachable, .. } = analysis;
    let exported_symbols = base::find_exported_symbols(tcx, &reachable);
    let check_overflow = tcx.sess.overflow_checks();
    let link_meta = back::link::build_link_meta(incremental_hashes_map);

    let shared_ccx = SharedCrateContext::new(tcx,
                                             exported_symbols,
                                             check_overflow,
                                             output_filenames);

    let translation_items = collect_translation_items(&shared_ccx);
}

fn collect_translation_items<'a, 'tcx>(scx: &SharedCrateContext<'a, 'tcx>)
    -> FxHashSet<TransItem<'tcx>>
{
    let time_passes = scx.sess().time_passes();
    time(time_passes, "translation item collection", || {
        collector::collect_crate_translation_items(&scx)
    })
}
