
#![feature(rustc_private)]

extern crate env_logger;
extern crate getopts;
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_errors as errors;
extern crate rustc_incremental;
extern crate rustc_metadata;
extern crate rustc_lint;
extern crate rustc_shader;
extern crate rustc_trans;
extern crate syntax;

use rustc::dep_graph::DepGraph;
use rustc::lint;
use rustc::session::config::{self, Input, OutputFilenames};
use rustc::session::{build_session, early_error, Session};
use rustc::util::common::time;
use rustc_driver::{driver, Compilation, CompilerCalls};
use rustc_metadata::cstore::CStore;

use std::path::PathBuf;
use std::process;
use std::rc::Rc;

use syntax::ast;

struct AlthaeacCompilerCalls;

impl<'a> CompilerCalls<'a> for AlthaeacCompilerCalls {
    fn build_controller(&mut self,
                        _: &Session,
                        _: &getopts::Matches)
                        -> driver::CompileController<'a> {
        let mut control = driver::CompileController::basic();

        control.after_analysis.stop = Compilation::Stop;
        control.after_analysis.callback = Box::new(move |state| {
            state.session.abort_if_errors();

            let tcx = state.tcx.unwrap();
            let time_passes = state.session.time_passes();

            // Need to recompute as we don't have directly access to it via CompilerCalls
            let incremental_hashes_map =
                time(time_passes,
                     "compute_incremental_hashes_map",
                     || rustc_incremental::compute_incremental_hashes_map(tcx));

            {
                println!("Pre-trans");
                tcx.print_debug_stats();
            }

            let out_dir  = state.out_dir.map(|path| path.to_path_buf());
            let out_file = state.out_file.map(|path| path.to_path_buf());

            let outputs = driver::build_output_filenames(
                state.input,
                &out_dir,
                &out_file,
                &state.hir_crate.unwrap().attrs,
                state.session);

            time(time_passes,
                 "translation",
                 move || rustc_shader::trans_crate(tcx, state.analysis.unwrap().clone(), &incremental_hashes_map, &outputs));

            {
                println!("Post-trans");
                tcx.print_debug_stats();
            }
        });

        control
    }

    fn no_input(&mut self,
                matches: &getopts::Matches,
                sopts: &config::Options,
                cfg: &ast::CrateConfig,
                odir: &Option<PathBuf>,
                ofile: &Option<PathBuf>,
                descriptions: &errors::registry::Registry)
                -> Option<(Input, Option<PathBuf>)> {
        match matches.free.len() {
            0 => {
                if sopts.describe_lints {
                    let mut ls = lint::LintStore::new();
                    rustc_lint::register_builtins(&mut ls, None);
                    // TODO: describe_lints(&ls, false);
                    return None;
                }
                let dep_graph = DepGraph::new(sopts.build_dep_graph());
                let cstore = Rc::new(CStore::new(&dep_graph, Box::new(rustc_trans::LlvmMetadataLoader)));
                let sess = build_session(sopts.clone(),
                    &dep_graph,
                    None,
                    descriptions.clone(),
                    cstore.clone());
                rustc_lint::register_builtins(&mut sess.lint_store.borrow_mut(), Some(&sess));
                let mut cfg = config::build_configuration(&sess, cfg.clone());
                // target_features::add_configuration(&mut cfg, &sess);
                let should_stop = rustc_driver::RustcDefaultCalls::print_crate_info(&sess, None, odir, ofile);
                if should_stop == Compilation::Stop {
                    return None;
                }
                early_error(sopts.error_format, "no input filename given");
            }
            1 => panic!("make_input should have provided valid inputs"),
            _ => early_error(sopts.error_format, "multiple input filenames provided"),
        }
    }

    fn late_callback(&mut self,
                     matches: &getopts::Matches,
                     sess: &Session,
                     input: &Input,
                     odir: &Option<PathBuf>,
                     ofile: &Option<PathBuf>)
                     -> Compilation {
        rustc_driver::RustcDefaultCalls::print_crate_info(sess, Some(input), odir, ofile)
            .and_then(|| rustc_driver::RustcDefaultCalls::list_metadata(sess, matches, input))
    }
}

fn main() {
    env_logger::init().unwrap();

    let compiler_args = ["-h", "--help"];
    let mut rustc_args: Vec<String> =
        std::env::args().filter(|arg| !compiler_args.contains(&arg.as_ref())).collect();

    for flag in std::env::args().filter(|arg| compiler_args.contains(&arg.as_ref())) {
        match flag.as_ref() {
            "-h" | "--help" => {
                let usage = "althaeac [OPTIONS] INPUT \n\nOptions: \n    -h, --help    Display \
                             this message";
                println!("usage: {}", usage);
                process::exit(0);
            }
            _ => panic!("unexpected compiler flag: {}", flag),
        }
    }

    let mut compiler_calls = AlthaeacCompilerCalls;
    let result = rustc_driver::run(move || rustc_driver::run_compiler(&rustc_args, &mut compiler_calls, None, None));
    process::exit(result as i32);
}