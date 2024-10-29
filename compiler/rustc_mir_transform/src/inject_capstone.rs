#![allow(unused)]

// use itertools::Itertools;
// use std::collections::VecDeque;
use rustc_middle::mir::patch::MirPatch;
use rustc_middle::ty::ty_kind::TyKind;
use rustc_middle::ty::{TypeAndMut, Ty};
use crate::{Spanned};
use rustc_index::{IndexVec, IndexSlice};
use rustc_middle::mir::*;
use rustc_middle::mir::visit::MutVisitor;
use rustc_middle::ty::{self, ParamEnv, TyCtxt};
// use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_span::def_id::{DefIndex, DefId, CrateNum};
use rustc_middle::ty::{List, GenericArg};
use rustc_span::DUMMY_SP;
static SPANS: [rustc_span::Span; 1] = [DUMMY_SP];

// Taken directly from another Rust MIR pass
struct BasicBlockUpdater<'tcx> {
    map: IndexVec<BasicBlock, BasicBlock>,
    tcx: TyCtxt<'tcx>,
}

// Taken directly from another Rust MIR pass
impl<'tcx> MutVisitor<'tcx> for BasicBlockUpdater<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(&mut self, terminator: &mut Terminator<'tcx>, _location: Location) {
        for succ in terminator.successors_mut() {
            *succ = self.map[*succ];
        }
    }
}

// Taken directly from another Rust MIR pass
// fn permute<I: rustc_index::Idx + Ord, T>(data: &mut IndexVec<I, T>, map: &IndexSlice<I, I>) {
    // FIXME: It would be nice to have a less-awkward way to apply permutations,
    // but I don't know one that exists.  `sort_by_cached_key` has logic for it
    // internally, but not in a way that we're allowed to use here.
//     let mut enumerated: Vec<_> = std::mem::take(data).into_iter_enumerated().collect();
//     enumerated.sort_by_key(|p| map[p.0]);
//     *data = enumerated.into_iter().map(|p| p.1).collect();
// }

pub struct InjectCapstone;

fn get_func_def_id<'ctx>(tcx: TyCtxt<'ctx>, crate_num_opt: Option<CrateNum>, func_name: &str) -> Option<DefId> {
    match crate_num_opt {
        Some (crate_num) => {
            // Dynamically locate the function we want to inject, instead of hardcoding its definition index
            let def_index = DefIndex::from_usize(0);
            let mut _def_id = DefId { krate: crate_num, index: def_index };
            let mut _def_id_int = 0;
            let mut name = tcx.def_path_str(_def_id);

            // Check whether the thing being borrowed was mutable. This changes the nature of the function we are injecting.
            // Future note: I am unsure if two different functions based on this is even required. Rapturecell should definitely have the two functions, for manual injection needs it.
            // But it may not be necessary for injecting at the MIR level. Mutability consistency is checked before this level is reached.
            while !name.ends_with(func_name) {
                _def_id_int += 1;
                _def_id = DefId { krate: crate_num, index: DefIndex::from_usize(_def_id_int) };
                name = tcx.def_path_str(_def_id);
            }
            if !name.ends_with(func_name) {
                None
            } else {
                Some(_def_id)
            }
        }
        None => {
            // look for it locally
            tcx.iter_local_def_id().find_map(
                |local_def_id| {
                    if tcx.def_path_str(local_def_id.to_def_id()).ends_with(func_name) {
                        Some (local_def_id.to_def_id())
                    } else {
                        None
                    }
                }
            )
        }
    }
}

fn get_borrow_func_name(m: &Mutability, is_ref: bool, is_local: bool) -> &'static str {
    if is_local {
        match (*m, is_ref) {
            (Mutability::Mut, false) => "rapture::borrow_mut",
            (Mutability::Not, false) => "rapture::borrow",
            (Mutability::Mut, true) => "rapture::borrow_mut_ref",
            (Mutability::Not, true) => "rapture::borrow_ref",
        }
    } else {
        match (*m, is_ref) {
            (Mutability::Mut, false) => "rapture::borrow_mut",
            (Mutability::Not, false) => "rapture::borrow",
            (Mutability::Mut, true) => "rapture::borrow_mut_ref",
            (Mutability::Not, true) => "rapture::borrow_ref",
        }
    }
}

fn get_pointee_type<'ctx>(ty : Ty<'ctx>) -> Option<Ty<'ctx>> {
    match ty.kind() {
        ty::RawPtr(TypeAndMut {ty : inner_ty, ..}) => Some(*inner_ty),
        ty::Ref(_, inner_ty, _) => Some(*inner_ty),
        _ => None
    }
}

fn insert_borrow<'ctx>(tcx: TyCtxt<'ctx>, rapture_crate_number : Option<CrateNum>,
        patch: &mut MirPatch<'ctx>, bb: BasicBlock, data: &mut BasicBlockData<'ctx>, i: usize,
        mutability: &Mutability, lhs_type: Ty<'ctx>, lhs: &Place<'ctx>) {
    // Shift all the statements beyond our target statement to a new vector and clear them from the original block
    let new_stmts = data.statements.split_off(i + 1);

    // Create an intermediary block that will be inserted between the current block and the next block
    // This block has to point to the next block in the control flow graph (that terminator is an Option type)
    let borrow_block = patch.new_block(BasicBlockData {
        statements: new_stmts.clone(),
        terminator: Some(data.terminator.as_ref().unwrap().clone()),
        is_cleanup: data.is_cleanup.clone(),
    });

    let def_id = get_func_def_id(tcx, rapture_crate_number,
        get_borrow_func_name(mutability, lhs_type.is_ref(), rapture_crate_number.is_none())
    ).expect("Unable to find function.");

    let root_ty = get_pointee_type(lhs_type).unwrap();

    // The generic argument that goes inside the <> brackets of the function call. This is why we obtained the root type
    let generic_arg = GenericArg::from(root_ty);
    let generic_args = tcx.mk_args(&[generic_arg]);

    // Creating the sugar of all the structures for the function type to be injected
    let ty_ = Ty::new(tcx, ty::FnDef(def_id, generic_args));
    let const_ = Const::Val(ConstValue::ZeroSized, ty_);
    let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
    let operand_ = Operand::Constant(const_operand);

    // println!("Operand: {:?}", operand_);    // The function is uniquely denoted by an Operand type; this is not to be confused with the arguments to the function

    let dest_place = Place {local: (lhs.local).into(), projection: List::empty()};  // Every function has to have a target place where it will store its return value

    // This is how we create the arguments to be passed to the function that we are calling
    let operand_input = Operand::Copy(Place {local: lhs.local, projection: List::empty()});
    let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

    // println!("Spanned Operand: {:?}", spanned_operand);   // This is the actual argument

    let unwind_action = if data.is_cleanup {
        UnwindAction::Terminate(UnwindTerminateReason::InCleanup)
    }
    else {
        UnwindAction::Continue
    };

    // Create a block terminator that will execute the function call we want to inject. This terminator points from current block to our intermediary block
    let intermediary_terminator = TerminatorKind::Call {
        func: operand_,
        args: vec![spanned_operand],
        destination: dest_place,
        target: Some(borrow_block),
        unwind: unwind_action,
        call_source: CallSource::Normal,
        fn_span: SPANS[0],
    };

    patch.patch_terminator(bb, intermediary_terminator);
}


fn first_pass<'ctx>(tcx: TyCtxt<'ctx>, body: &mut Body<'ctx>,
        rapture_crate_number : Option<CrateNum>, local_decls : &IndexVec<Local, LocalDecl<'ctx>>) {
    let func_path_str = tcx.def_path_str(body.source.def_id());
    if func_path_str.contains("rapture") || func_path_str.contains("mem::uninitialized") {
        // we don't do this to rapture itself
        return;
    }
    let param_env = tcx.param_env(body.source.def_id());
    loop {
        let mut patch = MirPatch::new(body);
        let mut _patch_empty = true;


        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            // FIXME: it's not correct to always skip the last statement
            for (i, stmt) in data.statements.clone().iter().enumerate().rev().skip(1) {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                        let lhs_type = (*local_decls)[lhs.local].ty;

                        // println!("\nGeneric RHS: {:?}", rhs);
                        match rhs {
                            // (It is not always clear what the things we see in the rust source level deconstructs to at the MIR level.)
                            // Candidates: Cast, Ref, AdressOf. And technically Use as well, but that's just moving the same pointer around.
                            Rvalue::AddressOf(mutability, place) => {
                                // Seems that this only includes getting raw addresses?
                                if !place.is_indirect_first_projection() || (*local_decls)[place.local].ty.is_ref() {
                                    match lhs_type.kind() {
                                        crate::ty::RawPtr(tm)=> {
                                            if tm.ty.is_sized(tcx, param_env) {
                                                // && lhs_type.peel_refs().is_sized(tcx, ParamEnv::reveal_all()) {
                                                eprintln!("Ok this is the place {:?} type {:?} {:?}", place, lhs_type, lhs_type.peel_refs());
                                                insert_borrow(tcx, rapture_crate_number, &mut patch, bb, data,
                                                    i, mutability, lhs_type, lhs);
                                                _patch_empty = false;
                                                break;
                                            }
                                        },
                                        _ => ()
                                    }
                                }
                            },
                            Rvalue::Cast(cast_kind, operand, ty) => {
                                // // println!("Cast found of kind {:?} with operand {:?} and type {:?}", cast_kind, operand, ty);
                                // match cast_kind {
                                //     CastKind::PtrToPtr => {
                                //         // println!("PtrToPtr cast found.");
                                //         // As per our decided scheme, there are only two cases in which a borrow will take place.
                                //         // When the source pointer and the target type mismatch, ie:
                                //         // 1. Source is a primitive reference, target is a raw pointer
                                //         // 2. Source is a raw pointer, target is a primitive reference

                                //         let mut source_is_ref = false;
                                //         let mut target_is_ref = false;

                                //         match operand {
                                //             Operand::Copy(Place {local, ..})
                                //             | Operand::Move(Place {local, ..}) => {
                                //                 let source_type = (*local_decls)[*local].ty;
                                //                 match source_type.kind() {
                                //                     ty::Ref(_, _, _) => {
                                //                         source_is_ref = true;
                                //                     },
                                //                     _ => (),
                                //                 }
                                //             },
                                //             _ => (),
                                //         }

                                //         match ty.kind() {
                                //             ty::Ref(_, _, _) => {
                                //                 target_is_ref = true;
                                //             },
                                //             _ => (),
                                //         }

                                //         if (source_is_ref && !target_is_ref) || (!source_is_ref && target_is_ref) {
                                //             insert_borrow(tcx, rapture_crate_number, &mut patch, bb, data, i,
                                //             &lhs_type.ref_mutability().unwrap_or(Mutability::Not), lhs_type, lhs);
                                //             _patch_empty = false;
                                //             break;
                                //         }
                                //         else {
                                //             println!("Casting ptr to ptr or ref to ref. No borrow here.");
                                //         }
                                //     },
                                //     _ => (),
                                // }
                            },
                            Rvalue::Ref(_region, borrow_kind, place) => {
                                // check if this is &*p where p is a raw pointer and of a sized type
                                if place.is_indirect_first_projection() &&
                                    (*local_decls)[place.local].ty.is_unsafe_ptr() &&
                                    lhs_type.peel_refs().is_sized(tcx, param_env){
                                    // println!("Ref {:?} = {:?}, lhs type peeled = {:?}", lhs_type, place, lhs_type.peel_refs());
                                    let mutability = match borrow_kind {
                                        BorrowKind::Mut { .. } => Mutability::Mut,
                                        _ => Mutability::Not
                                    };
                                    insert_borrow(tcx, rapture_crate_number, &mut patch, bb, data, i,
                                        &mutability, lhs_type, lhs);
                                    _patch_empty = false;
                                    break;
                                }
                            },
                            _ => (),
                        }
                    }
                    _ => (),
                }
            }
        }

        patch.apply(body);

        // Reorder basic blocks (routine copied from another Rust MIR pass)
        // let rpo: IndexVec<BasicBlock, BasicBlock> = body.basic_blocks.reverse_postorder().iter().copied().collect();
        // if !rpo.iter().is_sorted() {
        //     let mut updater = BasicBlockUpdater { map: rpo.invert_bijective_mapping(), tcx };
        //     debug_assert_eq!(updater.map[START_BLOCK], START_BLOCK);
        //     updater.visit_body(body);

        //     permute(body.basic_blocks.as_mut(), &updater.map);
        //     // Reorder ends
        // }

        // break;
        if _patch_empty {
            break;
        }
    }
}

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        // const EXCLUDED_CRATES : &'static [&'static str] = ["alloc", "core", "hashbrow"];

        // checking executable crate type as a hack to avoid dependent libraries
        // if sess.opts.capstone.is_some() {
            // println!("Crate name = {:?}", sess.opts.crate_name);
        // }

        sess.target.arch == "riscv64" &&
            // sess.opts.crate_name.as_ref() != Some(&"alloc".to_string()) &&
            // sess.opts.crate_name.as_ref() != Some(&"core".to_string()) &&
            sess.opts.crate_name.as_ref() != Some(&"hashbrown".to_string()) &&
            sess.opts.crate_name.as_ref() != Some(&"addr2line".to_string()) &&
            sess.opts.crate_name.as_ref() != Some(&"std".to_string()) &&
            sess.opts.crate_name.as_ref() != Some(&"gimli".to_string()) /* FIXME: just a hack */
        // match (sess.opts.capstone.as_ref(), sess.opts.crate_name.as_ref()) {
        //     (Some(c), Some(n)) => {
        //         c == "*" || c == n
        //     },
        //     (Some(c), None) => c == "*",
        //     _ => false
        // }
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // println!("\nStart of CAPSTONE-Injection pass for function: {}", tcx.def_path_str(body.source.def_id()));

        let local_decls_clone = body.local_decls.clone();

        // This is to dynamically locate the rapture crate and not hard-code its definition index

        let rapture_crate_number = tcx.crates(()).iter()
            .find(|x| tcx.crate_name(**x).as_str() == "core").cloned();

        first_pass(tcx, body, rapture_crate_number, &local_decls_clone);

        // println!("Successfully ran CAPSTONE-injection pass on function: {}", tcx.def_path_str(body.source.def_id()));
    }
}