#![allow(unused)]

use interpret::Scalar;
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
pub struct InjectCapsLock;

fn get_func_def_id<'ctx>(tcx: TyCtxt<'ctx>, crate_num_opt: Option<CrateNum>, func_name: &str) -> Option<DefId> {
    match crate_num_opt {
        Some (crate_num) => {
            // Dynamically locate the function we want to inject, instead of hardcoding its definition index
            let def_index = DefIndex::from_usize(0);
            let mut _def_id = DefId { krate: crate_num, index: def_index };
            let mut _def_id_int = 0;
            let mut name = tcx.def_path_str(_def_id);

            // Check whether the thing being borrowed was mutable. This changes the nature of the function we are injecting.
            // Future note: I am unsure if two different functions based on this is even required.  should definitely have the two functions, for manual injection needs it.
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

fn get_pointee_type<'ctx>(ty : Ty<'ctx>) -> Option<Ty<'ctx>> {
    match ty.kind() {
        ty::RawPtr(TypeAndMut {ty : inner_ty, ..}) => Some(*inner_ty),
        ty::Ref(_, inner_ty, _) => Some(*inner_ty),
        _ => None
    }
}

fn insert_call<'ctx>(tcx: TyCtxt<'ctx>, func: DefId, generic_args: &[GenericArg<'ctx>], args: Vec<Spanned<Operand<'ctx>>>,
        patch: &mut MirPatch<'ctx>, bb: BasicBlock, data: &mut BasicBlockData<'ctx>, i: usize,
        lhs: &Place<'ctx>) {
    // Shift all the statements beyond our target statement to a new vector and clear them from the original block
    let new_stmts = data.statements.split_off(i + 1);
    let unwind_action = UnwindAction::Terminate(UnwindTerminateReason::Abi);

    // Create an intermediary block that will be inserted between the current block and the next block
    // This block has to point to the next block in the control flow graph (that terminator is an Option type)
    let block = patch.new_block(BasicBlockData {
        statements: new_stmts.clone(),
        terminator: Some(data.terminator.as_ref().unwrap().clone()),
        is_cleanup: data.is_cleanup.clone(),
    });

    let def_id = func;

    let generic_args = tcx.mk_args(generic_args);

    // Creating the sugar of all the structures for the function type to be injected
    let ty_ = Ty::new(tcx, ty::FnDef(def_id, generic_args));
    let const_ = Const::Val(ConstValue::ZeroSized, ty_);
    let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
    let operand_ = Operand::Constant(const_operand);

    let dest_place = Place {local: (lhs.local).into(), projection: List::empty()};  // Every function has to have a target place where it will store its return value

    // Create a block terminator that will execute the function call we want to inject. This terminator points from current block to our intermediary block
    let intermediary_terminator = TerminatorKind::Call {
        func: operand_,
        args: args,
        destination: dest_place,
        target: Some(block),
        unwind: unwind_action,
        call_source: CallSource::Normal,
        fn_span: SPANS[0],
    };

    patch.patch_terminator(bb, intermediary_terminator);
}


fn get_borrow_func_name(m: &Mutability, is_ref: bool, is_local: bool) -> &'static str {
    if is_local {
        match (*m, is_ref) {
            (Mutability::Mut, false) => "capslock::borrow_mut",
            (Mutability::Not, false) => "capslock::borrow",
            (Mutability::Mut, true) => "capslock::borrow_mut_ref",
            (Mutability::Not, true) => "capslock::borrow_ref",
        }
    } else {
        match (*m, is_ref) {
            (Mutability::Mut, false) => "capslock::borrow_mut",
            (Mutability::Not, false) => "capslock::borrow",
            (Mutability::Mut, true) => "capslock::borrow_mut_ref",
            (Mutability::Not, true) => "capslock::borrow_ref",
        }
    }
}

fn insert_borrow<'ctx>(tcx: TyCtxt<'ctx>, capslock_crate_number : Option<CrateNum>,
        patch: &mut MirPatch<'ctx>, bb: BasicBlock, data: &mut BasicBlockData<'ctx>, i: usize,
        mutability: &Mutability, lhs_type: Ty<'ctx>, lhs: &Place<'ctx>, is_unsafe_cell : bool,
        is_foreign : bool) {
    eprintln!("Insert borrow (UnsafeCell = {}, Foreign = {}): {:?}", is_unsafe_cell, is_foreign, lhs_type);

    let pointer_type : u8 = match lhs_type.kind() {
        crate::ty::RawPtr(tm) => {
            if is_unsafe_cell {
                2 // unafe cell
            } else {
                1 // plain raw pointer
            }
        }
        _ => 0 // reference
    };

    let func = get_func_def_id(tcx, capslock_crate_number,
        get_borrow_func_name(mutability, lhs_type.is_ref(), capslock_crate_number.is_none())
    ).expect("Unable to find function.");

    let root_ty = get_pointee_type(lhs_type).unwrap();
    // The generic argument that goes inside the <> brackets of the function call. This is why we obtained the root type
    let generic_arg = GenericArg::from(root_ty);

    // This is how we create the arguments to be passed to the function that we are calling
    let operand_input = Operand::Copy(Place {local: lhs.local, projection: List::empty()});
    let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

    let operand_pointer_type = Operand::const_from_scalar(tcx, Ty::new(tcx, ty::Uint(ty::UintTy::U8)), Scalar::from_u8(pointer_type), SPANS[0]);
    let spanned_operand_pointer_type = Spanned { span: SPANS[0], node: operand_pointer_type };

    let operand_is_foreign = Operand::const_from_scalar(tcx, Ty::new(tcx, ty::Bool), Scalar::from_bool(is_foreign), SPANS[0]);
    let spanned_operand_is_foreign = Spanned { span: SPANS[0], node: operand_is_foreign };
    let args = vec![spanned_operand, spanned_operand_pointer_type, spanned_operand_is_foreign];

    insert_call(tcx, func, &[generic_arg], args, patch, bb, data, i, lhs)
}

fn get_shrink_func_name(m: &Mutability, is_ref: bool, is_local: bool) -> &'static str {
    if is_local {
        match (*m, is_ref) {
            (Mutability::Mut, false) => "capslock::shrink_mut",
            (Mutability::Not, false) => "capslock::shrink",
            (Mutability::Mut, true) => "capslock::shrink_mut_ref",
            (Mutability::Not, true) => "capslock::shrink_ref",
        }
    } else {
        match (*m, is_ref) {
            (Mutability::Mut, false) => "capslock::shrink_mut",
            (Mutability::Not, false) => "capslock::shrink",
            (Mutability::Mut, true) => "capslock::shrink_mut_ref",
            (Mutability::Not, true) => "capslock::shrink_ref",
        }
    }
}


fn insert_shrink<'ctx>(tcx: TyCtxt<'ctx>, capslock_crate_number : Option<CrateNum>,
        patch: &mut MirPatch<'ctx>, bb: BasicBlock, data: &mut BasicBlockData<'ctx>, i: usize,
        mutability: &Mutability, lhs_type: Ty<'ctx>, lhs: &Place<'ctx>,
        is_foreign : bool) {

    let func = get_func_def_id(tcx, capslock_crate_number,
        get_shrink_func_name(mutability, lhs_type.is_ref(), capslock_crate_number.is_none())
    ).expect("Unable to find function.");

    let root_ty = get_pointee_type(lhs_type).unwrap();
    // The generic argument that goes inside the <> brackets of the function call. This is why we obtained the root type
    let generic_arg = GenericArg::from(root_ty);

    // This is how we create the arguments to be passed to the function that we are calling
    let operand_input = Operand::Copy(Place {local: lhs.local, projection: List::empty()});
    let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

    let operand_is_foreign = Operand::const_from_scalar(tcx, Ty::new(tcx, ty::Bool), Scalar::from_bool(is_foreign), SPANS[0]);
    let spanned_operand_is_foreign = Spanned { span: SPANS[0], node: operand_is_foreign };
    let args = vec![spanned_operand, spanned_operand_is_foreign];

    insert_call(tcx, func, &[generic_arg], args, patch, bb, data, i, lhs)
}


fn first_pass<'ctx>(tcx: TyCtxt<'ctx>, body: &mut Body<'ctx>,
        capslock_crate_number : Option<CrateNum>, local_decls : &IndexVec<Local, LocalDecl<'ctx>>) {
    let func_path_str = tcx.def_path_str(body.source.def_id());
    if func_path_str.contains("capslock") || func_path_str.contains("mem::uninitialized") {
        // we don't do this to capslock itself
        return;
    }
    let param_env = tcx.param_env(body.source.def_id());
    loop {
        let mut patch = MirPatch::new(body);
        let mut _patch_empty = true;


        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (i, stmt) in data.statements.clone().iter().enumerate().rev().skip(1) {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                        let lhs_type = (*local_decls)[lhs.local].ty;

                        match rhs {
                            Rvalue::AddressOf(mutability, place) => {
                                    let r_ty = (*local_decls)[place.local].ty;
                                    match lhs_type.kind() {
                                        crate::ty::RawPtr(tm) => {
                                                let is_unsafe_cell = get_pointee_type(r_ty)
                                                    .is_some_and(|ty: Ty<'_>| ty.ty_adt_def().is_some_and(|adt| adt.is_unsafe_cell())) ;
                                                let is_foreign = get_pointee_type(lhs_type)
                                                    .is_some_and(|ty| matches!(ty.kind(), &ty::Foreign(_)));
                                                insert_borrow(tcx, capslock_crate_number, &mut patch, bb, data,
                                                    i, mutability, lhs_type, lhs, is_unsafe_cell, is_foreign); // treat all raw pointers as UnsafeCell
                                                _patch_empty = false;
                                                break;
                                            // }
                                        },
                                        _ => ()
                                    }
                            },
                            Rvalue::Ref(_region, borrow_kind, place) => {
                                // check if this is &*p where p is a raw pointer and of a sized type
                                let is_borrow = place.is_indirect_first_projection() &&
                                    (*local_decls)[place.local].ty.is_unsafe_ptr();

                                // println!("Ref {:?} = {:?}, lhs type peeled = {:?}", lhs_type, place, lhs_type.peel_refs());
                                let is_foreign = get_pointee_type(lhs_type)
                                    .is_some_and(|ty| matches!(ty.kind(), &ty::Foreign(_)));
                                let mutability = match borrow_kind {
                                    BorrowKind::Mut { .. } => Mutability::Mut,
                                    _ => Mutability::Not
                                };
                                if is_borrow {
                                    insert_borrow(tcx, capslock_crate_number, &mut patch, bb, data, i,
                                        &mutability, lhs_type, lhs, false, is_foreign);
                                    _patch_empty = false;
                                    break;
                                } else if !place.projection.is_empty() && place.projection.iter().find(
                                    // check if it is projected to a sub-region
                                    |proj|
                                        match proj {
                                            &ProjectionElem::Field(_, _) |
                                            &ProjectionElem::Index(_) |
                                            &ProjectionElem::Subslice { .. } |
                                            &ProjectionElem::ConstantIndex { .. } =>
                                                true,
                                            _ => false
                                        }
                                    ).is_some()
                                {
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
        if _patch_empty {
            break;
        }
    }
}

impl<'tcx> MirPass<'tcx> for InjectCapsLock {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.target.arch == "riscv64" &&
        sess.opts.crate_name.as_ref() != Some(&"hashbrown".to_string()) &&
        sess.opts.crate_name.as_ref() != Some(&"addr2line".to_string()) &&
        sess.opts.crate_name.as_ref() != Some(&"gimli".to_string())
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let local_decls_clone = body.local_decls.clone();

        // This is to dynamically locate the capslock crate and not hard-code its definition index
        let capslock_crate_number = tcx.crates(()).iter()
            .find(|x| tcx.crate_name(**x).as_str() == "core").cloned();

        first_pass(tcx, body, capslock_crate_number, &local_decls_clone);
    }
}