use std::cmp::max;
use itertools::Itertools;
use std::collections::VecDeque;
use crate::MirPass;
use rustc_ast::Mutability;
// use rustc_ast::InlineAsmOptions;
// use rustc_ast::InlineAsmTemplatePiece;
// use rustc_index::Idx;
// use rustc_data_structures::fx::{FxIndexMap, IndexEntry, IndexOccupiedEntry};
// use rustc_index::bit_set::BitSet;
// use rustc_index::interval::SparseIntervalMatrix;
// use rustc_middle::mir::visit::MutVisitor;
use rustc_middle::mir::patch::MirPatch;
use crate::ty::Ty;
use crate::Spanned;
// use rustc_middle::mir::HasLocalDecls;
// use rustc_middle::mir::{dump_mir, PassWhere};
use rustc_middle::mir::{
    /*traversal,*/ BasicBlock, BasicBlockData, Body, BorrowKind, CallSource, CastKind, Const, ConstOperand, ConstValue, InlineAsmOperand, Local, LocalDecl, MutBorrowKind, Operand, Place, Rvalue, Statement, StatementKind, TerminatorKind, UnwindAction, UnwindTerminateReason, START_BLOCK
};
use rustc_middle::mir::interpret::Scalar;
// use crate::ty::ty_kind;
use rustc_middle::ty::{self, ScalarInt, TyCtxt};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
// use crate::ty::BorrowKind;
// use rustc_mir_dataflow::impls::MaybeLiveLocals;
// use rustc_mir_dataflow::points::{/*save_as_intervals,*/ DenseLocationMap, PointIndex};
// use rustc_mir_dataflow::Analysis;

use rustc_span::def_id::{DefId, DefIndex, CrateNum};
use rustc_middle::ty::{List, GenericArg};
use rustc_span::{DUMMY_SP, Symbol};
static SPANS: [rustc_span::Span; 1] = [DUMMY_SP];

pub struct InjectCapstone;

fn handle_operands(alloc_roots: &mut Vec<Local>, tracked_locals: &mut Vec<Local>, operand: &Operand<'_>, lhs: &Place<'_>) {
    match operand {
        &Operand::Copy(place) | &Operand::Move(place) => {
            if !tracked_locals.contains(&place.local){
                tracked_locals.push(place.local.clone());
            }
        },
        &Operand::Constant(_) => {
            if !alloc_roots.contains(&lhs.local) {
                alloc_roots.push(lhs.local.clone());
            }
        },
    }
}

fn record_operand_dereferences(alloc_roots: &Vec<Local>, root_references: &mut FxHashMap<Local, 
    FxHashMap<Local, (i32, Vec<(bool, usize)>)>>, operand: &Operand<'_>, lhs: &Place<'_>) {
    match operand {
        &Operand::Copy(place) | &Operand::Move(place) => {
            record_place_derefences(alloc_roots, root_references, &place, lhs, false);
        },
        _ => (),
    }
}

fn record_place_derefences(alloc_roots: &Vec<Local>, root_references: &mut FxHashMap<Local, 
    FxHashMap<Local, (i32, Vec<(bool, usize)>)>>, place: &Place<'_>, lhs: &Place<'_>, create_ref: bool) {
    let ref_offset = if create_ref {1} else {0};
    if alloc_roots.contains(&place.local) {
        if !root_references.contains_key(&place.local) {
            root_references.insert(place.local.clone(), FxHashMap::default());
        }
        let deref_depth: i32 = place.projection.len() as i32 - lhs.projection.len() as i32 - ref_offset;
        if !root_references[&place.local].contains_key(&lhs.local) {
            root_references.get_mut(&place.local).unwrap().insert(lhs.local.clone(), (deref_depth, vec![(create_ref, place as *const Place<'_> as usize)]));
        }
        else {
            let old_value = root_references[&place.local][&lhs.local].0;
            root_references.get_mut(&place.local).unwrap().get_mut(&lhs.local).unwrap().0 = max(old_value, deref_depth);
            root_references.get_mut(&place.local).unwrap().get_mut(&lhs.local).unwrap().1.push((create_ref, place as *const Place<'_> as usize));
        }
    }
    else {
        for root in alloc_roots.iter(){
            if root_references.contains_key(root) && root_references[root].contains_key(&place.local) {
                let deref_depth: i32 = place.projection.len() as i32 - lhs.projection.len() as i32 + root_references[root][&place.local].0 - ref_offset;
                if !root_references[root].contains_key(&lhs.local) {
                    root_references.get_mut(root).unwrap().insert(lhs.local.clone(), (deref_depth, vec![(create_ref, place as *const Place<'_> as usize)]));
                }
                else {
                    let old_value = root_references[root][&lhs.local].0;
                    root_references.get_mut(root).unwrap().get_mut(&lhs.local).unwrap().0 = max(old_value, deref_depth);
                    root_references.get_mut(root).unwrap().get_mut(&lhs.local).unwrap().1.push((create_ref, place as *const Place<'_> as usize));
                }
            }
        }
    }
}

fn check_operand_depth(alloc_roots: &Vec<Local>, root_references: &mut FxHashMap<Local, 
    FxHashMap<Local, (i32, Vec<(bool, usize)>)>>, operand: &Operand<'_>) -> Vec<Local> {
    match operand {
        &Operand::Copy(place) | &Operand::Move(place) => {
            check_place_depth(alloc_roots, root_references, &place)
        },
        _ => vec![],
    }  
}

fn check_place_depth(alloc_roots: &Vec<Local>, root_references: &mut FxHashMap<Local, 
    FxHashMap<Local, (i32, Vec<(bool, usize)>)>>, place: &Place<'_>) -> Vec<Local> {
    let mut roots_found: Vec<Local> = vec![];
    if alloc_roots.contains(&place.local) {
        roots_found.push((&place.local).clone());
    }
    for root in alloc_roots.iter(){
        if root_references.contains_key(root) && root_references[root].contains_key(&place.local) {
            let deref_depth: i32 = place.projection.len() as i32 + root_references[root][&place.local].0;
            if deref_depth >= 0 {
                roots_found.push(root.clone());
            }
        }
    }
    roots_found
}

fn call_from_ref<'tcx> (
    tcx: TyCtxt<'tcx>, 
    root: Local, 
    root_temps: FxHashMap<Local, Local>, 
    root_refs: FxHashMap<Local, Local>, 
    generics_list: &[rustc_middle::ty::GenericArg<'tcx>; 1], 
    from_ref_block: BasicBlock,
    is_cleanup: bool,
    rapture_crate_number: usize
) -> TerminatorKind<'tcx> {
    // Here we determine which function to target for the injection, using its crate number and definition index (which are statically fixed)
    let crate_num = CrateNum::new(rapture_crate_number);
    let def_index = DefIndex::from_usize(0);
    let mut _def_id = DefId { krate: crate_num, index: def_index };
    let mut _def_id_int = 0;
    let mut name = tcx.def_path_str(_def_id);
    
    while name != "MutDLTBoundedPointer::<T>::from_ref" {
        _def_id_int += 1;
        _def_id = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(_def_id_int) };
        name = tcx.def_path_str(_def_id);
    }
    if name != "MutDLTBoundedPointer::<T>::from_ref" {
        println!("%$%$%$%$% Corrupted RaptureCell definition: {}", name);
    }

    let generic_args: &rustc_middle::ty::List<GenericArg<'_>> = tcx.mk_args(generics_list); 

    // Creating the sugar of all the structures for the function type to be injected
    let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
    let const_ = Const::Val(ConstValue::ZeroSized, ty_);
    let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
    let operand_ = Operand::Constant(const_operand);
    let dest_place = Place {local: (root_temps[&root]).into(), projection: List::empty()};

    // This is how we create the arguments to be passed to the function that we are calling
    let operand_input = Operand::Copy(Place {local: (root_refs[&root]).into(), projection: List::empty()});
    let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

    let unwind_action: UnwindAction;
    if is_cleanup {
        unwind_action = UnwindAction::Terminate(UnwindTerminateReason::InCleanup);
    }
    else {
        unwind_action = UnwindAction::Continue;
    }
    // Create a block terminator that will execute the function call we want to inject
    let intermediary_terminator = TerminatorKind::Call {
        func: operand_,
        args: vec![spanned_operand],
        destination: dest_place,
        target: Some(from_ref_block),
        unwind: unwind_action,
        call_source: CallSource::Normal,
        fn_span: SPANS[0],
    };

    intermediary_terminator
}

fn call_size_of<'tcx> (
    tcx: TyCtxt<'tcx>, 
    local: Local, 
    local_sizes: FxHashMap<Local, Local>,
    generics_list: &[rustc_middle::ty::GenericArg<'tcx>; 2],
    size_of_block: BasicBlock,
    is_cleanup: bool
) -> TerminatorKind<'tcx> {
    // Here we determine which function to target for the injection, using its crate number and definition index (which are statically fixed)
    let size_calc_crate_num = CrateNum::new(2);                     // fixed, unless standard library changes
    let size_calc_def_index = DefIndex::from_usize(1726);           // fixed, unless standard library changes
    let size_calc_def_id = DefId { krate: size_calc_crate_num, index: size_calc_def_index };
    let size_calc_name = tcx.def_path_str(size_calc_def_id);
    if !size_calc_name.contains("mem::size_of") {
        println!("%$%$%$%$% Corrupted std::mem::size_of definition: {}", size_calc_name);
    }

    let size_calc_generic_args = tcx.mk_args(generics_list);

    let size_calc_ty_ = Ty::new(tcx, ty::FnDef(size_calc_def_id, size_calc_generic_args));
    let size_calc_const_ = Const::Val(ConstValue::ZeroSized, size_calc_ty_);
    let size_calc_const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: size_calc_const_ });
    let size_calc_operand_ = Operand::Constant(size_calc_const_operand);

    let size_calc_dest_place = Place {local: (local_sizes[&local]).into(), projection: List::empty()};

    let unwind_action: UnwindAction;
    if is_cleanup {
        unwind_action = UnwindAction::Terminate(UnwindTerminateReason::InCleanup);
    }
    else {
        unwind_action = UnwindAction::Continue;
    }

    let size_calc_terminator = TerminatorKind::Call {
        func: size_calc_operand_,
        args: vec![],
        destination: size_calc_dest_place,
        target: Some(size_of_block),
        unwind: unwind_action,
        call_source: CallSource::Normal,
        fn_span: SPANS[0],
    };

    size_calc_terminator
}

fn call_index_mut_bound<'tcx> (
    tcx: TyCtxt<'tcx>, 
    local: Local, 
    root: Local,
    root_temp_refs: FxHashMap<Local, Local>, 
    local_sizes: FxHashMap<Local, Local>, 
    generics_list: &[rustc_middle::ty::GenericArg<'tcx>; 2], 
    index: usize, 
    dest_local: Local, 
    deref_block: BasicBlock,
    is_cleanup: bool,
    rapture_crate_number: usize
) -> TerminatorKind<'tcx> {
    let crate_index = CrateNum::new(rapture_crate_number);
    let def_index = DefIndex::from_usize(0);
    let mut _def_id_int = 0;
    let mut _def_id = DefId { krate: crate_index, index: def_index };
    let mut name = tcx.def_path_str(_def_id);

    while name != "index_mut_bound" {
        _def_id_int += 1;
        _def_id = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(_def_id_int) };
        name = tcx.def_path_str(_def_id);
    }

    if tcx.def_path_str(_def_id) != "index_mut_bound" {
        println!("%$%$%$%$% Corrupted index_mut_bound definition index: {}", tcx.def_path_str(_def_id));
    }

    // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
    let generic_args: &rustc_middle::ty::List<GenericArg<'_>> = tcx.mk_args(generics_list); 

    // Creating the sugar of all the structures for the function type to be injected
    let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
    let const_ = Const::Val(ConstValue::ZeroSized, ty_);
    let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
    let operand_ = Operand::Constant(const_operand);
    let dest_place = Place {local: (dest_local).into(), projection: List::empty()};

    let operand_input1 = Operand::Move(Place {local: (root_temp_refs[&root]).into(), projection: List::empty()});
    let spanned_operand1 = Spanned { span: SPANS[0], node: operand_input1 };

    let operand_input2 = Operand::Constant(Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: Const::from_scalar(tcx, Scalar::Int(ScalarInt::from(index as u64)), Ty::new(tcx, ty::Uint(ty::UintTy::Usize))) }));
    let spanned_operand2 = Spanned { span: SPANS[0], node: operand_input2 };

    let operand_input3 = Operand::Move(Place {local: (local_sizes[&local]).into(), projection: List::empty()});
    let spanned_operand3 = Spanned { span: SPANS[0], node: operand_input3 };

    let unwind_action: UnwindAction;
    if is_cleanup {
        unwind_action = UnwindAction::Terminate(UnwindTerminateReason::InCleanup);
    }
    else {
        unwind_action = UnwindAction::Continue;
    }
    // Create a block terminator that will execute the function call we want to inject
    let deref_terminator = TerminatorKind::Call {
        func: operand_,
        args: vec![spanned_operand1, spanned_operand2, spanned_operand3],
        destination: dest_place,
        target: Some(deref_block),
        unwind: unwind_action,
        call_source: CallSource::Normal,
        fn_span: SPANS[0],
    };

    deref_terminator
}

fn call_invalidate<'tcx> (
    tcx: TyCtxt<'tcx>, 
    root: Local, 
    root_temp_refs: FxHashMap<Local, Local>,
    generics_list: &[rustc_middle::ty::GenericArg<'tcx>; 1], 
    dest_local: Local, 
    invalidate_block: BasicBlock,
    is_cleanup: bool,
    rapture_crate_number: usize
) -> TerminatorKind<'tcx> {
    // Here we determine which function to target for the injection, using its crate number and definition index (which are statically fixed)
    let crate_num = CrateNum::new(rapture_crate_number);
    let def_index = DefIndex::from_usize(0);
    let mut _def_id = DefId { krate: crate_num, index: def_index };
    let mut _def_id_int = 0;
    let mut name = tcx.def_path_str(_def_id);
    
    while name != "MutDLTBoundedPointer::<T>::invalidate" {
        _def_id_int += 1;
        _def_id = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(_def_id_int) };
        name = tcx.def_path_str(_def_id);
    }
    if name != "MutDLTBoundedPointer::<T>::invalidate" {
        println!("%$%$%$%$% Corrupted RaptureCell definition: {}", name);
    }

    let generic_args: &rustc_middle::ty::List<GenericArg<'_>> = tcx.mk_args(generics_list); 

    // Creating the sugar of all the structures for the function type to be injected
    let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
    let const_ = Const::Val(ConstValue::ZeroSized, ty_);
    let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
    let operand_ = Operand::Constant(const_operand);
    let dest_place = Place {local: (dest_local).into(), projection: List::empty()};

    // This is how we create the arguments to be passed to the function that we are calling
    let operand_input = Operand::Move(Place {local: (root_temp_refs[&root]).into(), projection: List::empty()});
    let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

    let unwind_action: UnwindAction;
    if is_cleanup {
        unwind_action = UnwindAction::Terminate(UnwindTerminateReason::InCleanup);
    }
    else {
        unwind_action = UnwindAction::Continue;
    }
    // Create a block terminator that will execute the function call we want to inject
    let intermediary_terminator = TerminatorKind::Call {
        func: operand_,
        args: vec![spanned_operand],
        destination: dest_place,
        target: Some(invalidate_block),
        unwind: unwind_action,
        call_source: CallSource::Normal,
        fn_span: SPANS[0],
    };

    intermediary_terminator
}

fn inject_deref<'tcx> (
    tcx: TyCtxt<'tcx>, 
    data: &mut BasicBlockData<'tcx>,
    stmt: &Statement<'tcx>,
    local: Local,
    _empty_tuple_temp: Local,
    i: usize,
    size_temp: usize,
    expected_terminator: &mut TerminatorKind<'tcx>, 
    patch: &mut MirPatch<'tcx>, 
    roots: &Vec<Local>, 
    new_temps_counter: &mut usize, 
    local_sizes:&mut FxHashMap<Local, Local>,
    root_temps: &FxHashMap<Local, Local>, 
    root_temp_refs: &FxHashMap<Local, Local>, 
    root_generics: &FxHashMap<Local, GenericArg<'tcx>>, 
    dlt_generics: &FxHashMap<Local, GenericArg<'tcx>>,
    rapture_crate_number: usize
) {
    // Shift all the statements beyond our target statement to a new vector and clear them from the original block
    let mut new_stmts = vec![];
    for (j, stmt) in data.statements.iter_mut().enumerate() {
        if j > i { 
            new_stmts.push(stmt.clone());
            stmt.make_nop();
        }
    }

    for (z, root) in roots.iter().enumerate() {
        // Creating a reference to the MutDLTBoundedPointer that would need to be passed into our target function
        let new_stmt = Statement {
            source_info: stmt.source_info,
            kind: StatementKind::Assign(Box::new((root_temp_refs[&root].into(), Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Mut { kind: MutBorrowKind::Default }, Place { local: root_temps[&root], projection: List::empty() })))),
        };

        // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
        let g_root = root_generics[&root];
        let ty_bool = ty::Const::from_bool(tcx, true);
        let g_bool = GenericArg::from(ty_bool);
        let generics_list_for_size = [g_root, g_bool];
        let deref_block: BasicBlock;

        if z == roots.len() - 1 {
            deref_block = patch.new_block(BasicBlockData {
                statements: new_stmts.clone(),
                terminator: Some(data.terminator.as_ref().unwrap().clone()),
                is_cleanup: data.is_cleanup.clone(),
            });
        }
        else {
            deref_block = patch.new_block(BasicBlockData {
                statements: vec![],
                terminator: Some(data.terminator.as_ref().unwrap().clone()),
                is_cleanup: data.is_cleanup.clone(),
            });
        }
        patch.patch_terminator(deref_block, expected_terminator.clone());

        let generics_list = [dlt_generics[&root], root_generics[&root]];
        
        *new_temps_counter += 1;
        local_sizes.insert(local, (size_temp + *new_temps_counter).into());
        let deref_terminator = call_index_mut_bound(tcx, local, *root, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block, data.is_cleanup.clone(), rapture_crate_number);
        let size_calc_block = patch.new_block(BasicBlockData {
            statements: vec![new_stmt],
            terminator: Some(data.terminator.as_ref().unwrap().clone()),
            is_cleanup: data.is_cleanup.clone(),
        });
        patch.patch_terminator(size_calc_block, deref_terminator);
        *expected_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block, data.is_cleanup.clone());
    }
}

fn variable_projection_index<V, T>(projection: ProjectionElem<V, T>) -> V {
    match projection {
        ProjectionElem::Index(local) => {
            local
        },
        _ => {println!("Constant index found in projection"); panic!()},
    }
}

fn constant_projection_index<V, T>(projection: ProjectionElem<V, T>) -> usize {
    match projection {
        ProjectionElem::Field(fieldindex, _ty) => usize::from(fieldindex),
        ProjectionElem::ConstantIndex {offset, min_length, from_end} => {
            if from_end {
                (min_length as usize - offset as usize).try_into().unwrap()
            }
            else {
                offset as usize
            }
        },
        ProjectionElem::Subslice {from, to, from_end} => {
            if from_end {
                (to - from).try_into().unwrap()
            }
            else {
                from.try_into().unwrap()
            }
        },
        ProjectionElem::Downcast(_symbol, variant_index) => usize::from(variant_index),
        ProjectionElem::Index(_) => {println!("Variable index found in projection"); 0},
        _ => 0,
    }
}

fn whether_projection_index_variable<V, T>(projection: ProjectionElem<V, T>) -> bool {
    match projection {
        ProjectionElem::Index(_) => true,
        _ => false,
    }
}

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        println!("\nStart of CAPSTONE-Injection pass for function: {}", tcx.def_path_str(body.source.def_id()));
        let mut patch = MirPatch::new(body);

        let mut rapture_crate_number: usize = 0;
        let mut crate_num_flag: bool = true;
        while crate_num_flag {
            rapture_crate_number += 1;
            crate_num_flag = Symbol::as_str(& tcx.crate_name(CrateNum::from_usize(rapture_crate_number))) != "rapture";
        }
        
        // First, upward, loop to find the last assignments to pointers
        let mut alloc_roots: Vec<Local> = vec![];
        let mut tracked_locals: Vec<Local> = vec![];
        for (_bb, data) in body.basic_blocks_mut().iter_enumerated_mut().rev() {
            for (_i, stmt) in data.statements.iter_mut().enumerate().rev() {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                        match rhs {
                            // Match the rvalue on the RHS based on what we want
                            // Once found, run backprop to locate the root of those assigned values (lhs)
                            // Add that assigned value and the root to the RootAllocations struct
                            Rvalue::Cast(cast_type, operand, ..) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                                match cast_type {     
                                    CastKind::PtrToPtr => {
                                        handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                    },
                                    _ => (),
                                }
                            },
                            Rvalue::Aggregate( .., operands) => {
                                if tracked_locals.contains(&lhs.local) {
                                    for operand in operands.iter(){
                                        handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                    }
                                }
                            },
                            Rvalue::BinaryOp(  .., boxed_operands) | Rvalue::CheckedBinaryOp( .., boxed_operands) => {
                                let (first, second) = *(boxed_operands.clone());
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &first, &lhs);
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &second, &lhs);
                                }
                            },
                            Rvalue::AddressOf(.., place) => {
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::CopyForDeref(place) => {
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::Discriminant(place) => {
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::Len(place) => {
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::Ref(.., place) => {
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::Repeat(operand, ..) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                            },
                            Rvalue::ShallowInitBox(operand, ..) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                            },
                            Rvalue::UnaryOp(.., operand) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                            },
                            Rvalue::Use(operand) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                            },
                            _ => (),
                        }
                    },
                    _ => (),
                }
            }
            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Call { destination, .. } => {
                            if tracked_locals.contains(&(destination.local)) && !alloc_roots.contains(&(destination.local)) {
                                alloc_roots.push(destination.local.clone());
                            }
                        },
                        TerminatorKind::Yield { resume_arg, .. } => {
                            if tracked_locals.contains(&(resume_arg.local)) && !alloc_roots.contains(&(resume_arg.local)) {
                                alloc_roots.push(resume_arg.local.clone());
                            }
                        },
                        TerminatorKind::InlineAsm { operands, .. } => {
                            for asm_operand in operands.iter(){
                                match asm_operand {
                                    &InlineAsmOperand::Out { place, .. } => {
                                        match place {
                                            Some(asm_place) => {
                                                if tracked_locals.contains(&asm_place.local) && !alloc_roots.contains(&asm_place.local) {
                                                    alloc_roots.push(asm_place.local.clone());
                                                }
                                            },
                                            _ => (),
                                        }
                                    },
                                    _ => (),
                                }
                            }
                        },
                        _ => (),
                    }
                },
                _ => (),
            }
        }

        println!("***********************found roots: {:?}", alloc_roots);
        println!("***********************tracked tmps: {:?}", tracked_locals);

        // Creating a fixed number of temporary variables of fixed type to be used by our injected functions
        let return_type_1 = Ty::new(tcx, ty::Bool);
        let _temp_1 = body.local_decls.push(LocalDecl::new(return_type_1, SPANS[0]));
        let return_type_2 = Ty::new(tcx, ty::Bool);
        let _temp_2 = body.local_decls.push(LocalDecl::new(return_type_2, SPANS[0]));
        let _empty_tuple = Ty::new(tcx, ty::Tuple(List::empty()));
        let _empty_tuple_temp = body.local_decls.push(LocalDecl::new(_empty_tuple, SPANS[0]));

        // Obtaining the ADT type for MutDLTBoundedPointer
        let mut def_id_int = 0;
        let mut def_id_adt = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(def_id_int) };
        let mut name = tcx.def_path_str(def_id_adt);
        while name != "MutDLTBoundedPointer" {
            def_id_int += 1;
            def_id_adt = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(def_id_int) };
            name = tcx.def_path_str(def_id_adt);
        }
        if name != "MutDLTBoundedPointer" {
            println!("%$%$%$%$% Corrupted RaptureCell definition: {}", name);
        }
        let adt_type = tcx.adt_def(def_id_adt);

        // Creating temporaries for each of the roots that we have found. These temporaries will be of type MutDLTBoundedPointer
        let mut root_temps: FxHashMap<Local, Local> = FxHashMap::default();
        let mut root_refs: FxHashMap<Local, Local> = FxHashMap::default();
        let mut root_generics: FxHashMap<Local, GenericArg<'tcx>> = FxHashMap::default();
        let mut dlt_generics: FxHashMap<Local, GenericArg<'tcx>> = FxHashMap::default();

        for root in alloc_roots.iter() {
            // We make a generic arg corresponding to the type of the root
            let root_ty = body.local_decls[*root].ty;
            let generic_arg = GenericArg::from(root_ty);
            let generic_args = tcx.mk_args(&[generic_arg]);
            root_generics.insert(*root, generic_arg);
            let root_adt_type = Ty::new(tcx, ty::Adt(adt_type, generic_args));
            let temp = body.local_decls.push(LocalDecl::new(root_adt_type, SPANS[0]));
            root_temps.insert(*root, temp);
            let dlt_generic = GenericArg::from(root_adt_type);
            dlt_generics.insert(*root, dlt_generic);
        }

        // Creating reference type temporaries for each root
        for root in alloc_roots.iter() {
            let root_ty = body.local_decls[*root].ty;
            let region = tcx.lifetimes.re_erased;
            let ref_ty = Ty::new(tcx, ty::Ref(region, root_ty, Mutability::Mut));
            let reftemp = body.local_decls.push(LocalDecl::new(ref_ty, SPANS[0]));
            root_refs.insert(*root, reftemp);
        }

        // Create temporaries that will hold the size of the root type
        let mut local_sizes: FxHashMap<Local, Local> = FxHashMap::default();
        
        // for root in alloc_roots.iter() {
        //     let size_ty = Ty::new(tcx, ty::Uint(ty::UintTy::Usize));
        //     size_temp = body.local_decls.push(LocalDecl::new(size_ty, SPANS[0]));
        //     local_sizes.insert(*root, size_temp);
        // }
        // for local in tracked_locals.iter() {
        //     if !local_sizes.contains_key(local) {
        //         let size_ty = Ty::new(tcx, ty::Uint(ty::UintTy::Usize));
        //         size_temp = body.local_decls.push(LocalDecl::new(size_ty, SPANS[0]));
        //         local_sizes.insert(*local, size_temp);
        //     }
        // };

        let mut new_temps_counter = 0;

        // References to the temps that are of MutDLTBoundedPointer type
        let mut root_temp_refs: FxHashMap<Local, Local> = FxHashMap::default();
        for root in alloc_roots.iter() {
            let root_ty = body.local_decls[root_temps[root]].ty;
            let region = tcx.lifetimes.re_erased;
            let ref_ty = Ty::new(tcx, ty::Ref(region, root_ty, Mutability::Mut));
            let reftemp = body.local_decls.push(LocalDecl::new(ref_ty, SPANS[0]));
            root_temp_refs.insert(*root, reftemp);
        }

        let mut root_references: FxHashMap<Local, FxHashMap<Local, (i32, Vec<(bool, usize)>)>> = FxHashMap::default();

        // let root_references_retrieve = &mut root_references as 
        // *mut FxHashMap<Local, FxHashMap<Local, (i32, Vec<(bool, usize)>)>> as *mut FxHashMap<Local, FxHashMap<Local, (i32, Vec<(bool, *const Place<'tcx>)>)>>;

        let size_temp = body.local_decls.len() - 1;

        for (_bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (_i, stmt) in data.statements.iter_mut().enumerate() {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                        match rhs {
                            Rvalue::Cast( .., operand, _ty) => {
                                record_operand_dereferences(&alloc_roots, &mut root_references, &operand, &lhs);
                            },
                            Rvalue::Aggregate( .., operands) => {
                                for operand in operands.iter(){
                                    record_operand_dereferences(&alloc_roots, &mut root_references, &operand, &lhs);
                                }
                            },
                            Rvalue::BinaryOp(  .., boxed_operands) | Rvalue::CheckedBinaryOp( .., boxed_operands) => {
                                let (first, second) = *(boxed_operands.clone());
                                record_operand_dereferences(&alloc_roots, &mut root_references, &first, &lhs);
                                record_operand_dereferences(&alloc_roots, &mut root_references, &second, &lhs);
                            },
                            Rvalue::AddressOf(.., place) | Rvalue::Ref(.., place) => {
                                record_place_derefences(&alloc_roots, &mut root_references, &place, &lhs, true);
                            },
                            Rvalue::CopyForDeref(place) | Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                                record_place_derefences(&alloc_roots, &mut root_references, &place, &lhs, false);
                            },
                            Rvalue::Repeat(operand, ..) | Rvalue::ShallowInitBox(operand, ..) | Rvalue::UnaryOp(.., operand) | Rvalue::Use(operand) => {
                                record_operand_dereferences(&alloc_roots, &mut root_references, &operand, &lhs);
                            },
                            _ => (),
                        }
                    },
                    _ => (),
                }
            }
        }
        
        // unsafe {println!("map of deref depths: {:?}", *root_references_retrieve);}

        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            let mut expected_terminator = data.terminator.as_ref().unwrap().kind.clone();
            for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                        let mut roots: Vec<Local>;
                        if {roots = check_place_depth(&alloc_roots, &mut root_references, &lhs); roots.len() > 0} {
                            let local = lhs.local.clone();

                            inject_deref(tcx, data, &stmt, local, _empty_tuple_temp, i, size_temp, &mut expected_terminator, &mut patch, &roots, 
                                &mut new_temps_counter, &mut local_sizes, &root_temps, &root_temp_refs, &root_generics, &dlt_generics, rapture_crate_number);
                        }
                        match rhs {
                            Rvalue::Cast( .., operand, _ty) => {
                                if {roots = check_operand_depth(&alloc_roots, &mut root_references, &operand); roots.len() > 0} {
                                    match operand {
                                        &Operand::Copy(place) | &Operand::Move(place) => {
                                            let local = place.local.clone();
                                            
                                            inject_deref(tcx, data, &stmt, local, _empty_tuple_temp, i, size_temp, &mut expected_terminator, &mut patch, &roots, 
                                                &mut new_temps_counter, &mut local_sizes, &root_temps, &root_temp_refs, &root_generics, &dlt_generics, rapture_crate_number);
                                        },
                                        _ => (),
                                    }
                                }
                            },
                            Rvalue::Aggregate( .., operands) => {
                                for operand in operands.iter(){
                                    if {roots = check_operand_depth(&alloc_roots, &mut root_references, &operand); roots.len() > 0} {
                                        match operand {
                                            &Operand::Copy(place) | &Operand::Move(place) => {
                                                let local = place.local.clone();
                                                
                                                inject_deref(tcx, data, &stmt, local, _empty_tuple_temp, i, size_temp, &mut expected_terminator, &mut patch, &roots, 
                                                    &mut new_temps_counter, &mut local_sizes, &root_temps, &root_temp_refs, &root_generics, &dlt_generics, rapture_crate_number);
                                            },
                                            _ => (),
                                        }
                                    }
                                }
                            },
                            Rvalue::BinaryOp(  .., boxed_operands) | Rvalue::CheckedBinaryOp( .., boxed_operands) => {
                                let (first, second) = *(boxed_operands.clone());
                                if {roots = check_operand_depth(&alloc_roots, &mut root_references, &first); roots.len() > 0} {
                                    match first {
                                        Operand::Copy(place) | Operand::Move(place) => {
                                            let local = place.local.clone();
                                            
                                            inject_deref(tcx, data, &stmt, local, _empty_tuple_temp, i, size_temp, &mut expected_terminator, &mut patch, &roots, 
                                                &mut new_temps_counter, &mut local_sizes, &root_temps, &root_temp_refs, &root_generics, &dlt_generics, rapture_crate_number);
                                        },
                                        _ => (),
                                    }
                                }
                                if {roots = check_operand_depth(&alloc_roots, &mut root_references, &second); roots.len() > 0} {
                                    match second {
                                        Operand::Copy(place) | Operand::Move(place) => {
                                            let local = place.local.clone();
                                            
                                            inject_deref(tcx, data, &stmt, local, _empty_tuple_temp, i, size_temp, &mut expected_terminator, &mut patch, &roots, 
                                                &mut new_temps_counter, &mut local_sizes, &root_temps, &root_temp_refs, &root_generics, &dlt_generics, rapture_crate_number);
                                        },
                                        _ => (),
                                    }
                                }
                            },
                            Rvalue::AddressOf(.., place) | Rvalue::Ref(.., place) | Rvalue::CopyForDeref(place) | 
                            Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                                if {roots = check_place_depth(&alloc_roots, &mut root_references, &place); roots.len() > 0} {
                                    let local = place.local.clone();
                                    
                                    inject_deref(tcx, data, &stmt, local, _empty_tuple_temp, i, size_temp, &mut expected_terminator, &mut patch, &roots, 
                                        &mut new_temps_counter, &mut local_sizes, &root_temps, &root_temp_refs, &root_generics, &dlt_generics, rapture_crate_number);
                                }
                            },
                            Rvalue::Repeat(operand, ..) | Rvalue::ShallowInitBox(operand, ..) | Rvalue::UnaryOp(.., operand) | Rvalue::Use(operand) => {
                                if {roots = check_operand_depth(&alloc_roots, &mut root_references, &operand); roots.len() > 0} {
                                    match operand {
                                        &Operand::Copy(place) | &Operand::Move(place) => {
                                            let local = place.local.clone();
                                            
                                            inject_deref(tcx, data, &stmt, local, _empty_tuple_temp, i, size_temp, &mut expected_terminator, &mut patch, &roots, 
                                                &mut new_temps_counter, &mut local_sizes, &root_temps, &root_temp_refs, &root_generics, &dlt_generics, rapture_crate_number);
                                        },
                                        _ => (),
                                    }
                                }
                            },
                            _ => (),
                        }
                    },
                    _ => (),
                }
            }
            patch.patch_terminator(bb, expected_terminator);
        }

        // Add the new temporaries to the local_decls
        for _i in 0..new_temps_counter {
            let size_ty = Ty::new(tcx, ty::Uint(ty::UintTy::Usize));
            body.local_decls.push(LocalDecl::new(size_ty, SPANS[0]));
        }

        patch.apply(body);

        patch = MirPatch::new(body);

        // Second, downward, loop to find the first uses of those pointers as well as track their borrows and later uses such as dereferences
        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
                match stmt {
                    Statement {kind: StatementKind::Assign(box (lhs, _rhs)), .. } => {
                        match lhs {
                            Place { local, .. } => {
                            // Check if the local is in the root_allocations set
                                if alloc_roots.contains(local) {
                                    // Make the RaptureCell function call for generating the capability
                                    // Store the capability into the local temporary that we have created for this root
                                    // Store a mapping of this allocation and its capability (or its address) 

                                    let new_stmt = Statement {
                                        source_info: stmt.source_info,
                                        kind: StatementKind::Assign(Box::new((root_refs[local].into(), Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Mut { kind: MutBorrowKind::Default }, Place { local: *local, projection: List::empty() })))),
                                    };

                                    // Shift all the statements beyond our target statement to a new vector and clear them from the original block
                                    let mut new_stmts = vec![];
                                    for (j, stmt) in data.statements.iter_mut().enumerate() {
                                        if j > i { 
                                            new_stmts.push(stmt.clone());
                                            stmt.make_nop();
                                        }
                                    }

                                    data.statements.push(new_stmt);

                                    // Create an intermediary block that will be inserted between the current block and the next block
                                    let from_ref_block;

                                    // This block has to point to the next block in the control flow graph (that terminator is an Option type)
                                    match data.terminator.as_ref() {
                                        Some(_x) => {
                                            from_ref_block = patch.new_block(BasicBlockData {
                                                statements: new_stmts.clone(),
                                                terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                is_cleanup: data.is_cleanup.clone(),
                                            });
                                        },
                                        _ => {
                                            from_ref_block = patch.new_block(BasicBlockData {
                                                statements: new_stmts.clone(),
                                                terminator: None,
                                                is_cleanup: data.is_cleanup.clone(),
                                            });
                                        }
                                    }

                                    let g_root = root_generics[&local];
                                    let generics_list = [g_root];
                                    println!("****lhs {:?}, temp: {:?}", &local, &root_temps[&local]);

                                    let from_ref_terminator = call_from_ref(tcx, *local, root_temps.clone(), root_refs.clone(), &generics_list, from_ref_block, data.is_cleanup.clone(), rapture_crate_number);

                                    patch.patch_terminator(bb, from_ref_terminator);
                                }
                            }
                        }
                    },
                    _ => (),
                }
            }
            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Call { func, args, destination, target, unwind, call_source, fn_span} => {
                            if alloc_roots.contains(&(destination.local)) {
                                let local = destination.local;

                                let new_stmt = Statement {
                                    source_info: data.terminator.as_ref().unwrap().source_info,
                                    kind: StatementKind::Assign(Box::new((root_refs[&local].into(), Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Mut { kind: MutBorrowKind::Default }, Place { local: local, projection: List::empty() })))),
                                };

                                // Create an intermediary block that will be inserted between the current block and the next block
                                let from_ref_block;

                                // This block has to point to the next block in the control flow graph (that terminator is an Option type)
                                match &data.terminator {
                                    Some(_x) => {
                                        from_ref_block = patch.new_block(BasicBlockData {
                                            statements: vec![new_stmt],
                                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                            is_cleanup: data.is_cleanup.clone(),
                                        });
                                    },
                                    _ => {
                                        from_ref_block = patch.new_block(BasicBlockData {
                                            statements: vec![new_stmt],
                                            terminator: None,
                                            is_cleanup: data.is_cleanup.clone(),
                                        });
                                    }
                                }

                                let new_terminator = TerminatorKind::Call {
                                    func: func.clone(),
                                    args: args.clone(),
                                    destination: destination.clone(),
                                    target: Some(from_ref_block),
                                    unwind: unwind.clone(),
                                    call_source: call_source.clone(),
                                    fn_span: fn_span.clone(),
                                };

                                let g_root = root_generics[&local];
                                let generics_list = [g_root];

                                let from_ref_terminator = call_from_ref(tcx, local, root_temps.clone(), root_refs.clone(), &generics_list, target.unwrap(), data.is_cleanup.clone(), rapture_crate_number);

                                println!("****lhs {:?}, temp: {:?}", &local, &root_temps[&local]);
                                // The current basic block's terminator is now replaced with the one we just created (which shifts the control flow to the intermediary block)
                                patch.patch_terminator(bb, new_terminator);
                                patch.patch_terminator(from_ref_block, from_ref_terminator);
                            }
                        },
                        _ => (),
                    }
                },
                _ => (),
            }
        }

        patch.apply(body);
        patch = MirPatch::new(body);

        // Traverse the basic blocks in DFS order by following the targets of the terminators
        
        let mut active_root_refs: Vec<Local> = vec![];
        let mut active_root_refs_per_bb: FxHashMap<BasicBlock, Vec<Local>> = FxHashMap::default();

        let mut visited_blocks = FxHashSet::default();
        let mut parent_map: FxHashMap<usize, BasicBlock> = FxHashMap::default();
        let mut stack = VecDeque::new();

        // Start with the first basic block
        stack.push_front(START_BLOCK);

        let mut previous_bb = START_BLOCK;

        while !stack.is_empty() {
            let bb = stack.pop_front().unwrap();
            let data = &body.basic_blocks[bb];

            visited_blocks.insert(bb);

            if bb != START_BLOCK {
                match &body.basic_blocks[previous_bb].terminator {
                    Some(y) => {
                        if !y.successors().contains(&bb) {
                            active_root_refs = active_root_refs_per_bb[&parent_map[&(bb.index())]].clone();
                        }
                    },
                    _ => (),
                }
            }

            match &data.terminator {
                Some(x) => {
                    for target in x.successors() {
                        parent_map.insert(target.index(), bb);
                        if !visited_blocks.contains(&target) && !stack.contains(&target) {
                            stack.push_front(target); 
                        }
                    }

                    match &x.kind {
                        TerminatorKind::Call {func, destination, ..} => {
                            match func {
                                Operand::Constant(c) => {
                                    match c.const_ {
                                        Const::Val(_constval, ty) => {
                                            match ty.kind() {
                                                ty::FnDef(_def_id, _) => {
                                                    if tcx.def_path_str(_def_id) == "MutDLTBoundedPointer::<T>::from_ref" {
                                                        if !active_root_refs.contains(&destination.local) {
                                                            active_root_refs.push(destination.local.clone());
                                                        }
                                                    }
                                                },
                                                _ => (),
                                            }
                                        },
                                        _ => (),
                                    }
                                },
                                _ => (),
                            };
                        },
                        _ => (),
                    }
                    active_root_refs_per_bb.insert(bb, active_root_refs.clone());
                },
                _ => (),
            }
            previous_bb = bb;
        }

        let mut last_block_in_scope: Vec<BasicBlock> = vec![];
        let mut return_points: Vec<BasicBlock> = vec![];

        let mut scope_children: FxHashMap<usize, Vec<usize>> = FxHashMap::default();

        for i in 0..body.source_scopes.len() {
            last_block_in_scope.push(START_BLOCK);
            scope_children.insert(i, vec![]);

            let scope = &body.source_scopes[i.into()];
            let parent = scope.parent_scope;
            match parent {
                Some(p) => {
                    scope_children.get_mut(&p.index()).unwrap().push(i);
                },
                None => (),
            }
        }

        for (bb, data) in body.basic_blocks.iter().enumerate() {
            match &data.terminator {
                Some(x) => {
                    let mut successor_count = 0;
                    for target in x.successors() {
                        successor_count += 1;

                        if x.source_info.scope.index() > (body.basic_blocks[target].terminator).clone().unwrap().source_info.scope.index() {
                            // for all scopes in the parent chain from current scope to the target scope, we update the last block in scope
                            let mut current_scope = x.source_info.scope;
                            while current_scope.index() > (body.basic_blocks[target].terminator).clone().unwrap().source_info.scope.index() {
                                last_block_in_scope[current_scope.index()] = bb.into();
                                match body.source_scopes[current_scope].parent_scope {
                                    Some(parent) => {
                                        current_scope = parent;
                                    },
                                    None => break,
                                }
                            }
                        }
                        
                        if x.source_info.scope.index() < (body.basic_blocks[target].terminator).clone().unwrap().source_info.scope.index() {
                            // we check if the target scope is not in the subtree of the children scopes of the current scope, we update the last block in scope
                            let mut potentially_child_scope = (body.basic_blocks[target].terminator).clone().unwrap().source_info.scope;
                            while potentially_child_scope.index() > x.source_info.scope.index() {
                                if body.source_scopes[potentially_child_scope].parent_scope.unwrap().index() == x.source_info.scope.index() {
                                    break;
                                }
                                match body.source_scopes[potentially_child_scope].parent_scope {
                                    Some(parent) => {
                                        potentially_child_scope = parent;
                                    },
                                    None => break,
                                }
                            }
                            match body.source_scopes[potentially_child_scope].parent_scope {
                                Some(parent) => {
                                    if parent.index() == x.source_info.scope.index() {
                                        last_block_in_scope[x.source_info.scope.index()] = bb.into();
                                    }
                                },
                                None => {},
                            }
                        }
                    }
                    
                    if successor_count == 0 {
                        last_block_in_scope[x.source_info.scope.index()] = bb.into();
                    }
                    match &x.kind {
                        // Return points for the given function
                        TerminatorKind::Return | TerminatorKind::UnwindTerminate(_) | TerminatorKind::UnwindResume | TerminatorKind::CoroutineDrop => {
                            last_block_in_scope[x.source_info.scope.index()] = bb.into();
                            return_points.push(bb.into());
                        },

                        TerminatorKind::Drop {unwind, ..} | TerminatorKind::Call {unwind, ..} | TerminatorKind::Assert {unwind, ..} | TerminatorKind::FalseUnwind {unwind, ..} | TerminatorKind::InlineAsm {unwind, ..} => {
                            // Target block of the unwind, we treat it as a successor
                            match unwind {
                                UnwindAction::Cleanup(unwind_target) => {
                                    if x.source_info.scope.index() > (body.basic_blocks[*unwind_target].terminator).clone().unwrap().source_info.scope.index() {
                                        // for all scopes in the parent chain from current scope to the target scope, update the last block in scope
                                        let mut current_scope = x.source_info.scope;
                                        while current_scope.index() > (body.basic_blocks[*unwind_target].terminator).clone().unwrap().source_info.scope.index() {
                                            last_block_in_scope[current_scope.index()] = bb.into();
                                            match body.source_scopes[current_scope].parent_scope {
                                                Some(parent) => {
                                                    current_scope = parent;
                                                },
                                                None => break,
                                            }
                                        }
                                    }
                                    
                                    if x.source_info.scope.index() < (body.basic_blocks[*unwind_target].terminator).clone().unwrap().source_info.scope.index() {
                                        // check if the target scope is not in the subtree of the children scopes of the current scope, update the last block in scope
                                        let mut potentially_child_scope = (body.basic_blocks[*unwind_target].terminator).clone().unwrap().source_info.scope;
                                        while potentially_child_scope.index() > x.source_info.scope.index() {
                                            if body.source_scopes[potentially_child_scope].parent_scope.unwrap().index() == x.source_info.scope.index() {
                                                break;
                                            }
                                            match body.source_scopes[potentially_child_scope].parent_scope {
                                                Some(parent) => {
                                                    potentially_child_scope = parent;
                                                },
                                                None => break,
                                            }
                                        }
                                        match body.source_scopes[potentially_child_scope].parent_scope {
                                            Some(parent) => {
                                                if parent.index() == x.source_info.scope.index() {
                                                    last_block_in_scope[x.source_info.scope.index()] = bb.into();
                                                }
                                            },
                                            None => {},
                                        }
                                    }
                                },
                                _ => {},
                            }
                        },
                        _ => {},
                    }
                },
                _ => (),
            }
        }

        // We now create new restricted sets that track "last active"ness
        // For this we do a DFS on the scopes tree

        let mut visited_scopes = FxHashSet::default();
        let mut stack = VecDeque::new();
        stack.push_front(0);

        let mut last_active_root_refs_per_scope: FxHashMap<usize, Vec<Local>> = FxHashMap::default();

        while !stack.is_empty() {
            let scope = stack.pop_front().unwrap();
            let children = &scope_children[&scope];
            visited_scopes.insert(scope);

            for child in children.iter() {
                if !visited_scopes.contains(&child) {
                    stack.push_front(*child);
                }
            }

            match body.source_scopes[scope.into()].parent_scope {
                Some(parent) => {
                    let mut last_active: Vec<Local> = active_root_refs_per_bb[&last_block_in_scope[scope]].clone();
                    let parent_active = active_root_refs_per_bb[&last_block_in_scope[parent.index()]].clone();
                    for root in parent_active {
                        if last_active.contains(&root) {
                            last_active.remove(last_active.iter().position(|x| *x == root).unwrap());
                        }
                    }
                    last_active_root_refs_per_scope.insert(scope, last_active.clone());
                },
                None => {
                    let last_active: Vec<Local> = active_root_refs_per_bb[&last_block_in_scope[scope]].clone();
                    last_active_root_refs_per_scope.insert(scope, last_active.clone());
                }
            }
        }
        
        // Form a set of the blocks that require a drop
        let mut drop_blocks: FxHashSet<BasicBlock> = FxHashSet::default();
        for return_point in return_points.iter() {
            drop_blocks.insert(*return_point);
        }
        for scope in 0..body.source_scopes.len() {
            if last_active_root_refs_per_scope[(&scope).into()].len() > 0 {
                drop_blocks.insert(last_block_in_scope[scope]);
            }
        }

        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            if drop_blocks.contains(&bb) {
                let roots_to_drop = {
                    if return_points.contains(&bb) {
                        active_root_refs_per_bb[&bb].clone()
                    } else {
                        let scope: usize = {
                            let mut scope = 0;
                            for (key, value) in last_block_in_scope.iter().enumerate() {
                                if *value == bb {
                                    scope = key as usize;
                                    break;
                                }
                            }
                            scope
                        };
                        last_active_root_refs_per_scope[&(scope)].clone()
                    }
                };
                let mut expected_terminator = data.terminator.as_ref().unwrap().kind.clone();
                for root_temp in roots_to_drop.iter() {
                    println!("******* Performing drop for root with reftemp: {:?}", root_temp);
                    // The following code injects drop and invalidate for some root allocation local. Right now they are unreachable in the CFG and only go to themselvers.
                    // The target location block is to be decided given the search for termination blocks.
                    let mut root = root_temp.clone();
                    for root_local in alloc_roots.iter() {
                        if root_temps[root_local] == *root_temp {
                            root = root_local.clone();
                            break;
                        }
                    }

                    let new_stmt = Statement {
                        source_info: data.terminator.as_ref().unwrap().source_info,
                        kind: StatementKind::Assign(Box::new((root_temp_refs[&root].into(), Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Mut { kind: MutBorrowKind::Default }, Place { local: root_temps[&root], projection: List::empty() })))),
                    };
                    
                    let invalidate_block = patch.new_block(BasicBlockData {
                        statements: vec![],
                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                        is_cleanup: data.is_cleanup.clone(),
                    });

                    let g_root = root_generics[&root];
                    let generics_list = [g_root];
                    let invalidate_terminator = call_invalidate(tcx, root, root_temp_refs.clone(), &generics_list, _empty_tuple_temp, invalidate_block, data.is_cleanup.clone(), rapture_crate_number);
                    
                    let drop_place = Place {local: (root_temps[&root]).into(), projection: List::empty()};
                    
                    let drop_block = patch.new_block(BasicBlockData {
                        statements: vec![],
                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                        is_cleanup: data.is_cleanup.clone(),
                    });

                    let unwind_action: UnwindAction;
                    if data.is_cleanup {
                        unwind_action = UnwindAction::Terminate(UnwindTerminateReason::InCleanup);
                    }
                    else {
                        unwind_action = UnwindAction::Continue;
                    }

                    let drop_terminator = TerminatorKind::Drop {
                        place: drop_place,
                        target: drop_block, // TODO: placeholder
                        unwind: unwind_action,
                        replace: false,
                    };

                    patch.patch_terminator(invalidate_block, drop_terminator);
                    patch.patch_terminator(drop_block, expected_terminator.clone());
                    expected_terminator = invalidate_terminator.clone();
                    data.statements.push(new_stmt);
                }
                patch.patch_terminator(bb, expected_terminator);
            }
        }   

        // For reference, we can print the contents of each basic block in the body of this function. Not required at this point.
        
        patch.apply(body);
        println!("Successfully ran CAPSTONE-injection pass on function: {}", tcx.def_path_str(body.source.def_id()));
    }
}