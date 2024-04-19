use std::cmp::max;
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
    /*traversal,*/ Body, LocalDecl, Local, InlineAsmOperand, /*LocalKind, Location,*/ BasicBlockData, Place, UnwindAction, CallSource, CastKind, Rvalue, 
    Statement, StatementKind, TerminatorKind, Operand, Const, ConstValue, ConstOperand, BorrowKind, MutBorrowKind, BasicBlock
};
use rustc_middle::mir::interpret::Scalar;
// use crate::ty::ty_kind;
use rustc_middle::ty::{self, ScalarInt, TyCtxt};
use rustc_data_structures::fx::FxHashMap;
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
    let mut roots_found = vec![];
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
    from_ref_block: BasicBlock
) -> TerminatorKind<'tcx> {
    // Here we determine which function to target for the injection, using its crate number and definition index (which are statically fixed)
    let crate_num = CrateNum::new(20);
    let def_index = DefIndex::from_usize(0);
    let mut _def_id = DefId { krate: crate_num, index: def_index };
    let mut _def_id_int = 0;
    let mut name = tcx.def_path_str(_def_id);
    
    while name != "MutDLTBoundedPointer::<T>::from_ref" {
        _def_id_int += 1;
        _def_id = DefId { krate: CrateNum::new(20), index: DefIndex::from_usize(_def_id_int) };
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

    // Create a block terminator that will execute the function call we want to inject
    let intermediary_terminator = TerminatorKind::Call {
        func: operand_,
        args: vec![spanned_operand],
        destination: dest_place,
        target: Some(from_ref_block),
        unwind: UnwindAction::Continue,
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
    size_of_block: BasicBlock
) -> TerminatorKind<'tcx> {
    // Here we determine which function to target for the injection, using its crate number and definition index (which are statically fixed)
    let size_calc_crate_num = CrateNum::new(2);
    let size_calc_def_index = DefIndex::from_usize(1726);
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

    let size_calc_terminator = TerminatorKind::Call {
        func: size_calc_operand_,
        args: vec![],
        destination: size_calc_dest_place,
        target: Some(size_of_block),
        unwind: UnwindAction::Continue,
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
    deref_block: BasicBlock
) -> TerminatorKind<'tcx> {
    let crate_index = CrateNum::new(20);
    let def_index = DefIndex::from_usize(0);
    let mut _def_id_int = 0;
    let mut _def_id = DefId { krate: crate_index, index: def_index };
    let mut name = tcx.def_path_str(_def_id);

    while name != "index_mut_bound" {
        _def_id_int += 1;
        _def_id = DefId { krate: CrateNum::new(20), index: DefIndex::from_usize(_def_id_int) };
        name = tcx.def_path_str(_def_id);
    }

    if tcx.def_path_str(_def_id) != "index_mut_bound" {
        println!("%$%$%$%$% Corrupted index_mut_bound definition index: {}", tcx.def_path_str(_def_id));
    }

    // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
    let generic_args: &rustc_middle::ty::List<GenericArg<'_>> = tcx.mk_args(generics_list); 
    println!("!! generic_args: {:?}", generic_args);

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

    // Create a block terminator that will execute the function call we want to inject
    let deref_terminator = TerminatorKind::Call {
        func: operand_,
        args: vec![spanned_operand1, spanned_operand2, spanned_operand3],
        destination: dest_place,
        target: Some(deref_block),
        unwind: UnwindAction::Continue,
        call_source: CallSource::Normal,
        fn_span: SPANS[0],
    };

    deref_terminator
}

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut patch = MirPatch::new(body);

        let mut rapture_crate_number: u32 = 0;
        let mut crate_num_flag: bool = true;
        while crate_num_flag {
            rapture_crate_number += 1;
            crate_num_flag = Symbol::as_str(& tcx.crate_name(CrateNum::from_u32(rapture_crate_number))) != "rapture";
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
                            Rvalue::Cast(cast_type, operand, ty) => {
                                println!("Cast Operands : {:?} , and types: {:?}", operand, ty);
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                                match cast_type {                                    
                                    CastKind::PointerExposeAddress => {
                                        println!("PointerExposeAddress: ");
                                    },
                                    CastKind::PointerFromExposedAddress => {
                                        println!("PointerFromExposedAddress: ");
                                    },
                                    CastKind::PointerCoercion(_coercion) => {
                                        println!("PointerCoercion: ");
                                    },
                                    CastKind::PtrToPtr => {
                                        match operand {
                                            Operand::Copy(place) => {
                                                println!("PtrToPtr Operands on Copy: {:?} , and types: {:?}", place, ty);
                                            },
                                            Operand::Move(place) => {
                                                println!("PtrToPtr Operands on Move: {:?} , and types: {:?}", place, ty);
                                            },
                                            Operand::Constant(boxed_constant) => {
                                                println!("PtrToPtr Operands on Constant: {:?} , and types: {:?}", boxed_constant, ty);
                                            },
                                        }
                                        handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                    },
                                    CastKind::FnPtrToPtr => {
                                        println!("FnPtrToPtr: {:?}", operand);
                                    },
                                    CastKind::Transmute => {
                                        println!("Transmute: {:?}", operand);
                                    },
                                    _ => (),
                                }
                            },
                            Rvalue::Aggregate( .., operands) => {
                                println!("Aggregate Operands : {:?}", operands);
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
                                match first {
                                    Operand::Copy(place) => {
                                        print!("BinaryOp Operands on Copy: {:?} , ", place);
                                    },
                                    Operand::Move(place) => {
                                        print!("BinaryOp Operands on Move: {:?} , ", place);
                                    },
                                    Operand::Constant(boxed_constant) => {
                                        print!("BinaryOp Operands on Constant: {:?} , ", boxed_constant);
                                    },
                                }
                                match second {
                                    Operand::Copy(place) => {
                                        println!(" Copy: {:?}", place);
                                    },
                                    Operand::Move(place) => {
                                        println!(" Move: {:?}", place);
                                    },
                                    Operand::Constant(boxed_constant) => {
                                        println!(" Constant: {:?}", boxed_constant);
                                    },
                                }
                            },
                            Rvalue::AddressOf(.., place) => {
                                println!("AddressOf Operand (Place): {:?}, local of place: {:?}, projection list: {:?}", place, place.local, place.projection);
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::CopyForDeref(place) => {
                                println!("CopyForDeref Operand (Place): {:?}", place);
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::Discriminant(place) => {
                                println!("Discriminant Operand (Place): {:?}", place);
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::Len(place) => {
                                println!("Len Operand (Place): {:?}", place);
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::Ref(.., place) => {
                                println!("Ref Operand (Place): {:?}", place);
                                if tracked_locals.contains(&lhs.local) && !tracked_locals.contains(&place.local){
                                    tracked_locals.push(place.local.clone());
                                }
                            },
                            Rvalue::Repeat(operand, ..) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                                match operand {
                                    Operand::Copy(place) => {
                                        println!("Repeat Operand on Copy: {:?}", place);
                                    },
                                    Operand::Move(place) => {
                                        println!("Repeat Operand on Move: {:?}", place);
                                    },
                                    Operand::Constant(boxed_constant) => {
                                        println!("Repeat Operand on Constant: {:?}", boxed_constant);
                                    },
                                }
                            },
                            Rvalue::ShallowInitBox(operand, ty) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                                match operand {
                                    Operand::Copy(place) => {
                                        println!("ShallowInitBox Operands on Copy: {:?} , and types: {:?}", place, ty);
                                    },
                                    Operand::Move(place) => {
                                        println!("ShallowInitBox Operands on Move: {:?} , and types: {:?}", place, ty);
                                    },
                                    Operand::Constant(boxed_constant) => {
                                        println!("ShallowInitBox Operands on Constant: {:?} , and types: {:?}", boxed_constant, ty);
                                    },
                                }
                            },
                            Rvalue::UnaryOp(.., operand) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                                match operand {
                                    Operand::Copy(place) => {
                                        println!("UnaryOp Operand on Copy: {:?}", place);
                                    },
                                    Operand::Move(place) => {
                                        println!("UnaryOp Operand on Move: {:?}", place);
                                    },
                                    Operand::Constant(boxed_constant) => {
                                        println!("UnaryOp Operand on Constant: {:?}", boxed_constant);
                                    },
                                }
                            },
                            Rvalue::Use(operand) => {
                                if tracked_locals.contains(&lhs.local) {
                                    handle_operands(&mut alloc_roots, &mut tracked_locals, &operand, &lhs);
                                }
                                match operand {
                                    Operand::Copy(place) => {
                                        println!("Use Operand on Copy: {:?}", place);
                                    },
                                    Operand::Move(place) => {
                                        println!("Use Operand on Move: {:?}", place);
                                    },
                                    Operand::Constant(boxed_constant) => {
                                        println!("Use Operand on Constant: {:?}", boxed_constant);
                                    },
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
        let mut def_id_adt = DefId { krate: CrateNum::new(20), index: DefIndex::from_usize(def_id_int) };
        let mut name = tcx.def_path_str(def_id_adt);
        while name != "MutDLTBoundedPointer" {
            def_id_int += 1;
            def_id_adt = DefId { krate: CrateNum::new(20), index: DefIndex::from_usize(def_id_int) };
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

        // Create a set of locals that hold the Local for each root allocation from alloc_roots
        let _root_allocations: FxHashMap<Local, Local> = alloc_roots.iter().map(|x| (*x, *x)).collect();

        // Create temporaries that will hold the size of the root type
        let mut local_sizes: FxHashMap<Local, Local> = FxHashMap::default();
        for root in alloc_roots.iter() {
            let size_ty = Ty::new(tcx, ty::Uint(ty::UintTy::Usize));
            let size_temp = body.local_decls.push(LocalDecl::new(size_ty, SPANS[0]));
            local_sizes.insert(*root, size_temp);
        }
        for local in tracked_locals.iter() {
            if !alloc_roots.contains(local) {
                let size_ty = Ty::new(tcx, ty::Uint(ty::UintTy::Usize));
                let size_temp = body.local_decls.push(LocalDecl::new(size_ty, SPANS[0]));
                local_sizes.insert(*local, size_temp);
            }
        }

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

        let root_references_retrieve = &mut root_references as 
        *mut FxHashMap<Local, FxHashMap<Local, (i32, Vec<(bool, usize)>)>> as *mut FxHashMap<Local, FxHashMap<Local, (i32, Vec<(bool, *const Place<'tcx>)>)>>;

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
        
        unsafe {println!("map of deref depths: {:?}", *root_references_retrieve);}

        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            println!("Basic block: {:?}", bb);
            let mut expected_terminator = data.terminator.as_ref().unwrap().kind.clone();
            let mut deref_block: BasicBlock;
            for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
                println!("Statement: {:?}", stmt);
                println!("expected terminator: {:?}", expected_terminator);
                match stmt {
                    Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                        let mut roots: Vec<Local>;
                        if {roots = check_place_depth(&alloc_roots, &mut root_references, &lhs); roots.len() > 0} {
                            println!("Requires LHS deref: {:?}", &lhs);
                            let local = lhs.local.clone();

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

                                let size_calc_block = patch.new_block(BasicBlockData {
                                    statements: vec![new_stmt],
                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                    is_cleanup: false,
                                });

                                // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                let g_root = root_generics[&root];
                                let ty_bool = ty::Const::from_bool(tcx, true);
                                let g_bool = GenericArg::from(ty_bool);
                                let generics_list_for_size = [g_root, g_bool];

                                let size_calc_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block);

                                println!("Patching prevbb inside LHS");
                                // patch.patch_terminator(bb, size_calc_terminator);

                                if z == roots.len() - 1 {
                                    deref_block = patch.new_block(BasicBlockData {
                                        statements: new_stmts.clone(),
                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                        is_cleanup: false,
                                    });
                                }
                                else {
                                    deref_block = patch.new_block(BasicBlockData {
                                        statements: vec![],
                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                        is_cleanup: false,
                                    });
                                }

                                let generics_list = [dlt_generics[&root], root_generics[&root]];
                                let deref_terminator = call_index_mut_bound(tcx, local, *root, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block);
                                
                                println!("Patching sizecalcblock inside LHS");
                                patch.patch_terminator(size_calc_block, deref_terminator);
                                patch.patch_terminator(deref_block, expected_terminator.clone());
                                println!("Done patching sizecalcblock inside LHS");

                                expected_terminator = size_calc_terminator.clone();
                            }
                        }
                        println!("right hand side: {:?}", &rhs);
                        println!("terminator before rhs: {:?}", expected_terminator);
                        match rhs {
                            Rvalue::Cast( .., operand, _ty) => {
                                if {roots = check_operand_depth(&alloc_roots, &mut root_references, &operand); roots.len() > 0} {
                                    println!("Requires Cast deref: {:?}", &operand);
                                    match operand {
                                        &Operand::Copy(place) | &Operand::Move(place) => {
                                            let local = place.local.clone();
                                            
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

                                                // Insert a new function call to std::mem::size_of for the root type
                                                let size_calc_block = patch.new_block(BasicBlockData {
                                                    statements: vec![new_stmt],
                                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                    is_cleanup: false,
                                                });
                
                                                // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                                let g_root = root_generics[&root];
                                                let ty_bool = ty::Const::from_bool(tcx, true);
                                                let g_bool = GenericArg::from(ty_bool);
                                                let generics_list_for_size = [g_root, g_bool];
                
                                                let size_calc_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block);
                
                                                println!("Patching prevbb inside LHS");
                                                // patch.patch_terminator(bb, size_calc_terminator);
                
                                                if z == roots.len() - 1 {
                                                    deref_block = patch.new_block(BasicBlockData {
                                                        statements: new_stmts.clone(),
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                                                }
                                                else {
                                                    deref_block = patch.new_block(BasicBlockData {
                                                        statements: vec![],
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                                                }
                
                                                let generics_list = [dlt_generics[&root], root_generics[&root]];
                                                let deref_terminator = call_index_mut_bound(tcx, local, *root, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block);
                                                
                                                println!("Patching sizecalcblock inside LHS");
                                                patch.patch_terminator(size_calc_block, deref_terminator);
                                                patch.patch_terminator(deref_block, expected_terminator.clone());
                                                println!("Done patching sizecalcblock inside LHS");
                
                                                expected_terminator = size_calc_terminator.clone();
                                            }
                                        },
                                        _ => (),
                                    }
                                }
                            },
                            Rvalue::Aggregate( .., operands) => {
                                for operand in operands.iter(){
                                    if {roots = check_operand_depth(&alloc_roots, &mut root_references, &operand); roots.len() > 0} {
                                        println!("Requires Aggregate deref: {:?}", &operand);
                                        match operand {
                                            &Operand::Copy(place) | &Operand::Move(place) => {
                                                let local = place.local.clone();
                                                
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
    
                                                    // Insert a new function call to std::mem::size_of for the root type
                                                    let size_calc_block = patch.new_block(BasicBlockData {
                                                        statements: vec![new_stmt],
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                    
                                                    // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                                    let g_root = root_generics[&root];
                                                    let ty_bool = ty::Const::from_bool(tcx, true);
                                                    let g_bool = GenericArg::from(ty_bool);
                                                    let generics_list_for_size = [g_root, g_bool];
                    
                                                    let size_calc_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block);
                    
                                                    println!("Patching prevbb inside LHS");
                                                    // patch.patch_terminator(bb, size_calc_terminator);
                    
                                                    if z == roots.len() - 1 {
                                                        deref_block = patch.new_block(BasicBlockData {
                                                            statements: new_stmts.clone(),
                                                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                            is_cleanup: false,
                                                        });
                                                    }
                                                    else {
                                                        deref_block = patch.new_block(BasicBlockData {
                                                            statements: vec![],
                                                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                            is_cleanup: false,
                                                        });
                                                    }
                    
                                                    let generics_list = [dlt_generics[&root], root_generics[&root]];
                                                    let deref_terminator = call_index_mut_bound(tcx, local, *root, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block);
                                                    
                                                    println!("Patching sizecalcblock inside LHS");
                                                    patch.patch_terminator(size_calc_block, deref_terminator);
                                                    patch.patch_terminator(deref_block, expected_terminator.clone());
                                                    println!("Done patching sizecalcblock inside LHS");
                    
                                                    expected_terminator = size_calc_terminator.clone();
                                                }
                                            },
                                            _ => (),
                                        }
                                    }
                                }
                            },
                            Rvalue::BinaryOp(  .., boxed_operands) | Rvalue::CheckedBinaryOp( .., boxed_operands) => {
                                let (first, second) = *(boxed_operands.clone());
                                if {roots = check_operand_depth(&alloc_roots, &mut root_references, &first); roots.len() > 0} {
                                    println!("Requires BinOp first deref: {:?}", &first);
                                    match first {
                                        Operand::Copy(place) | Operand::Move(place) => {
                                            let local = place.local.clone();
                                            
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

                                                // Insert a new function call to std::mem::size_of for the root type
                                                let size_calc_block = patch.new_block(BasicBlockData {
                                                    statements: vec![new_stmt],
                                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                    is_cleanup: false,
                                                });
                
                                                // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                                let g_root = root_generics[&root];
                                                let ty_bool = ty::Const::from_bool(tcx, true);
                                                let g_bool = GenericArg::from(ty_bool);
                                                let generics_list_for_size = [g_root, g_bool];
                
                                                let size_calc_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block);
                
                                                println!("Patching prevbb inside LHS");
                                                // patch.patch_terminator(bb, size_calc_terminator);
                
                                                if z == roots.len() - 1 {
                                                    deref_block = patch.new_block(BasicBlockData {
                                                        statements: new_stmts.clone(),
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                                                }
                                                else {
                                                    deref_block = patch.new_block(BasicBlockData {
                                                        statements: vec![],
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                                                }
                
                                                let generics_list = [dlt_generics[&root], root_generics[&root]];
                                                let deref_terminator = call_index_mut_bound(tcx, local, *root, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block);
                                                
                                                println!("Patching sizecalcblock inside LHS");
                                                patch.patch_terminator(size_calc_block, deref_terminator);
                                                patch.patch_terminator(deref_block, expected_terminator.clone());
                                                println!("Done patching sizecalcblock inside LHS");
                
                                                expected_terminator = size_calc_terminator.clone();
                                            }
                                        },
                                        _ => (),
                                    }
                                }
                                if {roots = check_operand_depth(&alloc_roots, &mut root_references, &second); roots.len() > 0} {
                                    println!("Requires Binop second deref: {:?}", &second);
                                    match second {
                                        Operand::Copy(place) | Operand::Move(place) => {
                                            let local = place.local.clone();
                                            
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

                                                // Insert a new function call to std::mem::size_of for the root type
                                                let size_calc_block = patch.new_block(BasicBlockData {
                                                    statements: vec![new_stmt],
                                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                    is_cleanup: false,
                                                });
                
                                                // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                                let g_root = root_generics[&root];
                                                let ty_bool = ty::Const::from_bool(tcx, true);
                                                let g_bool = GenericArg::from(ty_bool);
                                                let generics_list_for_size = [g_root, g_bool];
                
                                                let size_calc_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block);
                
                                                println!("Patching prevbb inside LHS");
                                                // patch.patch_terminator(bb, size_calc_terminator);
                
                                                if z == roots.len() - 1 {
                                                    deref_block = patch.new_block(BasicBlockData {
                                                        statements: new_stmts.clone(),
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                                                }
                                                else {
                                                    deref_block = patch.new_block(BasicBlockData {
                                                        statements: vec![],
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                                                }
                
                                                let generics_list = [dlt_generics[&root], root_generics[&root]];
                                                let deref_terminator = call_index_mut_bound(tcx, local, *root, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block);
                                                
                                                println!("Patching sizecalcblock inside LHS");
                                                patch.patch_terminator(size_calc_block, deref_terminator);
                                                patch.patch_terminator(deref_block, expected_terminator.clone());
                                                println!("Done patching sizecalcblock inside LHS");
                
                                                expected_terminator = size_calc_terminator.clone();
                                            }
                                        },
                                        _ => (),
                                    }
                                }
                            },
                            Rvalue::AddressOf(.., place) | Rvalue::Ref(.., place) | Rvalue::CopyForDeref(place) | 
                            Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                                if {roots = check_place_depth(&alloc_roots, &mut root_references, &place); roots.len() > 0} {
                                    println!("Requires Place deref: {:?}", &place);
                                    let local = place.local.clone();
                                    
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

                                        // Insert a new function call to std::mem::size_of for the root type
                                        let size_calc_block = patch.new_block(BasicBlockData {
                                            statements: vec![new_stmt],
                                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                            is_cleanup: false,
                                        });
        
                                        // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                        let g_root = root_generics[&root];
                                        let ty_bool = ty::Const::from_bool(tcx, true);
                                        let g_bool = GenericArg::from(ty_bool);
                                        let generics_list_for_size = [g_root, g_bool];
        
                                        let size_calc_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block);
        
                                        println!("Patching prevbb inside LHS");
                                        // patch.patch_terminator(bb, size_calc_terminator);
        
                                        if z == roots.len() - 1 {
                                            deref_block = patch.new_block(BasicBlockData {
                                                statements: new_stmts.clone(),
                                                terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                is_cleanup: false,
                                            });
                                        }
                                        else {
                                            deref_block = patch.new_block(BasicBlockData {
                                                statements: vec![],
                                                terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                is_cleanup: false,
                                            });
                                        }
        
                                        let generics_list = [dlt_generics[&root], root_generics[&root]];
                                        let deref_terminator = call_index_mut_bound(tcx, local, *root, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block);
                                        
                                        println!("Patching sizecalcblock inside LHS");
                                        patch.patch_terminator(size_calc_block, deref_terminator);
                                        patch.patch_terminator(deref_block, expected_terminator.clone());
                                        println!("Done patching sizecalcblock inside LHS");
        
                                        expected_terminator = size_calc_terminator.clone();
                                    }
                                }
                            },
                            Rvalue::Repeat(operand, ..) | Rvalue::ShallowInitBox(operand, ..) | Rvalue::UnaryOp(.., operand) | Rvalue::Use(operand) => {
                                if {roots = check_operand_depth(&alloc_roots, &mut root_references, &operand); roots.len() > 0} {
                                    println!("Requires Operand deref: {:?}", &operand);
                                    match operand {
                                        &Operand::Copy(place) | &Operand::Move(place) => {
                                            let local = place.local.clone();
                                            
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

                                                // Insert a new function call to std::mem::size_of for the root type
                                                let size_calc_block = patch.new_block(BasicBlockData {
                                                    statements: vec![new_stmt],
                                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                    is_cleanup: false,
                                                });
                
                                                // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                                let g_root = root_generics[&root];
                                                let ty_bool = ty::Const::from_bool(tcx, true);
                                                let g_bool = GenericArg::from(ty_bool);
                                                let generics_list_for_size = [g_root, g_bool];
                
                                                let size_calc_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block);
                
                                                println!("Patching prevbb inside LHS");
                                                // patch.patch_terminator(bb, size_calc_terminator);
                
                                                if z == roots.len() - 1 {
                                                    deref_block = patch.new_block(BasicBlockData {
                                                        statements: new_stmts.clone(),
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                                                }
                                                else {
                                                    deref_block = patch.new_block(BasicBlockData {
                                                        statements: vec![],
                                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                        is_cleanup: false,
                                                    });
                                                }
                
                                                let generics_list = [dlt_generics[&root], root_generics[&root]];
                                                let deref_terminator = call_index_mut_bound(tcx, local, *root, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block);
                                                
                                                println!("Patching sizecalcblock inside LHS");
                                                patch.patch_terminator(size_calc_block, deref_terminator);
                                                patch.patch_terminator(deref_block, expected_terminator.clone());
                                                println!("Done patching sizecalcblock inside LHS");
                
                                                expected_terminator = size_calc_terminator.clone();
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
            patch.patch_terminator(bb, expected_terminator);
        }

        // Second, downward, loop to find the first uses of those pointers as well as track their borrows and later uses such as dereferences
        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
                match stmt {
                    Statement {kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
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
                                    match &data.terminator {
                                        Some(_x) => {
                                            from_ref_block = patch.new_block(BasicBlockData {
                                                statements: vec![],
                                                terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                is_cleanup: false,
                                            });
                                        },
                                        _ => {
                                            from_ref_block = patch.new_block(BasicBlockData {
                                                statements: vec![],
                                                terminator: None,
                                                is_cleanup: false,
                                            });
                                        }
                                    }

                                    let g_root = root_generics[&local];
                                    let generics_list = [g_root];

                                    let from_ref_terminator = call_from_ref(tcx, *local, root_temps.clone(), root_refs.clone(), &generics_list, from_ref_block);

                                    // Insert a new function call to std::mem::size_of for the root type
                                    let size_calc_block = patch.new_block(BasicBlockData {
                                        statements: new_stmts,
                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                        is_cleanup: false,
                                    });

                                    // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                    
                                    let ty_bool = ty::Const::from_bool(tcx, true);
                                    let g_bool = GenericArg::from(ty_bool);
                                    let generics_list_for_size = [g_root, g_bool];

                                    let size_calc_terminator = call_size_of(tcx, *local, local_sizes.clone(), &generics_list_for_size, size_calc_block);

                                    // The current basic block's terminator is now replaced with the one we just created (which shifts the control flow to the intermediary block)
                                    patch.patch_terminator(bb, from_ref_terminator);
                                    patch.patch_terminator(from_ref_block, size_calc_terminator);
                                }
                            }
                        }

                        match rhs {
                            Rvalue::Use(operand) => {
                                match operand {
                                    Operand::Copy(place) => {
                                        if alloc_roots.contains(&place.local) {
                                            println!("Use Operand on Copy: {:?}", place)
                                        }
                                    },
                                    Operand::Move(place) => {
                                        if alloc_roots.contains(&place.local) {
                                            println!("Use Operand on Move: {:?}", place)
                                        }
                                    },
                                    Operand::Constant(boxed_constant) => {
                                        // Check if the value of the boxed constant is scalar 69, which is our marker (this is voodoo magic for now and must be formalised later)
                                        let constant = boxed_constant.const_;
                                        match constant {
                                            Const::Val(val, _ty) => {
                                                match val {
                                                    ConstValue::Scalar(scalar) => {
                                                        match scalar {
                                                            Scalar::Int(int) => {
                                                                match int.try_to_u32() {
                                                                    Ok(x) => {
                                                                        if x == 69 { 
                                                                            println!("# Marker found!");
                                                                            /*
                                                                            
                                                                            let local = (1 as usize).into();

                                                                            // Creating a reference to the MutDLTBoundedPointer that would need to be passed into our target function
                                                                            let new_stmt = Statement {
                                                                                source_info: stmt.source_info,
                                                                                kind: StatementKind::Assign(Box::new((root_temp_refs[&local].into(), Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Mut { kind: MutBorrowKind::Default }, Place { local: root_temps[&local], projection: List::empty() })))),
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

                                                                            let deref_block = patch.new_block(BasicBlockData {
                                                                                statements: vec![],
                                                                                terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                                                is_cleanup: false,
                                                                            });

                                                                            let generics_list = [dlt_generics[&local], root_generics[&local]];
                                                                            let deref_terminator = call_index_mut_bound(tcx, local, root_temp_refs.clone(), local_sizes.clone(), &generics_list, 0, _empty_tuple_temp, deref_block);
                                                                            patch.patch_terminator(bb, deref_terminator);
                                                                            */
                                                                        }
                                                                    },
                                                                    _ => (),
                                                                }
                                                            },
                                                            _ => (),
                                                        }
                                                    },
                                                    _ => (),
                                                }
                                            },
                                            _ => (),
                                        }
                                    },
                                }
                            }
                            _ => (),
                        }
                    },
                    _ => (),
                }
            }
            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Call { func: _, args: _, destination, .. } => {
                            if alloc_roots.contains(&(destination.local)) {
                                let local = destination.local;
                                println!("local: {:?}", local);

                                let new_stmt = Statement {
                                    source_info: data.terminator.as_ref().unwrap().source_info,
                                    kind: StatementKind::Assign(Box::new((root_refs[&local].into(), Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Mut { kind: MutBorrowKind::Default }, Place { local: local, projection: List::empty() })))),
                                };

                                data.statements.push(new_stmt);

                                // Create an intermediary block that will be inserted between the current block and the next block
                                let from_ref_block;

                                // This block has to point to the next block in the control flow graph (that terminator is an Option type)
                                match &data.terminator {
                                    Some(_x) => {
                                        from_ref_block = patch.new_block(BasicBlockData {
                                            statements: vec![],
                                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                            is_cleanup: false,
                                        });
                                    },
                                    _ => {
                                        from_ref_block = patch.new_block(BasicBlockData {
                                            statements: vec![],
                                            terminator: None,
                                            is_cleanup: false,
                                        });
                                    }
                                }

                                let g_root = root_generics[&local];
                                let generics_list = [g_root];

                                let from_ref_terminator = call_from_ref(tcx, local, root_temps.clone(), root_refs.clone(), &generics_list, from_ref_block);

                                // Insert a new function call to std::mem::size_of for the root type
                                let size_calc_block = patch.new_block(BasicBlockData {
                                    statements: vec![],
                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                    is_cleanup: false,
                                });

                                // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                
                                let ty_bool = ty::Const::from_bool(tcx, true);
                                let g_bool = GenericArg::from(ty_bool);
                                let generics_list_for_size = [g_root, g_bool];

                                let size_calc_terminator = call_size_of(tcx, local, local_sizes.clone(), &generics_list_for_size, size_calc_block);

                                // The current basic block's terminator is now replaced with the one we just created (which shifts the control flow to the intermediary block)
                                patch.patch_terminator(bb, from_ref_terminator);
                                patch.patch_terminator(from_ref_block, size_calc_terminator);
                            }
                        },
                        _ => (),
                    }
                },
                _ => (),
            }
        }


        // There will be a third loop for executing the drops for all the capabilities (identical to what we originally intended to do in elaborate_drops)
        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Drop { place, target, unwind, replace } => {
                            // Retrieve the associated capability using the two hash maps
                            // Inject inline asm to execute the drop on that capability
                            if alloc_roots.contains(&(place.local)) {
                                // Create a block terminator that will execute the function call we want to inject
                                let drop_terminator = TerminatorKind::Drop {
                                    place: place.clone(),
                                    target: target.clone(),
                                    unwind: unwind.clone(),
                                    replace: replace.clone(),
                                };

                                // Shift all the statements beyond our target statement to a new vector and clear them from the original block
                                let new_stmts = vec![];

                                // Create an intermediary block that will be inserted between the current block and the next block
                                let drop_block = patch.new_block(BasicBlockData {
                                    statements: new_stmts,
                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                    is_cleanup: data.is_cleanup.clone(),
                                });

                                patch.patch_terminator(drop_block, drop_terminator);

                                let new_terminator = TerminatorKind::Drop {
                                    place: Place { local: (root_temps[&place.local]).into(), projection: List::empty() },
                                    target: drop_block,
                                    unwind: unwind.clone(),
                                    replace: replace.clone(),
                                };

                                // The current basic block's terminator is now replaced with the one we just created (which shifts the control flow to the intermediary block)
                                patch.patch_terminator(bb, new_terminator);
                            }
                        },
                        _ => (),
                    }
                },
                _ => {}
            }
        }
        

        // For reference, printing the contents of each basic block in the body of this function
        for (_bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (_i, stmt) in data.statements.clone().iter().enumerate().rev() {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (_lhs, rhs)), .. } => {
                        match rhs {
                            Rvalue::Cast(cast_type, _operand, _) => {
                                match cast_type {
                                    CastKind::PointerCoercion(_coercion) => {
                                        println!("PointerCoercion: ");
                                    },/*
                                    CastKind::PtrToPtr => {
                                        println!("Rapture crate number: {}", rapture_crate_number);
                                        
                                        // Shift all the statements beyond our target statement to a new vector and clear them from the original block
                                        let mut new_stmts = vec![];
                                        for (j, stmt) in data.statements.iter_mut().enumerate() {
                                            if j > i {
                                                new_stmts.push(stmt.clone());
                                                stmt.make_nop();
                                            }
                                        }
                                        
                                        // Create an intermediary block that will be inserted between the current block and the next block
                                        let intermediary_block;

                                        // This block has to point to the next block in the control flow graph (that terminator is an Option type)
                                        match &data.terminator {
                                            Some(_x) => {
                                                intermediary_block = patch.new_block(BasicBlockData {
                                                    statements: new_stmts,
                                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                    is_cleanup: false,
                                                });
                                            },
                                            _ => {
                                                intermediary_block = patch.new_block(BasicBlockData {
                                                    statements: new_stmts,
                                                    terminator: None,
                                                    is_cleanup: false,
                                                });
                                            }
                                        }

                                        // Here we determine which function to target for the injection, using its crate number and definition index (which are statically fixed)
                                        let crate_num = CrateNum::new(0);
                                        let def_index = DefIndex::from_usize(6);
                                        let _def_id = DefId { krate: crate_num, index: def_index };

                                        // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                        let _generic_args: &rustc_middle::ty::List<GenericArg<'_>> = List::empty(); 

                                        // Creating the sugar of all the structures for the function type to be injected
                                        let ty_ = Ty::new(tcx, ty::FnDef(_def_id, _generic_args));
                                        let const_ = Const::Val(ConstValue::ZeroSized, ty_);
                                        let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
                                        let operand_ = Operand::Constant(const_operand);
                                        let dest_place = Place {local: (temp_1).into(), projection: List::empty()};

                                        println!("########### operand_: {:?}", operand_);

                                        // Create a block terminator that will execute the function call we want to inject
                                        let _intermediary_terminator = TerminatorKind::Call {
                                            func: operand_,
                                            args: vec![],
                                            destination: dest_place,
                                            target: Some(intermediary_block),
                                            unwind: UnwindAction::Continue,
                                            call_source: CallSource::Normal,
                                            fn_span: SPANS[0],
                                        };

                                        // The current basic block's terminator is now replaced with the one we just created (which shifts the control flow to the intermediary block)
                                        // patch.patch_terminator(bb, intermediary_terminator);

                                        //// DEBUG PRINTS
                                        // println!("ty_: {:?}", ty_);
                                        // println!("destination: {:?}", dest_place);
                                        // println!("target: {:?}", Some(intermediary_block));
                                        // println!("unwind: {:?}", UnwindAction::Continue);
                                        // println!("call_source: {:?}", CallSource::Normal);
                                        // println!("fn_span: {:?}", SPANS[0]);

                                        // This is a second block which injects another function call to a function (that prints something for us to verify our transformation)
                                        let intermediary_block_2 = patch.new_block(BasicBlockData {
                                            statements: vec![],
                                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                            is_cleanup: false,
                                        });

                                        // Here we determine which function to target for the injection, using its crate number and definition index (which are statically fixed)
                                        let crate_num_2 = CrateNum::new(0);
                                        let def_index_2 = DefIndex::from_usize(7);
                                        let _def_id_2 = DefId { krate: crate_num_2, index: def_index_2 };

                                        // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                        let _generic_args_2: &rustc_middle::ty::List<GenericArg<'_>> = List::empty();

                                        // Creating the sugar of all the structures for the function type to be injected
                                        let ty_2 = Ty::new(tcx, ty::FnDef(_def_id_2, _generic_args_2));
                                        let const_2 = Const::Val(ConstValue::ZeroSized, ty_2);
                                        let const_operand_2 = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_2 });
                                        let operand_2 = Operand::Constant(const_operand_2);
                                        let dest_place_2 = Place {local: (temp_2).into(), projection: List::empty()};
                                        
                                        println!("########### operand_: {:?}", operand_2);

                                        // This is how we create the arguments to be passed to the function that we are calling
                                        let operand_input = Operand::Copy(dest_place);
                                        let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

                                        // Create a block terminator that will execute the function call we want to inject
                                        let _intermediary_terminator_2 = TerminatorKind::Call {
                                            func: operand_2,
                                            args: vec![spanned_operand],
                                            destination: dest_place_2,
                                            target: Some(intermediary_block_2),
                                            unwind: UnwindAction::Continue,
                                            call_source: CallSource::Normal,
                                            fn_span: SPANS[0],
                                        };

                                        // The intermediary block is now made to point to the second intermediary block by virtue of its new terminator
                                        // patch.patch_terminator(intermediary_block, intermediary_terminator_2);

                                        //// DEBUG PRINTS
                                        // println!("ty_: {:?}", ty_);
                                        // println!("destination: {:?}", dest_place_2);
                                        // println!("target: {:?}", Some(intermediary_block));
                                        // println!("unwind: {:?}", UnwindAction::Continue);
                                        // println!("call_source: {:?}", CallSource::Normal);
                                        // println!("fn_span: {:?}", SPANS[0]);                                       
                                    },*/
                                    _ => (),
                                }
                            },
                            _ => (),
                        }
                    },
                    _ => (),
                }
            }

            /*
            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Call{func, args, destination, target, unwind, call_source, fn_span} => {
                            println!("func: {:?}", func);
                            match func {
                                Operand::Constant(c) => {
                                    println!("constoperand.user_ty: {:?}", c.user_ty);
                                    match c.const_ {
                                        Const::Val(_constval, ty) => {
                                            println!("const_.val: {:?}", _constval);
                                            println!("const_.ty: {:?}", ty);

                                            match ty.kind() {
                                                ty::FnDef(_def_id, generic_args) => {
                                                    println!("def_id: {:?}", _def_id);
                                                    println!("generic_args: {:?}", generic_args);
                                                },
                                                _ => (),
                                            }
                                        },
                                        _ => (),
                                    }
                                },
                                _ => (),
                            };
                            println!("args: {:?}", args);
                            println!("destination: {:?}, {:?}", usize::from(destination.local), destination.projection);
                            println!("target: {:?}", target);
                            println!("unwind: {:?}", unwind);
                            println!("call_source: {:?}", call_source);
                            println!("fn_span: {:?}", fn_span);
                        },
                        _ => (),
                    }
                },
                _ => {}
            }*/
        }
        
        patch.apply(body);
    }
}