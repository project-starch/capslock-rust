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
    Statement, StatementKind, TerminatorKind, Operand, Const, ConstValue, ConstOperand, BorrowKind, MutBorrowKind
};
// use crate::ty::ty_kind;
use rustc_middle::ty::{self};
use rustc_middle::ty::TyCtxt;
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
                            // To be written (Fangqi is working on this)
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

        // Obtaining the ADT type for MutDLTBoundedPointer
        let def_id_adt = DefId { krate: CrateNum::new(20), index: DefIndex::from_usize(83) };
        let adt_type = tcx.adt_def(def_id_adt);

        // Creating temporaries for each of the roots that we have found. These temporaries will be of type MutDLTBoundedPointer
        let mut root_temps: FxHashMap<Local, Local> = FxHashMap::default();
        let mut root_refs: FxHashMap<Local, Local> = FxHashMap::default();
        let mut root_generics: FxHashMap<Local, GenericArg<'_>> = FxHashMap::default();
        for root in alloc_roots.iter() {
            // We make a generic arg corresponding to the type of the root
            let root_ty = body.local_decls[*root].ty;
            let generic_arg = GenericArg::from(root_ty);
            let generic_args = tcx.mk_args(&[generic_arg]);
            root_generics.insert(*root, generic_arg);
            let root_adt_type = Ty::new(tcx, ty::Adt(adt_type, generic_args));
            let temp = body.local_decls.push(LocalDecl::new(root_adt_type, SPANS[0]));
            root_temps.insert(*root, temp);
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

        // Second, downward, loop to find the first uses of those pointers as well as track their borrows
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
                                    println!("local: {:?}", local);

                                    // Print all details of the statement at i+1
                                    match &data.statements[i+1].kind {
                                        StatementKind::Assign(box (lhs1, rhs1)) => {
                                            println!("stmt lhs: {:?}", lhs1);
                                            match rhs1 {
                                                Rvalue::Ref(region, borrowkind, place) => {
                                                    println!("rhs: Ref: {:?}, {:?}, {:?}", region, borrowkind, place);
                                                },
                                                _ => (),
                                            }
                                        },
                                        _ => (),
                                    }

                                    let new_stmt = Statement {
                                        source_info: stmt.source_info,
                                        kind: StatementKind::Assign(Box::new((root_refs[local].into(), Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Mut { kind: MutBorrowKind::Default }, Place { local: *local, projection: List::empty() })))),
                                    };

                                    // Shift all the statements beyond our target statement to a new vector and clear them from the original block
                                    let mut new_stmts = vec![];
                                    for (j, stmt) in data.statements.iter_mut().enumerate() {
                                        if j > i { //TODO: REMEMBER TO REVERT THIS TO j > i !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                                            new_stmts.push(stmt.clone());
                                            stmt.make_nop();
                                        }
                                    }

                                    data.statements.push(new_stmt);

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
                                    let crate_num = CrateNum::new(20);
                                    let def_index = DefIndex::from_usize(98);
                                    let _def_id = DefId { krate: crate_num, index: def_index };

                                    // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                    let g = root_generics[&local];
                                    let generic_args: &rustc_middle::ty::List<GenericArg<'_>> = tcx.mk_args(&[g]); 

                                    // Creating the sugar of all the structures for the function type to be injected
                                    let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
                                    let const_ = Const::Val(ConstValue::ZeroSized, ty_);
                                    let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
                                    let operand_ = Operand::Constant(const_operand);
                                    let dest_place = Place {local: (root_temps[&local]).into(), projection: List::empty()};

                                    // This is how we create the arguments to be passed to the function that we are calling
                                    let operand_input = Operand::Copy(Place {local: (root_refs[local]).into(), projection: List::empty()});
                                    let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

                                    println!("########### operand_: {:?}", operand_);
                                    println!("########### dest_place: {:?}", dest_place);
                                    println!("########### spanned_operand: {:?}", spanned_operand);

                                    // Create a block terminator that will execute the function call we want to inject
                                    let intermediary_terminator = TerminatorKind::Call {
                                        func: operand_,
                                        args: vec![spanned_operand],
                                        destination: dest_place,
                                        target: Some(intermediary_block),
                                        unwind: UnwindAction::Continue,
                                        call_source: CallSource::Normal,
                                        fn_span: SPANS[0],
                                    };

                                    // The current basic block's terminator is now replaced with the one we just created (which shifts the control flow to the intermediary block)
                                    patch.patch_terminator(bb, intermediary_terminator);
                                }
                                // match &body.local_decls[local].ty.kind {
                                //     ty::Ref(_, ty, _) => {
                                //         println!("ty: {:?}", ty);
                                //     },
                                //     _ => (),
                                // }
                            }
                        }
                    },
                    _ => (),
                }
            }
            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Call { func, args, destination, target, unwind, call_source, fn_span } => {
                            if alloc_roots.contains(&(destination.local)) {
                                println!("local: {:?}", destination.local);

                                // Here we determine which function to target for the injection, using its crate number and definition index (which are statically fixed)
                                let crate_num = CrateNum::new(20);
                                let def_index = DefIndex::from_usize(98);
                                let _def_id = DefId { krate: crate_num, index: def_index };

                                // The function may have generic types as its parameters. These need to be statically mentioned if we are injecting a call to it
                                let g = root_generics[&destination.local];
                                let generic_args: &rustc_middle::ty::List<GenericArg<'_>> = tcx.mk_args(&[g]); 

                                // Creating the sugar of all the structures for the function type to be injected
                                let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
                                let const_ = Const::Val(ConstValue::ZeroSized, ty_);
                                let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
                                let operand_ = Operand::Constant(const_operand);
                                let dest_place = Place {local: (1 as usize).into(), projection: List::empty()};

                                // This is how we create the arguments to be passed to the function that we are calling
                                let operand_input = Operand::Copy((destination.local).into());
                                let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

                                println!("t########### operand_: {:?}", operand_);
                                println!("t########### dest_place: {:?}", dest_place);
                                println!("t########### spanned_operand: {:?}", spanned_operand);

                                // Create a block terminator that will execute the function call we want to inject
                                let intermediary_terminator = TerminatorKind::Call {
                                    func: operand_,
                                    args: vec![spanned_operand],
                                    destination: dest_place,
                                    target: target.clone(),
                                    unwind: UnwindAction::Continue,
                                    call_source: CallSource::Normal,
                                    fn_span: SPANS[0],
                                };

                                // Shift all the statements beyond our target statement to a new vector and clear them from the original block
                                let new_stmts = vec![];
                                
                                // Create an intermediary block that will be inserted between the current block and the next block
                                let intermediary_block = patch.new_block(BasicBlockData {
                                    statements: new_stmts,
                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                    is_cleanup: false,
                                });

                                patch.patch_terminator(intermediary_block, intermediary_terminator);

                                let new_terminator = TerminatorKind::Call {
                                    func: func.clone(),
                                    args: args.clone(),
                                    destination: destination.clone(),
                                    target: Some(intermediary_block),
                                    unwind: unwind.clone(),
                                    call_source: call_source.clone(),
                                    fn_span: fn_span.clone(),
                                };

                                // The current basic block's terminator is now replaced with the one we just created (which shifts the control flow to the intermediary block)
                                patch.patch_terminator(bb, new_terminator);
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

            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Call{func, args, destination, target, unwind, call_source, fn_span} => {
                            println!("func: {:?}", func);
                            match func {
                                Operand::Constant(c) => {
                                    match c.const_ {
                                        Const::Val(_constval, ty) => {
                                            println!("const_.ty: {:?}", ty);
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
            }
        }
        
        patch.apply(body);
    }
}