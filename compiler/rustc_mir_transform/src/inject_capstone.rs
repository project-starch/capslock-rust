// use std::cmp::max;
use itertools::Itertools;
use std::collections::VecDeque;
use crate::MirPass;
// use rustc_ast::Mutability;
// use rustc_ast::InlineAsmOptions;
// use rustc_ast::InlineAsmTemplatePiece;
// use rustc_index::Idx;
// use rustc_data_structures::fx::{FxIndexMap, IndexEntry, IndexOccupiedEntry};
// use rustc_index::bit_set::BitSet;
// use rustc_index::interval::SparseIntervalMatrix;
// use rustc_middle::mir::visit::MutVisitor;
use rustc_middle::mir::patch::MirPatch;
use crate::ty::Ty;
use crate::{Spanned};
// use rustc_middle::mir::HasLocalDecls;
// use rustc_middle::mir::{dump_mir, PassWhere};
use rustc_index::{IndexVec, IndexSlice};
use rustc_middle::mir::*;
use rustc_middle::mir::visit::MutVisitor;
// use rustc_middle::mir::interpret::Scalar;
// use crate::ty::ty_kind;
use rustc_middle::ty::{self, TyCtxt};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
// use crate::ty::BorrowKind;
// use rustc_mir_dataflow::impls::MaybeLiveLocals;
// use rustc_mir_dataflow::points::{/*save_as_intervals,*/ DenseLocationMap, PointIndex};
// use rustc_mir_dataflow::Analysis;

use rustc_span::def_id::{CrateNum, DefIndex, DefId};
use rustc_middle::ty::{List, GenericArg};
use rustc_span::{Symbol, DUMMY_SP};
static SPANS: [rustc_span::Span; 1] = [DUMMY_SP];

struct BasicBlockUpdater<'tcx> {
    map: IndexVec<BasicBlock, BasicBlock>,
    tcx: TyCtxt<'tcx>,
}

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

fn permute<I: rustc_index::Idx + Ord, T>(data: &mut IndexVec<I, T>, map: &IndexSlice<I, I>) {
    // FIXME: It would be nice to have a less-awkward way to apply permutations,
    // but I don't know one that exists.  `sort_by_cached_key` has logic for it
    // internally, but not in a way that we're allowed to use here.
    let mut enumerated: Vec<_> = std::mem::take(data).into_iter_enumerated().collect();
    enumerated.sort_by_key(|p| map[p.0]);
    *data = enumerated.into_iter().map(|p| p.1).collect();
}

pub struct InjectCapstone;

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        println!("\nStart of CAPSTONE-Injection pass for function: {}", tcx.def_path_str(body.source.def_id()));
        let local_decls_clone = body.local_decls.clone();

        let mut patch = MirPatch::new(body);

        let num_of_crates = tcx.crates(()).len();

        let mut rapture_crate_number: usize = 0;
        let mut crate_num_flag: bool = true;
        // println!("Current crate symbol: {:?}", Symbol::as_str(& tcx.crate_name(CrateNum::from_usize(rapture_crate_number))));
        while crate_num_flag && num_of_crates > rapture_crate_number {
            rapture_crate_number += 1;
            crate_num_flag = Symbol::as_str(& tcx.crate_name(CrateNum::from_usize(rapture_crate_number))) != "rapture";
            // println!("Current crate symbol: {:?}", Symbol::as_str(& tcx.crate_name(CrateNum::from_usize(rapture_crate_number))));
        }

        if crate_num_flag {
            println!("Rapture crate not found.");
            return;
        }

        else {
            // Create a hash set that will store which variables we are performing create_capab for
            let mut capab_locals: FxHashSet<Local> = FxHashSet::default();

            println!("\n\n\tFirst pass.\n\n");

            for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
                for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
                    match stmt {
                        Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                            let lhs_type = local_decls_clone[lhs.local].ty;

                            println!("\nGeneric RHS: {:?}", rhs);
                            match rhs {
                                // Candidates: Cast, Ref, AdressOf. And technically Use as well, but that's just moving the same pointer around.
                                Rvalue::AddressOf(mutability, place) => {
                                    println!("RHS here. AddressOf found {:?} of type {:?}. The rhs place is {:?} with mutability {:?}", lhs.local, lhs_type, place, mutability);
                                },
                                Rvalue::Use(operand) => {
                                    println!("RHS here. Use found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, operand);
                                },
                                Rvalue::Repeat(operand, ..) => {
                                    println!("RHS here. Repeat found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, operand);
                                },
                                Rvalue::ThreadLocalRef(defid) => {
                                    println!("RHS here. ThreadLocalRef found {:?} of type {:?}. The rhs defid is {:?}", lhs.local, lhs_type, defid);
                                },
                                Rvalue::Len(place) => {
                                    println!("RHS here. Len found {:?} of type {:?}. The rhs place is {:?}", lhs.local, lhs_type, place);
                                },
                                Rvalue::BinaryOp(_binop, operands) => {
                                    println!("RHS here. BinaryOp found {:?} of type {:?}. The rhs operands are {:?}", lhs.local, lhs_type, operands);
                                },
                                Rvalue::CheckedBinaryOp(_binop, operands) => {
                                    println!("RHS here. CheckedBinaryOp found {:?} of type {:?}. The rhs operands are {:?}", lhs.local, lhs_type, operands);
                                },
                                Rvalue::Aggregate(_aggregate, operands) => {
                                    println!("RHS here. Aggregate found {:?} of type {:?}. The rhs operands are {:?}", lhs.local, lhs_type, operands);
                                },
                                Rvalue::ShallowInitBox(operand, ..) => {
                                    println!("RHS here. ShallowInitBox found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, operand);
                                },
                                Rvalue::Discriminant(place) => {
                                    println!("RHS here. Discriminant found {:?} of type {:?}. The rhs place is {:?}", lhs.local, lhs_type, place);
                                },
                                Rvalue::NullaryOp(op, ..) => {
                                    println!("RHS here. NullaryOp found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, op);
                                },
                                Rvalue::UnaryOp(unop, ..) => {
                                    println!("RHS here. UnaryOp found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, unop);
                                },
                                Rvalue::Ref(.., place) => {
                                    println!("RHS here. Reference found {:?} of type {:?}. The rhs place is {:?}", lhs.local, lhs_type, place);
                                    // This is the point where we will inject one function call to create_capab, passing in the pointer (that we just found) as an argument

                                    // Hack: Convert the type to a string and check if it contains the term "argument"
                                    let lhs_type_str = format!("{:?}", lhs_type);
                                    if !lhs_type_str.contains("Argument") && !place.projection.contains(&ProjectionElem::Deref) {
                                        capab_locals.insert(lhs.local);

                                        // Shift all the statements beyond our target statement to a new vector and clear them from the original block
                                        let mut new_stmts = vec![];
                                        for (j, stmt) in data.statements.iter_mut().enumerate() {
                                            if j > i { 
                                                new_stmts.push(stmt.clone());
                                                stmt.make_nop();
                                            }
                                        }

                                        // Create an intermediary block that will be inserted between the current block and the next block
                                        let create_capab_block;

                                        // This block has to point to the next block in the control flow graph (that terminator is an Option type)
                                        create_capab_block = patch.new_block(BasicBlockData {
                                            statements: new_stmts.clone(),
                                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                            is_cleanup: data.is_cleanup.clone(),
                                        });

                                        let crate_num = CrateNum::new(rapture_crate_number);
                                        let def_index = DefIndex::from_usize(0);
                                        let mut _def_id = DefId { krate: crate_num, index: def_index };
                                        let mut _def_id_int = 0;
                                        let mut name = tcx.def_path_str(_def_id);
                                        
                                        while name != "rapture::create_capab_from_ref" || name != "create_capab_from_ref" {
                                            if name == "rapture::create_capab_from_ptr" || name == "create_capab_from_ptr" {
                                                break;
                                            }
                                            _def_id_int += 1;
                                            _def_id = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(_def_id_int) };
                                            name = tcx.def_path_str(_def_id);
                                        }
                                        if name != "rapture::create_capab_from_ref" || name != "create_capab_from_ref" {
                                            println!("%$%$%$%$% Corrupted RaptureCell function definition: {}", name);
                                        }

                                        let root_ty = lhs_type;
                                        let generic_arg = GenericArg::from(root_ty);
                                        let generic_args = tcx.mk_args(&[generic_arg]);

                                        // Creating the sugar of all the structures for the function type to be injected
                                        let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
                                        let const_ = Const::Val(ConstValue::ZeroSized, ty_);
                                        let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
                                        let operand_ = Operand::Constant(const_operand);

                                        println!("Operand: {:?}", operand_);

                                        let dest_place = Place {local: (lhs.local).into(), projection: List::empty()};

                                        // This is how we create the arguments to be passed to the function that we are calling
                                        let operand_input = Operand::Copy(Place {local: lhs.local, projection: List::empty()});
                                        let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

                                        println!("Spanned Operand: {:?}", spanned_operand);

                                        let unwind_action: UnwindAction;
                                        if data.is_cleanup {
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
                                            target: Some(create_capab_block),
                                            unwind: unwind_action,
                                            call_source: CallSource::Normal,
                                            fn_span: SPANS[0],
                                        };

                                        patch.patch_terminator(bb, intermediary_terminator);
                                        break;
                                    }
                                    else {
                                        println!("Weird case. Pointer found {:?} of type {}. Projection list: {:?}. Ignored for injection.", lhs.local, lhs_type_str, place.projection);
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
            patch = MirPatch::new(body);

            println!("\n\n\tSecond pass.\n\n");

            for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
                for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
                    match stmt {
                        Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                            let lhs_type = local_decls_clone[lhs.local].ty;

                            println!("\nGeneric RHS: {:?}", rhs);
                            match rhs {
                                // Candidates: Cast, Ref, AdressOf. And technically Use as well, but that's just moving the same pointer around.
                                Rvalue::AddressOf(mutability, place) => {
                                    println!("RHS here. AddressOf found {:?} of type {:?}. The rhs place is {:?} with mutability {:?}", lhs.local, lhs_type, place, mutability);
                                    let mut new_stmts = vec![];
                                    for (j, stmt) in data.statements.iter_mut().enumerate() {
                                        if j > i { 
                                            new_stmts.push(stmt.clone());
                                            stmt.make_nop();
                                        }
                                    }

                                    // Create an intermediary block that will be inserted between the current block and the next block
                                    let create_capab_block;

                                    // This block has to point to the next block in the control flow graph (that terminator is an Option type)
                                    create_capab_block = patch.new_block(BasicBlockData {
                                        statements: new_stmts.clone(),
                                        terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                        is_cleanup: data.is_cleanup.clone(),
                                    });

                                    let crate_num = CrateNum::new(rapture_crate_number);
                                    let def_index = DefIndex::from_usize(0);
                                    let mut _def_id = DefId { krate: crate_num, index: def_index };
                                    let mut _def_id_int = 0;
                                    let mut name = tcx.def_path_str(_def_id);

                                    // Check whether the thing being borrowed was mutable
                                    let is_mut;
                                    match mutability {
                                        Mutability::Mut => {
                                            is_mut = true;
                                        },
                                        Mutability::Not => {
                                            is_mut = false;
                                        },
                                    }

                                    let function_name;
                                    
                                    if is_mut {
                                        function_name = "rapture::borrow_mut";
                                    }
                                    else {
                                        function_name = "rapture::borrow";
                                    }
                                    
                                    while name != function_name {
                                        _def_id_int += 1;
                                        _def_id = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(_def_id_int) };
                                        name = tcx.def_path_str(_def_id);
                                    }
                                    if name != function_name {
                                        println!("%$%$%$%$% Corrupted RaptureCell function definition: {}", name);
                                    }

                                    let root_ty = lhs_type;
                                    let generic_arg = GenericArg::from(root_ty);
                                    let generic_args = tcx.mk_args(&[generic_arg]);

                                    // Creating the sugar of all the structures for the function type to be injected
                                    let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
                                    let const_ = Const::Val(ConstValue::ZeroSized, ty_);
                                    let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
                                    let operand_ = Operand::Constant(const_operand);

                                    println!("Operand: {:?}", operand_);

                                    let dest_place = Place {local: (lhs.local).into(), projection: List::empty()};

                                    // This is how we create the arguments to be passed to the function that we are calling
                                    let operand_input = Operand::Copy(Place {local: place.local, projection: List::empty()});
                                    let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

                                    println!("Spanned Operand: {:?}", spanned_operand);

                                    let unwind_action: UnwindAction;
                                    if data.is_cleanup {
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
                                        target: Some(create_capab_block),
                                        unwind: unwind_action,
                                        call_source: CallSource::Normal,
                                        fn_span: SPANS[0],
                                    };

                                    patch.patch_terminator(bb, intermediary_terminator);
                                    break;
                                },
                                Rvalue::Use(operand) => {
                                    println!("RHS here. Use found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, operand);
                                },
                                Rvalue::Repeat(operand, ..) => {
                                    println!("RHS here. Repeat found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, operand);
                                },
                                Rvalue::ThreadLocalRef(defid) => {
                                    println!("RHS here. ThreadLocalRef found {:?} of type {:?}. The rhs defid is {:?}", lhs.local, lhs_type, defid);
                                },
                                Rvalue::Len(place) => {
                                    println!("RHS here. Len found {:?} of type {:?}. The rhs place is {:?}", lhs.local, lhs_type, place);
                                },
                                Rvalue::BinaryOp(_binop, operands) => {
                                    println!("RHS here. BinaryOp found {:?} of type {:?}. The rhs operands are {:?}", lhs.local, lhs_type, operands);
                                },
                                Rvalue::CheckedBinaryOp(_binop, operands) => {
                                    println!("RHS here. CheckedBinaryOp found {:?} of type {:?}. The rhs operands are {:?}", lhs.local, lhs_type, operands);
                                },
                                Rvalue::Aggregate(_aggregate, operands) => {
                                    println!("RHS here. Aggregate found {:?} of type {:?}. The rhs operands are {:?}", lhs.local, lhs_type, operands);
                                },
                                Rvalue::ShallowInitBox(operand, ..) => {
                                    println!("RHS here. ShallowInitBox found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, operand);
                                },
                                Rvalue::Discriminant(place) => {
                                    println!("RHS here. Discriminant found {:?} of type {:?}. The rhs place is {:?}", lhs.local, lhs_type, place);
                                },
                                Rvalue::NullaryOp(op, ..) => {
                                    println!("RHS here. NullaryOp found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, op);
                                },
                                Rvalue::UnaryOp(unop, ..) => {
                                    println!("RHS here. UnaryOp found {:?} of type {:?}. The rhs operand is {:?}", lhs.local, lhs_type, unop);
                                },
                                Rvalue::Ref(.., place) => {
                                    println!("RHS here. Reference found {:?} of type {:?}. The rhs place is {:?}", lhs.local, lhs_type, place);
                                },
                                Rvalue::Cast(cast_kind, operand, ty) => {
                                    println!("Cast found of kind {:?} with operand {:?} and type {:?}", cast_kind, operand, ty);
                                    match cast_kind {
                                        CastKind::PtrToPtr => {
                                            println!("PtrToPtr cast found.");
                                            // There are only two cases in which a borrow will take place
                                            // The source pointer and the target type mismatch, ie:
                                            // 1. Source is a primitive reference, target is a raw pointer
                                            // 2. Source is a raw pointer, target is a primitive reference

                                            let mut source_is_ref = false;
                                            let mut target_is_ref = false;

                                            match operand {
                                                Operand::Copy(Place {local, ..}) => {
                                                    let source_type = local_decls_clone[*local].ty;
                                                    match source_type.kind() {
                                                        ty::Ref(_, _, _) => {
                                                            source_is_ref = true;
                                                        },
                                                        _ => (),
                                                    }
                                                },
                                                Operand::Move(Place {local, ..}) => {
                                                    let source_type = local_decls_clone[*local].ty;
                                                    match source_type.kind() {
                                                        ty::Ref(_, _, _) => {
                                                            source_is_ref = true;
                                                        },
                                                        _ => (),
                                                    }
                                                },
                                                _ => (),
                                            }

                                            match ty.kind() {
                                                ty::Ref(_, _, _) => {
                                                    target_is_ref = true;
                                                },
                                                _ => (),
                                            }

                                            if (source_is_ref && !target_is_ref) || (!source_is_ref && target_is_ref) {
                                                // Shift all the statements beyond our target statement to a new vector and clear them from the original block
                                                let mut new_stmts = vec![];
                                                for (j, stmt) in data.statements.iter_mut().enumerate() {
                                                    if j > i { 
                                                        new_stmts.push(stmt.clone());
                                                        stmt.make_nop();
                                                    }
                                                }

                                                // Create an intermediary block that will be inserted between the current block and the next block
                                                let create_capab_block;

                                                // This block has to point to the next block in the control flow graph (that terminator is an Option type)
                                                create_capab_block = patch.new_block(BasicBlockData {
                                                    statements: new_stmts.clone(),
                                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                    is_cleanup: data.is_cleanup.clone(),
                                                });

                                                let crate_num = CrateNum::new(rapture_crate_number);
                                                let def_index = DefIndex::from_usize(0);
                                                let mut _def_id = DefId { krate: crate_num, index: def_index };
                                                let mut _def_id_int = 0;
                                                let mut name = tcx.def_path_str(_def_id);

                                                let function_name;

                                                // check if the lhs is a mutable type
                                                let mut is_mutable = false;
                                                match lhs_type.kind() {
                                                    ty::Ref(_, _, mutability) => {
                                                        if *mutability == rustc_middle::ty::Mutability::Mut {
                                                            is_mutable = true;
                                                        }
                                                    },
                                                    _ => (),
                                                }

                                                if is_mutable {
                                                    function_name = "rapture::borrow_mut";
                                                }
                                                else {
                                                    function_name = "rapture::borrow";
                                                }

                                                println!("Function name: {}", function_name);
                                                
                                                while name != function_name {
                                                    _def_id_int += 1;
                                                    _def_id = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(_def_id_int) };
                                                    name = tcx.def_path_str(_def_id);
                                                }
                                                if name != function_name {
                                                    println!("%$%$%$%$% Corrupted RaptureCell function definition: {}", name);
                                                }

                                                let root_ty = lhs_type;
                                                let generic_arg = GenericArg::from(root_ty);
                                                let generic_args = tcx.mk_args(&[generic_arg]);

                                                // Creating the sugar of all the structures for the function type to be injected
                                                let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
                                                let const_ = Const::Val(ConstValue::ZeroSized, ty_);
                                                let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
                                                let operand_ = Operand::Constant(const_operand);

                                                println!("Operand: {:?}", operand_);

                                                let dest_place = Place {local: (lhs.local).into(), projection: List::empty()};

                                                // This is how we create the arguments to be passed to the function that we are calling
                                                let operand_input = Operand::Copy(Place {local: lhs.local, projection: List::empty()});
                                                let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

                                                println!("Spanned Operand: {:?}", spanned_operand);

                                                let unwind_action: UnwindAction;
                                                if data.is_cleanup {
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
                                                    target: Some(create_capab_block),
                                                    unwind: unwind_action,
                                                    call_source: CallSource::Normal,
                                                    fn_span: SPANS[0],
                                                };

                                                patch.patch_terminator(bb, intermediary_terminator);
                                                break;
                                            }
                                            else {
                                                println!("Casting ptr to ptr or ref to ref. No borrow here.");
                                            }
                                        },
                                        _ => (),
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
            patch = MirPatch::new(body);

            // reorder basic blocks
            let rpo: IndexVec<BasicBlock, BasicBlock> = body.basic_blocks.reverse_postorder().iter().copied().collect();
            if rpo.iter().is_sorted() {
                return;
            }

            let mut updater = BasicBlockUpdater { map: rpo.invert_bijective_mapping(), tcx };
            debug_assert_eq!(updater.map[START_BLOCK], START_BLOCK);
            updater.visit_body(body);

            permute(body.basic_blocks.as_mut(), &updater.map);
            // reorder ends

            // Traverse the basic blocks in DFS order by following the targets of the terminators
            
            let mut active_roots: Vec<Local> = vec![];
            let mut active_roots_per_bb: FxHashMap<BasicBlock, Vec<Local>> = FxHashMap::default();

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
                                active_roots = active_roots_per_bb[&parent_map[&(bb.index())]].clone();
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
                                                        if tcx.def_path_str(_def_id) == "rapture::create_capab_from_ref" || tcx.def_path_str(_def_id) == "rapture::create_capab_from_ptr" || tcx.def_path_str(_def_id) == "create_capab_from_ref" || tcx.def_path_str(_def_id) == "create_capab_from_ptr" {
                                                            if !active_roots.contains(&destination.local) {
                                                                active_roots.push(destination.local.clone());
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
                        active_roots_per_bb.insert(bb, active_roots.clone());
                    },
                    _ => (),
                }
                previous_bb = bb;
            }

            println!("Active roots per BB: {:?}", active_roots_per_bb);

            let mut last_block_in_scope: Vec<BasicBlock> = vec![];
            let mut return_points: Vec<BasicBlock> = vec![];

            let mut scope_children: FxHashMap<usize, Vec<usize>> = FxHashMap::default();

            let mut root_scope: FxHashMap<Local, usize> = FxHashMap::default();
            let mut last_active_roots_per_scope: FxHashMap<usize, Vec<Local>> = FxHashMap::default();

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
                if data.is_cleanup {continue;}
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
                            TerminatorKind::Return /*| TerminatorKind::UnwindTerminate(_) | TerminatorKind::UnwindResume*/ | TerminatorKind::CoroutineDrop => {
                                last_block_in_scope[x.source_info.scope.index()] = bb.into();
                                return_points.push(bb.into());
                            },
                            _ => {},
                        }
                        for (_i, stmt) in data.statements.clone().iter().enumerate() {
                            match stmt {
                                Statement {kind: StatementKind::Assign(box (lhs, ..)), .. } => {
                                    match lhs {
                                        Place { local, .. } => {
                                            if active_roots.contains(local) {
                                                root_scope.insert(local.clone(), x.source_info.scope.index());
                                            }
                                        },
                                    }
                                },
                                _ => (),
                            }
                        }
                        match &data.terminator {
                            Some(x) => {
                                match &x.kind {
                                    TerminatorKind::Call { destination, ..} => {
                                        let local = &(destination.local);
                                        if active_roots.contains(local) {
                                            root_scope.insert(local.clone(), x.source_info.scope.index());
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
            }

            for root in active_roots.iter() {
                if !root_scope.contains_key(root) {continue;}
                let scope = root_scope[root];
                if !last_active_roots_per_scope.contains_key(&scope) {last_active_roots_per_scope.insert(scope.clone(), vec![]);}
                last_active_roots_per_scope.get_mut(&scope).unwrap().push(root.clone());
            }

            println!("\n\n\tThird pass.\n\n");
            println!("Capab locals: {:?}", capab_locals);

            // Creating a fixed number of temporary variables of fixed type to be used by our injected functions
            let empty_tuple_type = Ty::new(tcx, ty::Tuple(List::empty()));
            let empty_tuple_temp = body.local_decls.push(LocalDecl::new(empty_tuple_type, SPANS[0]));

            let mut dropped_refs: Vec<Local> = vec![];
            // Form a set of the blocks that require a drop
            let mut drop_blocks: FxHashSet<BasicBlock> = FxHashSet::default();
            for return_point in return_points.iter() {
                drop_blocks.insert(*return_point);
            }
            for scope in 0..body.source_scopes.len() {
                if !last_active_roots_per_scope.contains_key(&scope) {last_active_roots_per_scope.insert(scope.clone(), vec![]);}
                if last_active_roots_per_scope[(&scope).into()].len() > 0 && last_block_in_scope[scope] != START_BLOCK {
                    drop_blocks.insert(last_block_in_scope[scope]);
                }
            }
            // println!("drop blocks: {:?}", drop_blocks);

            for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
                if drop_blocks.contains(&bb) {
                    // println!("current block during drop: {:?}", &bb);
                    let roots_to_drop = {
                        if return_points.contains(&bb) {
                            println!("***********Drop roots: {:?} at return point", active_roots_per_bb[&bb].clone());
                            active_roots_per_bb[&bb].clone()
                        } else {
                            let scope: usize = {
                                let mut scope = 0;
                                for (key, value) in last_block_in_scope.iter().enumerate() {
                                    if *value == bb && last_active_roots_per_scope[(&key).into()].len() > 0 {
                                        scope = key as usize;
                                        break;
                                    }
                                }
                                scope
                            };
                            println!("***********Drop roots: {:?} at scope: {:?}", last_active_roots_per_scope[&(scope)].clone(), scope.clone());
                            last_active_roots_per_scope[&(scope)].clone()
                        }
                    };
                    let mut expected_terminator = data.terminator.as_ref().unwrap().kind.clone();
                    for root_temp in roots_to_drop.iter() {
                        if dropped_refs.contains(root_temp) {
                            continue;
                        }
                        else {
                            dropped_refs.push(root_temp.clone());
                            println!("******* Performing drop for root with reftemp: {:?}, at block: {:?}", root_temp, &bb);
                        }
                        // The following code injects drop and invalidate for some root allocation local. Right now they are unreachable in the CFG and only go to themselvers.
                        // The target location block is to be decided given the search for termination blocks.
                        
                        let invalidate_block = patch.new_block(BasicBlockData {
                            statements: vec![],
                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                            is_cleanup: data.is_cleanup.clone(),
                        });

                        let crate_num = CrateNum::new(rapture_crate_number);
                        let def_index = DefIndex::from_usize(0);
                        let mut _def_id = DefId { krate: crate_num, index: def_index };
                        let mut _def_id_int = 0;
                        let mut name = tcx.def_path_str(_def_id);
                        
                        while name != "revoke" || name != "rapture::revoke" {
                            if name == "rapture::revoke" || name == "revoke" {
                                break;
                            }
                            _def_id_int += 1;
                            _def_id = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(_def_id_int) };
                            name = tcx.def_path_str(_def_id);
                        }
                        if name != "revoke" || name != "rapture::revoke" {
                            println!("%$%$%$%$% Corrupted RaptureCell function definition: {}", name);
                        }

                        let root_ty = local_decls_clone[*root_temp].ty;
                        let generic_arg = GenericArg::from(root_ty);
                        let generic_args = tcx.mk_args(&[generic_arg]);

                    // Creating the sugar of all the structures for the function type to be injected
                        let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
                        let const_ = Const::Val(ConstValue::ZeroSized, ty_);
                        let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
                        let operand_ = Operand::Constant(const_operand);

                        println!("Operand: {:?}", operand_);

                        let dest_place = Place {local: (empty_tuple_temp).into(), projection: List::empty()};

                        // This is how we create the arguments to be passed to the function that we are calling
                        let operand_input = Operand::Copy(Place {local: *root_temp, projection: List::empty()});
                        let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

                        println!("Spanned Operand: {:?}", spanned_operand);

                        let unwind_action: UnwindAction;
                        if data.is_cleanup {
                            unwind_action = UnwindAction::Terminate(UnwindTerminateReason::InCleanup);
                        }
                        else {
                            unwind_action = UnwindAction::Continue;
                        }
                        // Create a block terminator that will execute the function call we want to inject
                        let invalidate_terminator = TerminatorKind::Call {
                            func: operand_,
                            args: vec![spanned_operand],
                            destination: dest_place,
                            target: Some(invalidate_block),
                            unwind: unwind_action,
                            call_source: CallSource::Normal,
                            fn_span: SPANS[0],
                        };
                        
                        let drop_place = Place {local: (*root_temp).into(), projection: List::empty()};
                        
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
                    }
                    patch.patch_terminator(bb, expected_terminator);
                }
            }   

            // In this pass we inject our revokes by checking when our tracked locals are being dropped (via the StorageDead statement)
            // for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            //     for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
            //         match stmt {
            //             Statement { kind: StatementKind::StorageDead(local), .. } => {
            //                 if capab_locals.contains(local) {
            //                     // Shift all the statements beyond our target statement to a new vector and clear them from the original block
            //                     let mut new_stmts = vec![];
            //                     for (j, stmt) in data.statements.iter_mut().enumerate() {
            //                         if j > i { 
            //                             new_stmts.push(stmt.clone());
            //                             stmt.make_nop();
            //                         }
            //                     }

            //                     // Create an intermediary block that will be inserted between the current block and the next block
            //                     let revoke_capab_block;

            //                     // This block has to point to the next block in the control flow graph (that terminator is an Option type)
            //                     revoke_capab_block = patch.new_block(BasicBlockData {
            //                         statements: new_stmts.clone(),
            //                         terminator: Some(data.terminator.as_ref().unwrap().clone()),
            //                         is_cleanup: data.is_cleanup.clone(),
            //                     });

            //                     let crate_num = CrateNum::new(rapture_crate_number);
            //                     let def_index = DefIndex::from_usize(0);
            //                     let mut _def_id = DefId { krate: crate_num, index: def_index };
            //                     let mut _def_id_int = 0;
            //                     let mut name = tcx.def_path_str(_def_id);
                                
            //                     while name != "revoke" {
            //                         _def_id_int += 1;
            //                         _def_id = DefId { krate: CrateNum::new(rapture_crate_number), index: DefIndex::from_usize(_def_id_int) };
            //                         name = tcx.def_path_str(_def_id);
            //                     }
            //                     if name != "revoke" {
            //                         println!("%$%$%$%$% Corrupted RaptureCell function definition: {}", name);
            //                     }

            //                     let root_ty = local_decls_clone[*local].ty;
            //                     let generic_arg = GenericArg::from(root_ty);
            //                     let generic_args = tcx.mk_args(&[generic_arg]);

            //                     // Creating the sugar of all the structures for the function type to be injected
            //                     let ty_ = Ty::new(tcx, ty::FnDef(_def_id, generic_args));
            //                     let const_ = Const::Val(ConstValue::ZeroSized, ty_);
            //                     let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
            //                     let operand_ = Operand::Constant(const_operand);

            //                     println!("Operand: {:?}", operand_);

            //                     let dest_place = Place {local: (empty_tuple_temp).into(), projection: List::empty()};

            //                     // This is how we create the arguments to be passed to the function that we are calling
            //                     let operand_input = Operand::Copy(Place {local: *local, projection: List::empty()});
            //                     let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

            //                     println!("Spanned Operand: {:?}", spanned_operand);

            //                     let unwind_action: UnwindAction;
            //                     if data.is_cleanup {
            //                         unwind_action = UnwindAction::Terminate(UnwindTerminateReason::InCleanup);
            //                     }
            //                     else {
            //                         unwind_action = UnwindAction::Continue;
            //                     }
            //                     // Create a block terminator that will execute the function call we want to inject
            //                     let intermediary_terminator = TerminatorKind::Call {
            //                         func: operand_,
            //                         args: vec![spanned_operand],
            //                         destination: dest_place,
            //                         target: Some(revoke_capab_block),
            //                         unwind: unwind_action,
            //                         call_source: CallSource::Normal,
            //                         fn_span: SPANS[0],
            //                     };

            //                     patch.patch_terminator(bb, intermediary_terminator);
            //                     capab_locals.remove(local);
            //                     break;
            //                 }
            //             },
            //             _ => (),
            //         }
            //     }
            // }

            patch.apply(body);
            println!("Successfully ran CAPSTONE-injection pass on function: {}", tcx.def_path_str(body.source.def_id()));
        }
    }
}