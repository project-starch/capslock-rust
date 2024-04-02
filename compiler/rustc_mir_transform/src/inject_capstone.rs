use crate::MirPass;
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
    /*traversal,*/ Body, LocalDecl, /*Local, */ /*InlineAsmOperand, LocalKind, Location,*/ BasicBlockData, Place, UnwindAction, CallSource, CastKind, Rvalue, 
    Statement, StatementKind, TerminatorKind, Operand, Const, ConstValue, ConstOperand
};
// use crate::ty::ty_kind;
use rustc_middle::ty;
use rustc_middle::ty::TyCtxt;
// use rustc_data_structures::fx::FxHashMap;
// use rustc_mir_dataflow::impls::MaybeLiveLocals;
// use rustc_mir_dataflow::points::{/*save_as_intervals,*/ DenseLocationMap, PointIndex};
// use rustc_mir_dataflow::Analysis;

use rustc_span::def_id::{DefId, DefIndex, CrateNum};
use rustc_middle::ty::{List, GenericArg};
use rustc_span::DUMMY_SP;
static SPANS: [rustc_span::Span; 1] = [DUMMY_SP];

// struct RootAllocations {
//     // A map between every variable and its root allocation (identified by backpropagation)
//     // Question: What is the ideal type for a variable idenitifier? Local? LocalDecl? String?
//     roots: FxHashMap<Local, Local>,
// }

// struct AllocationCapabilities {
//     // A map between a root allocation and the address of its associated capability in memory
//     capabilities: FxHashMap<Local, usize>,
// }

pub struct InjectCapstone;

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut patch = MirPatch::new(body);

        let return_type_1 = Ty::new(tcx, ty::Bool);
        let temp_1 = body.local_decls.push(LocalDecl::new(return_type_1, SPANS[0]));
        let return_type_2 = Ty::new(tcx, ty::Bool);
        let temp_2 = body.local_decls.push(LocalDecl::new(return_type_2, SPANS[0]));

        // let root_allocations = RootAllocations {
        //     roots: FxHashMap::default(),
        // };

        // let allocation_capabilities = AllocationCapabilities {
        //     capabilities: FxHashMap::default(),
        // };
        
        // First, upward, loop to find the last assignments to pointers
        for (_bb, data) in body.basic_blocks_mut().iter_enumerated_mut().rev() {
            for (_i, stmt) in data.statements.iter_mut().enumerate().rev() {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (_lhs, rhs)), .. } => {
                        match rhs {
                            // Match the rvalue on the RHS based on what we want
                            // To be written (Fangqi is working on this)
                                // Once found, run backprop to locate the root of those assigned values (lhs)
                                // Add that assigned value and the root to the RootAllocations struct
                            _ => (),
                        }
                    },
                    _ => (),
                }
            }
        }


        // Second, downward, loop to find the first uses of those pointers as well as their borrows
        for (_bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (_i, stmt) in data.statements.iter_mut().enumerate() {
                match stmt {
                    Statement {kind: StatementKind::Assign(box (_lhs, _rhs)), .. } => {
                        // match lhs {
                        //     // Match the lvalue on LHS for all root allocations
                        //         // Upon match,
                        //             // Inject inline asm here to GENerate the CAPabilities for those roots
                        //             // Store the capabilities in memory (take inspiration from library solution)
                        //             // Store the capabilities (or their addresses) into the AllocationCapabilities struct
                        //     _ => todo!(),
                        // };
                        // match rhs {
                        //     // Match the rvalue on the RHS based on what we want
                        //         // Upon match, check if the value being assigned is in the Candidates struct
                        //             // If so, inject inline asm to load the capability from memory
                        //             // Its address can be found using the two hash maps
                        //             // Use the capability to perform the operation
                        //     _ => (),
                        // }
                    },
                    _ => (),
                }
            }
        }


        // There will be a third loop for executing the drops for all the capabilities (identical to what we originally intended to do in elaborate_drops)
        for (_bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Drop { place, .. } => {
                            // Retrieve the associated capability using the two hash maps
                            // Inject inline asm to execute the drop on that capability
                            _ = place;
                        },
                        _ => (),
                    }
                },
                _ => {}
            }
        }
        

        // For reference, printing the contents of each basic block in the body of this function
        for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {    
            println!("Basic Block: {}", bb.index());        
            for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
                println!("Statement {}", i);
                match stmt {
                    Statement { kind: StatementKind::Assign(box (_lhs, rhs)), .. } => {
                        match rhs {
                            Rvalue::Cast(cast_type, _operand, _) => {
                                match cast_type {
                                    CastKind::PointerCoercion(_coercion) => {
                                        println!("PointerCoercion: ");
                                    },
                                    CastKind::PtrToPtr => {
                                        let mut new_stmts = vec![];

                                        for (j, stmt) in data.statements.iter_mut().enumerate() {
                                            if j > i {
                                                new_stmts.push(stmt.clone());
                                                stmt.make_nop();
                                            }
                                        }
                                        
                                        let inline_block;

                                        match &data.terminator {
                                            Some(_x) => {
                                                inline_block = patch.new_block(BasicBlockData {
                                                    statements: new_stmts,
                                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                    is_cleanup: false,
                                                });
                                            },
                                            _ => {
                                                inline_block = patch.new_block(BasicBlockData {
                                                    statements: new_stmts,
                                                    terminator: None,
                                                    is_cleanup: false,
                                                });
                                            }
                                        }

                                        // println!("PtrToPtr: {:?}", operand);

                                        let crate_num = CrateNum::new(0);
                                        let def_index = DefIndex::from_usize(6);
                                        let _def_id = DefId { krate: crate_num, index: def_index };

                                        let _generic_args: &rustc_middle::ty::List<GenericArg<'_>> = List::empty();

                                        // let tykind_ = ty::FnDef(_def_id, _generic_args);
                                        let ty_ = Ty::new(tcx, ty::FnDef(_def_id, _generic_args));

                                        let const_ = Const::Val(ConstValue::ZeroSized, ty_);
                                        
                                        let const_operand = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_ });
                                        let operand_ = Operand::Constant(const_operand);
                                        println!("########### operand_: {:?}", operand_);

                                        // let local = body.local_decls.push(LocalDecl::new(ty_, SPANS[0]));

                                        let dest_place = Place {local: (temp_1).into(), projection: List::empty()};

                                        // Call a function named do_nothing present in rapture::pointer
                                        let inline_terminator = TerminatorKind::Call {
                                            func: operand_,
                                            args: vec![],
                                            destination: dest_place,
                                            target: Some(inline_block),
                                            unwind: UnwindAction::Continue,
                                            call_source: CallSource::Normal,
                                            fn_span: SPANS[0],
                                        };

                                        // println!("ty_: {:?}", ty_);
                                        println!("destination: {:?}", dest_place);
                                        // println!("target: {:?}", Some(inline_block));
                                        // println!("unwind: {:?}", UnwindAction::Continue);
                                        // println!("call_source: {:?}", CallSource::Normal);
                                        // println!("fn_span: {:?}", SPANS[0]);

                                        

                                        // SECOND BLOCK!!
                                        let inline_block_2 = patch.new_block(BasicBlockData {
                                                    statements: vec![],
                                                    terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                                    is_cleanup: false,
                                                });

                                        // println!("PtrToPtr: {:?}", operand);

                                        let crate_num1 = CrateNum::new(0);
                                        let def_index1 = DefIndex::from_usize(7);
                                        let _def_id1 = DefId { krate: crate_num1, index: def_index1 };

                                        let _generic_args1: &rustc_middle::ty::List<GenericArg<'_>> = List::empty();

                                        // let tykind_ = ty::FnDef(_def_id, _generic_args);
                                        let ty_1 = Ty::new(tcx, ty::FnDef(_def_id1, _generic_args1));

                                        let const_1 = Const::Val(ConstValue::ZeroSized, ty_1);
                                        
                                        let const_operand1 = Box::new(ConstOperand { span: SPANS[0], user_ty: None, const_: const_1 });
                                        let operand_1 = Operand::Constant(const_operand1);
                                        println!("########### operand_: {:?}", operand_1);

                                        // let local = body.local_decls.push(LocalDecl::new(ty_, SPANS[0]));

                                        let dest_place1 = Place {local: (temp_2).into(), projection: List::empty()};

                                        let operand_input = Operand::Copy(dest_place);
                                        let spanned_operand = Spanned { span: SPANS[0], node: operand_input };

                                        // Call a function named just_print and pass the temp_1 as an argument
                                        let inline_terminator1 = TerminatorKind::Call {
                                            func: operand_1,
                                            args: vec![spanned_operand],
                                            destination: dest_place1,
                                            target: Some(inline_block_2),
                                            unwind: UnwindAction::Continue,
                                            call_source: CallSource::Normal,
                                            fn_span: SPANS[0],
                                        };

                                        // println!("ty_: {:?}", ty_);
                                        println!("destination: {:?}", dest_place1);
                                        // println!("target: {:?}", Some(inline_block));
                                        // println!("unwind: {:?}", UnwindAction::Continue);
                                        // println!("call_source: {:?}", CallSource::Normal);
                                        // println!("fn_span: {:?}", SPANS[0]);
                                        patch.patch_terminator(bb, inline_terminator);
                                        patch.patch_terminator(inline_block, inline_terminator1);

                                        
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
                                            // ty is a FnDef variant of the enum TyKind
                                            // FnDef holds two things DefId and GenericArgs

                                            
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