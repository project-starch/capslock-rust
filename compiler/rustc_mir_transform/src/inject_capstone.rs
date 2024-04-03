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
use rustc_span::{DUMMY_SP, Symbol};
static SPANS: [rustc_span::Span; 1] = [DUMMY_SP];

pub struct InjectCapstone;

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut patch = MirPatch::new(body);

        // Creating a fixed number of temporary variables of fixed type to be used by our injected functions
        let return_type_1 = Ty::new(tcx, ty::Bool);
        let temp_1 = body.local_decls.push(LocalDecl::new(return_type_1, SPANS[0]));
        let return_type_2 = Ty::new(tcx, ty::Bool);
        let temp_2 = body.local_decls.push(LocalDecl::new(return_type_2, SPANS[0]));

        let mut rapture_crate_number: u32 = 0;
        let mut crate_num_flag: bool = true;
        while crate_num_flag {
                rapture_crate_number += 1;
                crate_num_flag = Symbol::as_str(& tcx.crate_name(CrateNum::from_u32(rapture_crate_number))) != "rapture";
        }
        
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
            for (i, stmt) in data.statements.clone().iter().enumerate().rev() {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (_lhs, rhs)), .. } => {
                        match rhs {
                            Rvalue::Cast(cast_type, _operand, _) => {
                                match cast_type {
                                    CastKind::PointerCoercion(_coercion) => {
                                        println!("PointerCoercion: ");
                                    },
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
                                        let intermediary_terminator = TerminatorKind::Call {
                                            func: operand_,
                                            args: vec![],
                                            destination: dest_place,
                                            target: Some(intermediary_block),
                                            unwind: UnwindAction::Continue,
                                            call_source: CallSource::Normal,
                                            fn_span: SPANS[0],
                                        };

                                        // The current basic block's terminator is now replaced with the one we just created (which shifts the control flow to the intermediary block)
                                        patch.patch_terminator(bb, intermediary_terminator);

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
                                        let intermediary_terminator_2 = TerminatorKind::Call {
                                            func: operand_2,
                                            args: vec![spanned_operand],
                                            destination: dest_place_2,
                                            target: Some(intermediary_block_2),
                                            unwind: UnwindAction::Continue,
                                            call_source: CallSource::Normal,
                                            fn_span: SPANS[0],
                                        };

                                        // The intermediary block is now made to point to the second intermediary block by virtue of its new terminator
                                        patch.patch_terminator(intermediary_block, intermediary_terminator_2);

                                        //// DEBUG PRINTS
                                        // println!("ty_: {:?}", ty_);
                                        // println!("destination: {:?}", dest_place_2);
                                        // println!("target: {:?}", Some(intermediary_block));
                                        // println!("unwind: {:?}", UnwindAction::Continue);
                                        // println!("call_source: {:?}", CallSource::Normal);
                                        // println!("fn_span: {:?}", SPANS[0]);                                       
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
                        TerminatorKind::Call{func, ..} => {
                            println!("func: {:?}", func);
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