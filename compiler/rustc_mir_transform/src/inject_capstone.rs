use crate::MirPass;
use rustc_ast::InlineAsmOptions;
use rustc_ast::InlineAsmTemplatePiece;
// use rustc_index::Idx;
// use rustc_data_structures::fx::{FxIndexMap, IndexEntry, IndexOccupiedEntry};
// use rustc_index::bit_set::BitSet;
// use rustc_index::interval::SparseIntervalMatrix;
// use rustc_middle::mir::visit::MutVisitor;
use rustc_middle::mir::patch::MirPatch;
// use rustc_middle::mir::HasLocalDecls;
// use rustc_middle::mir::{dump_mir, PassWhere};
use rustc_middle::mir::{
    /*traversal,*/ Body, /*Local, */ /*InlineAsmOperand, LocalKind, Location, Operand, Place, */CastKind, Rvalue,
    Statement, StatementKind, TerminatorKind, UnwindAction, BasicBlockData, 
};
use rustc_middle::ty::TyCtxt;
// use rustc_data_structures::fx::FxHashMap;
// use rustc_mir_dataflow::impls::MaybeLiveLocals;
// use rustc_mir_dataflow::points::{/*save_as_intervals,*/ DenseLocationMap, PointIndex};
// use rustc_mir_dataflow::Analysis;

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


        // Second, downward, loop to find the first uses of those pointers from Candidates
        for (_bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (_i, stmt) in data.statements.iter_mut().enumerate() {
                match stmt {
                    Statement {kind: StatementKind::Assign(box (_lhs, rhs)), .. } => {
                        // match lhs {
                        //     // Match the lvalue on LHS for all root allocations
                        //         // Upon match,
                        //             // Inject inline asm here to GENerate the CAPabilities for those roots
                        //             // Store the capabilities in memory (take inspiration from library solution)
                        //             // Store the capabilities (or their addresses) into the AllocationCapabilities struct
                        //     _ => todo!(),
                        // };
                        match rhs {
                            // Match the rvalue on the RHS based on what we want
                                // Upon match, check if the value being assigned is in the Candidates struct
                                    // If so, inject inline asm to load the capability from memory
                                    // Its address can be found using the two hash maps
                                    // Use the capability to perform the operation
                            _ => (),
                        }
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
                            Rvalue::Cast(cast_type, operand, _) => {
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
                                        
                                        let inline_block = patch.new_block(BasicBlockData {
                                            statements: new_stmts,
                                            terminator: Some(data.terminator.as_ref().unwrap().clone()),
                                            is_cleanup: false,
                                        });

                                        let inline_terminator = TerminatorKind::InlineAsm {
                                            template: tcx.arena.alloc_from_iter([InlineAsmTemplatePiece::String(".insn r 0x5b, 0x1, 0x43, x0, t0, x0".to_string())]),
                                            operands: vec![],
                                            options: InlineAsmOptions::empty(),
                                            line_spans: &SPANS,
                                            targets: vec![inline_block],
                                            unwind: UnwindAction::Continue,
                                        };

                                        patch.patch_terminator(bb, inline_terminator);

                                        println!("PtrToPtr: {:?}", operand);
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
        }
        
        patch.apply(body);
    }
}