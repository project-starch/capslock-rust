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
    /*traversal,*/ Body, /*InlineAsmOperand, Local, LocalKind, Location, Operand, Place, */CastKind, Rvalue,
    Statement, StatementKind, TerminatorKind, UnwindAction, BasicBlockData, 
};
use rustc_middle::ty::TyCtxt;
// use rustc_mir_dataflow::impls::MaybeLiveLocals;
// use rustc_mir_dataflow::points::{/*save_as_intervals,*/ DenseLocationMap, PointIndex};
// use rustc_mir_dataflow::Analysis;
pub struct InjectCapstone;

use rustc_span::DUMMY_SP;
static SPANS: [rustc_span::Span; 1] = [DUMMY_SP];

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut patch = MirPatch::new(body);
        
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
            
            match &data.terminator {
                Some(x) => {
                    match &x.kind {
                        TerminatorKind::Drop { .. } => {
                            println!("Drop: ")
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