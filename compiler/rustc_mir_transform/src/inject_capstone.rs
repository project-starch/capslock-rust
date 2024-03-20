use crate::MirPass;
// use rustc_data_structures::fx::{FxIndexMap, IndexEntry, IndexOccupiedEntry};
// use rustc_index::bit_set::BitSet;
// use rustc_index::interval::SparseIntervalMatrix;
// use rustc_middle::mir::visit::{MutVisitor, PlaceContext, Visitor};
// use rustc_middle::mir::HasLocalDecls;
// use rustc_middle::mir::{dump_mir, PassWhere};
use rustc_middle::mir::{
    /*traversal,*/ Body, /*InlineAsmOperand, Local, LocalKind, Location, Operand, Place, Rvalue,*/
    Statement, StatementKind, TerminatorKind,
};
use rustc_middle::ty::TyCtxt;
// use rustc_mir_dataflow::impls::MaybeLiveLocals;
// use rustc_mir_dataflow::points::{/*save_as_intervals,*/ DenseLocationMap, PointIndex};
// use rustc_mir_dataflow::Analysis;
pub struct InjectCapstone;

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        
        println!("Running InjectCapstone on {:?}", body.source.def_id());
        
        // For reference, printing the contents of each basic block in the body of this function
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            println!("\nBasic Block: {:?}", bb);
            for (i, stmt) in data.statements.iter().enumerate() {
                match stmt {
                    Statement { kind: StatementKind::Assign(box (lhs, rhs)), .. } => {
                        println!("Statement {}: {:?} = {:?}", i, lhs, rhs);
                    },
                    Statement { kind: StatementKind::StorageLive(local), .. } => {
                        println!("Statement {}: StorageLive {:?}", i, local);
                    },
                    Statement { kind: StatementKind::StorageDead(local), .. } => {
                        println!("Statement {}: StorageDead {:?}", i, local);
                    },
                    _ => println!("Other non-matched statement {}: {:?}", i, stmt.kind),
                }
            }
            
            match &data.terminator {
                Some(x) => {
                    match x.kind {
                        TerminatorKind::Return => println!("Return: {:?}", x.kind),
                        TerminatorKind::Drop { place, target, .. } => {
                            println!("Drop: {:?}, {:?}", place, target)
                        },
                        TerminatorKind::Goto { target } => {
                            println!("Goto: {:?}", target)
                        },
                        _ => {},
                    }
                },
                _ => {}
            }
        }
    }
}
