use crate::MirPass;
// use rustc_data_structures::fx::{FxIndexMap, IndexEntry, IndexOccupiedEntry};
// use rustc_index::bit_set::BitSet;
// use rustc_index::interval::SparseIntervalMatrix;
// use rustc_middle::mir::visit::{MutVisitor, PlaceContext, Visitor};
// use rustc_middle::mir::HasLocalDecls;
// use rustc_middle::mir::{dump_mir, PassWhere};
use rustc_middle::mir::{
    /*traversal,*/ Body, /*InlineAsmOperand, Local, LocalKind, Location, Operand, Place, Rvalue,
    Statement, StatementKind,*/ TerminatorKind,
};
use rustc_middle::ty::TyCtxt;
// use rustc_mir_dataflow::impls::MaybeLiveLocals;
// use rustc_mir_dataflow::points::{/*save_as_intervals,*/ DenseLocationMap, PointIndex};
// use rustc_mir_dataflow::Analysis;
pub struct InjectCapstone;

impl<'tcx> MirPass<'tcx> for InjectCapstone {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        
        println!("running InjectCapstone on {:?}", body.source.def_id());
        
        // For reference, printing the contents of each basic block in the body of this function
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            println!("Basic Block: {:?}", bb);
            for (i, stmt) in data.statements.iter().enumerate() {
                println!("Statement {}: {:?}", i, stmt);
            }
            //println!("Terminator: {:?}", data.terminator().kind);
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

        // let def_id = body.source.def_id();
        // let mut allocations = Allocations::default();
        // trace!(func = ?tcx.def_path_str(def_id));

        // let borrowed = rustc_mir_dataflow::impls::borrowed_locals(body);

        // let live = MaybeLiveLocals
        //     .into_engine(tcx, body)
        //     .pass_name("MaybeLiveLocals-InjectCapstone")
        //     .iterate_to_fixpoint();
        // let points = DenseLocationMap::new(body);
        // let mut live = save_as_intervals(&points, body, live);

        // // In order to avoid having to collect data for every single pair of locals in the body, we
        // // do not allow doing more than one merge for places that are derived from the same local at
        // // once. To avoid missed opportunities, we instead iterate to a fixed point - we'll refer to
        // // each of these iterations as a "round."
        // //
        // // Reaching a fixed point could in theory take up to `min(l, s)` rounds - however, we do not
        // // expect to see MIR like that. To verify this, a test was run against `[rust-lang/regex]` -
        // // the average MIR body saw 1.32 full iterations of this loop. The most that was hit were 30
        // // for a single function. Only 80/2801 (2.9%) of functions saw at least 5.
        // //
        // // [rust-lang/regex]:
        // //     https://github.com/rust-lang/regex/tree/b5372864e2df6a2f5e543a556a62197f50ca3650
        // let mut round_count = 0;
        // loop {
        //     println!("Inject Capstone Round: {}", round_count);
        //     // PERF: Can we do something smarter than recalculating the candidates and liveness
        //     // results?
        //     let mut candidates = find_candidates(
        //         body,
        //         &borrowed,
        //         &mut allocations.candidates,
        //         &mut allocations.candidates_reverse,
        //     );
        //     trace!(?candidates);
        //     dest_prop_mir_dump(tcx, body, &points, &live, round_count);

        //     FilterInformation::filter_liveness(
        //         &mut candidates,
        //         &points,
        //         &live,
        //         &mut allocations.write_info,
        //         body,
        //     );

        //     // Because we only filter once per round, it is unsound to use a local for more than
        //     // one merge operation within a single round of optimizations. We store here which ones
        //     // we have already used.
        //     let mut merged_locals: BitSet<Local> = BitSet::new_empty(body.local_decls.len());

        //     // This is the set of merges we will apply this round. It is a subset of the candidates.
        //     let mut merges = FxIndexMap::default();

        //     for (src, candidates) in candidates.c.iter() {
        //         println!("Inject Capstone: {:?} => {:?}", src, candidates);
        //         if merged_locals.contains(*src) {
        //             continue;
        //         }
        //         let Some(dest) = candidates.iter().find(|dest| !merged_locals.contains(**dest))
        //         else {
        //             continue;
        //         };
        //         if !tcx.consider_optimizing(|| {
        //             format!("{} round {}", tcx.def_path_str(def_id), round_count)
        //         }) {
        //             break;
        //         }

        //         // Replace `src` by `dest` everywhere.
        //         merges.insert(*src, *dest);
        //         merged_locals.insert(*src);
        //         merged_locals.insert(*dest);

        //         // Update liveness information based on the merge we just performed.
        //         // Every location where `src` was live, `dest` will be live.
        //         live.union_rows(*src, *dest);
        //     }
        //     trace!(merging = ?merges);

        //     if merges.is_empty() {
        //         break;
        //     }
        //     round_count += 1;

        //     apply_merges(body, tcx, &merges, &merged_locals);
        // }
        // println!("Inject Capstone Rounds: {}", round_count);
        // trace!(round_count);
    }
}

// #[derive(Default)]
// struct Allocations {
//     candidates: FxIndexMap<Local, Vec<Local>>,
//     candidates_reverse: FxIndexMap<Local, Vec<Local>>,
//     write_info: WriteInfo,
//     // PERF: Do this for `MaybeLiveLocals` allocations too.
// }

// #[derive(Debug)]
// struct Candidates<'alloc> {
//     /// The set of candidates we are considering in this optimization.
//     ///
//     /// We will always merge the key into at most one of its values.
//     ///
//     /// Whether a place ends up in the key or the value does not correspond to whether it appears as
//     /// the lhs or rhs of any assignment. As a matter of fact, the places in here might never appear
//     /// in an assignment at all. This happens because if we see an assignment like this:
//     ///
//     /// ```ignore (syntax-highlighting-only)
//     /// _1.0 = _2.0
//     /// ```
//     ///
//     /// We will still report that we would like to merge `_1` and `_2` in an attempt to allow us to
//     /// remove that assignment.
//     c: &'alloc mut FxIndexMap<Local, Vec<Local>>,
//     /// A reverse index of the `c` set; if the `c` set contains `a => Place { local: b, proj }`,
//     /// then this contains `b => a`.
//     // PERF: Possibly these should be `SmallVec`s?
//     reverse: &'alloc mut FxIndexMap<Local, Vec<Local>>,
// }

// //////////////////////////////////////////////////////////
// // Merging
// //
// // Applies the actual optimization

// fn apply_merges<'tcx>(
//     body: &mut Body<'tcx>,
//     tcx: TyCtxt<'tcx>,
//     merges: &FxIndexMap<Local, Local>,
//     merged_locals: &BitSet<Local>,
// ) {
//     let mut merger = Merger { tcx, merges, merged_locals };
//     merger.visit_body_preserves_cfg(body);
// }

// struct Merger<'a, 'tcx> {
//     tcx: TyCtxt<'tcx>,
//     merges: &'a FxIndexMap<Local, Local>,
//     merged_locals: &'a BitSet<Local>,
// }

// impl<'a, 'tcx> MutVisitor<'tcx> for Merger<'a, 'tcx> {
//     fn tcx(&self) -> TyCtxt<'tcx> {
//         self.tcx
//     }

//     fn visit_local(&mut self, local: &mut Local, _: PlaceContext, _location: Location) {
//         if let Some(dest) = self.merges.get(local) {
//             *local = *dest;
//         }
//     }

//     fn visit_statement(&mut self, statement: &mut Statement<'tcx>, location: Location) {
//         match &statement.kind {
//             // FIXME: Don't delete storage statements, but "merge" the storage ranges instead.
//             StatementKind::StorageDead(local) | StatementKind::StorageLive(local)
//                 if self.merged_locals.contains(*local) =>
//             {
//                 statement.make_nop();
//                 return;
//             }
//             _ => (),
//         };
//         self.super_statement(statement, location);
//         match &statement.kind {
//             StatementKind::Assign(box (dest, rvalue)) => {
//                 match rvalue {
//                     Rvalue::CopyForDeref(place)
//                     | Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
//                         // These might've been turned into self-assignments by the replacement
//                         // (this includes the original statement we wanted to eliminate).
//                         if dest == place {
//                             debug!("{:?} turned into self-assignment, deleting", location);
//                             statement.make_nop();
//                         }
//                     }
//                     _ => {}
//                 }
//             }

//             _ => {}
//         }
//     }
// }
// //////////////////////////////////////////////////////////
// // Liveness filtering
// //
// // This section enforces bullet point 2

// struct FilterInformation<'a, 'body, 'alloc, 'tcx> {
//     body: &'body Body<'tcx>,
//     points: &'a DenseLocationMap,
//     live: &'a SparseIntervalMatrix<Local, PointIndex>,
//     candidates: &'a mut Candidates<'alloc>,
//     write_info: &'alloc mut WriteInfo,
//     at: Location,
// }

// // We first implement some utility functions which we will expose removing candidates according to
// // different needs. Throughout the liveness filtering, the `candidates` are only ever accessed
// // through these methods, and not directly.
// impl<'alloc> Candidates<'alloc> {
//     /// Just `Vec::retain`, but the condition is inverted and we add debugging output
//     fn vec_filter_candidates(
//         src: Local,
//         v: &mut Vec<Local>,
//         mut f: impl FnMut(Local) -> CandidateFilter,
//         at: Location,
//     ) {
//         v.retain(|dest| {
//             let remove = f(*dest);
//             if remove == CandidateFilter::Remove {
//                 trace!("eliminating {:?} => {:?} due to conflict at {:?}", src, dest, at);
//             }
//             remove == CandidateFilter::Keep
//         });
//     }

//     /// `vec_filter_candidates` but for an `Entry`
//     fn entry_filter_candidates(
//         mut entry: IndexOccupiedEntry<'_, Local, Vec<Local>>,
//         p: Local,
//         f: impl FnMut(Local) -> CandidateFilter,
//         at: Location,
//     ) {
//         let candidates = entry.get_mut();
//         Self::vec_filter_candidates(p, candidates, f, at);
//         if candidates.len() == 0 {
//             // FIXME(#120456) - is `swap_remove` correct?
//             entry.swap_remove();
//         }
//     }

//     /// For all candidates `(p, q)` or `(q, p)` removes the candidate if `f(q)` says to do so
//     fn filter_candidates_by(
//         &mut self,
//         p: Local,
//         mut f: impl FnMut(Local) -> CandidateFilter,
//         at: Location,
//     ) {
//         // Cover the cases where `p` appears as a `src`
//         if let IndexEntry::Occupied(entry) = self.c.entry(p) {
//             Self::entry_filter_candidates(entry, p, &mut f, at);
//         }
//         // And the cases where `p` appears as a `dest`
//         let Some(srcs) = self.reverse.get_mut(&p) else {
//             return;
//         };
//         // We use `retain` here to remove the elements from the reverse set if we've removed the
//         // matching candidate in the forward set.
//         srcs.retain(|src| {
//             if f(*src) == CandidateFilter::Keep {
//                 return true;
//             }
//             let IndexEntry::Occupied(entry) = self.c.entry(*src) else {
//                 return false;
//             };
//             Self::entry_filter_candidates(
//                 entry,
//                 *src,
//                 |dest| {
//                     if dest == p { CandidateFilter::Remove } else { CandidateFilter::Keep }
//                 },
//                 at,
//             );
//             false
//         });
//     }
// }

// #[derive(Copy, Clone, PartialEq, Eq)]
// enum CandidateFilter {
//     Keep,
//     Remove,
// }

// impl<'a, 'body, 'alloc, 'tcx> FilterInformation<'a, 'body, 'alloc, 'tcx> {
//     /// Filters the set of candidates to remove those that conflict.
//     ///
//     /// The steps we take are exactly those that are outlined at the top of the file. For each
//     /// statement/terminator, we collect the set of locals that are written to in that
//     /// statement/terminator, and then we remove all pairs of candidates that contain one such local
//     /// and another one that is live.
//     ///
//     /// We need to be careful about the ordering of operations within each statement/terminator
//     /// here. Many statements might write and read from more than one place, and we need to consider
//     /// them all. The strategy for doing this is as follows: We first gather all the places that are
//     /// written to within the statement/terminator via `WriteInfo`. Then, we use the liveness
//     /// analysis from *before* the statement/terminator (in the control flow sense) to eliminate
//     /// candidates - this is because we want to conservatively treat a pair of locals that is both
//     /// read and written in the statement/terminator to be conflicting, and the liveness analysis
//     /// before the statement/terminator will correctly report locals that are read in the
//     /// statement/terminator to be live. We are additionally conservative by treating all written to
//     /// locals as also being read from.
//     fn filter_liveness<'b>(
//         candidates: &mut Candidates<'alloc>,
//         points: &DenseLocationMap,
//         live: &SparseIntervalMatrix<Local, PointIndex>,
//         write_info_alloc: &'alloc mut WriteInfo,
//         body: &'b Body<'tcx>,
//     ) {
//         let mut this = FilterInformation {
//             body,
//             points,
//             live,
//             candidates,
//             // We don't actually store anything at this scope, we just keep things here to be able
//             // to reuse the allocation.
//             write_info: write_info_alloc,
//             // Doesn't matter what we put here, will be overwritten before being used
//             at: Location::START,
//         };
//         this.internal_filter_liveness();
//     }

//     fn internal_filter_liveness(&mut self) {
//         for (block, data) in traversal::preorder(self.body) {
//             self.at = Location { block, statement_index: data.statements.len() };
//             self.write_info.for_terminator(&data.terminator().kind);
//             self.apply_conflicts();

//             for (i, statement) in data.statements.iter().enumerate().rev() {
//                 self.at = Location { block, statement_index: i };
//                 self.write_info.for_statement(&statement.kind, self.body);
//                 self.apply_conflicts();
//             }
//         }
//     }

//     fn apply_conflicts(&mut self) {
//         let writes = &self.write_info.writes;
//         for p in writes {
//             let other_skip = self.write_info.skip_pair.and_then(|(a, b)| {
//                 if a == *p {
//                     Some(b)
//                 } else if b == *p {
//                     Some(a)
//                 } else {
//                     None
//                 }
//             });
//             let at = self.points.point_from_location(self.at);
//             self.candidates.filter_candidates_by(
//                 *p,
//                 |q| {
//                     if Some(q) == other_skip {
//                         return CandidateFilter::Keep;
//                     }
//                     // It is possible that a local may be live for less than the
//                     // duration of a statement This happens in the case of function
//                     // calls or inline asm. Because of this, we also mark locals as
//                     // conflicting when both of them are written to in the same
//                     // statement.
//                     if self.live.contains(q, at) || writes.contains(&q) {
//                         CandidateFilter::Remove
//                     } else {
//                         CandidateFilter::Keep
//                     }
//                 },
//                 self.at,
//             );
//         }
//     }
// }

// /// Describes where a statement/terminator writes to
// #[derive(Default, Debug)]
// struct WriteInfo {
//     writes: Vec<Local>,
//     /// If this pair of locals is a candidate pair, completely skip processing it during this
//     /// statement. All other candidates are unaffected.
//     skip_pair: Option<(Local, Local)>,
// }

// impl WriteInfo {
//     fn for_statement<'tcx>(&mut self, statement: &StatementKind<'tcx>, body: &Body<'tcx>) {
//         self.reset();
//         match statement {
//             StatementKind::Assign(box (lhs, rhs)) => {
//                 self.add_place(*lhs);
//                 match rhs {
//                     Rvalue::Use(op) => {
//                         self.add_operand(op);
//                         self.consider_skipping_for_assign_use(*lhs, op, body);
//                     }
//                     Rvalue::Repeat(op, _) => {
//                         self.add_operand(op);
//                     }
//                     Rvalue::Cast(_, op, _)
//                     | Rvalue::UnaryOp(_, op)
//                     | Rvalue::ShallowInitBox(op, _) => {
//                         self.add_operand(op);
//                     }
//                     Rvalue::BinaryOp(_, ops) | Rvalue::CheckedBinaryOp(_, ops) => {
//                         for op in [&ops.0, &ops.1] {
//                             self.add_operand(op);
//                         }
//                     }
//                     Rvalue::Aggregate(_, ops) => {
//                         for op in ops {
//                             self.add_operand(op);
//                         }
//                     }
//                     Rvalue::ThreadLocalRef(_)
//                     | Rvalue::NullaryOp(_, _)
//                     | Rvalue::Ref(_, _, _)
//                     | Rvalue::AddressOf(_, _)
//                     | Rvalue::Len(_)
//                     | Rvalue::Discriminant(_)
//                     | Rvalue::CopyForDeref(_) => (),
//                 }
//             }
//             // Retags are technically also reads, but reporting them as a write suffices
//             StatementKind::SetDiscriminant { place, .. }
//             | StatementKind::Deinit(place)
//             | StatementKind::Retag(_, place) => {
//                 self.add_place(**place);
//             }
//             StatementKind::Intrinsic(_)
//             | StatementKind::ConstEvalCounter
//             | StatementKind::Nop
//             | StatementKind::Coverage(_)
//             | StatementKind::StorageLive(_)
//             | StatementKind::StorageDead(_)
//             | StatementKind::PlaceMention(_) => (),
//             StatementKind::FakeRead(_) | StatementKind::AscribeUserType(_, _) => {
//                 bug!("{:?} not found in this MIR phase", statement)
//             }
//         }
//     }

//     fn consider_skipping_for_assign_use<'tcx>(
//         &mut self,
//         lhs: Place<'tcx>,
//         rhs: &Operand<'tcx>,
//         body: &Body<'tcx>,
//     ) {
//         let Some(rhs) = rhs.place() else { return };
//         if let Some(pair) = places_to_candidate_pair(lhs, rhs, body) {
//             self.skip_pair = Some(pair);
//         }
//     }

//     fn for_terminator<'tcx>(&mut self, terminator: &TerminatorKind<'tcx>) {
//         self.reset();
//         match terminator {
//             TerminatorKind::SwitchInt { discr: op, .. }
//             | TerminatorKind::Assert { cond: op, .. } => {
//                 self.add_operand(op);
//             }
//             TerminatorKind::Call { destination, func, args, .. } => {
//                 self.add_place(*destination);
//                 self.add_operand(func);
//                 for arg in args {
//                     self.add_operand(&arg.node);
//                 }
//             }
//             TerminatorKind::InlineAsm { operands, .. } => {
//                 for asm_operand in operands {
//                     match asm_operand {
//                         InlineAsmOperand::In { value, .. } => {
//                             self.add_operand(value);
//                         }
//                         InlineAsmOperand::Out { place, .. } => {
//                             if let Some(place) = place {
//                                 self.add_place(*place);
//                             }
//                         }
//                         // Note that the `late` field in `InOut` is about whether the registers used
//                         // for these things overlap, and is of absolutely no interest to us.
//                         InlineAsmOperand::InOut { in_value, out_place, .. } => {
//                             if let Some(place) = out_place {
//                                 self.add_place(*place);
//                             }
//                             self.add_operand(in_value);
//                         }
//                         InlineAsmOperand::Const { .. }
//                         | InlineAsmOperand::SymFn { .. }
//                         | InlineAsmOperand::SymStatic { .. }
//                         | InlineAsmOperand::Label { .. } => {}
//                     }
//                 }
//             }
//             TerminatorKind::Goto { .. }
//             | TerminatorKind::UnwindResume
//             | TerminatorKind::UnwindTerminate(_)
//             | TerminatorKind::Return
//             | TerminatorKind::Unreachable { .. } => (),
//             TerminatorKind::Drop { .. } => {
//                 // `Drop`s create a `&mut` and so are not considered
//             }
//             TerminatorKind::Yield { .. }
//             | TerminatorKind::CoroutineDrop
//             | TerminatorKind::FalseEdge { .. }
//             | TerminatorKind::FalseUnwind { .. } => {
//                 bug!("{:?} not found in this MIR phase", terminator)
//             }
//         }
//     }

//     fn add_place(&mut self, place: Place<'_>) {
//         self.writes.push(place.local);
//     }

//     fn add_operand<'tcx>(&mut self, op: &Operand<'tcx>) {
//         match op {
//             // FIXME(JakobDegen): In a previous version, the `Move` case was incorrectly treated as
//             // being a read only. This was unsound, however we cannot add a regression test because
//             // it is not possible to set this off with current MIR. Once we have that ability, a
//             // regression test should be added.
//             Operand::Move(p) => self.add_place(*p),
//             Operand::Copy(_) | Operand::Constant(_) => (),
//         }
//     }

//     fn reset(&mut self) {
//         self.writes.clear();
//         self.skip_pair = None;
//     }
// }

// /////////////////////////////////////////////////////
// // Candidate accumulation

// /// If the pair of places is being considered for merging, returns the candidate which would be
// /// merged in order to accomplish this.
// ///
// /// The contract here is in one direction - there is a guarantee that merging the locals that are
// /// outputted by this function would result in an assignment between the inputs becoming a
// /// self-assignment. However, there is no guarantee that the returned pair is actually suitable for
// /// merging - candidate collection must still check this independently.
// ///
// /// This output is unique for each unordered pair of input places.
// fn places_to_candidate_pair<'tcx>(
//     a: Place<'tcx>,
//     b: Place<'tcx>,
//     body: &Body<'tcx>,
// ) -> Option<(Local, Local)> {
//     let (mut a, mut b) = if a.projection.len() == 0 && b.projection.len() == 0 {
//         (a.local, b.local)
//     } else {
//         return None;
//     };

//     // By sorting, we make sure we're input order independent
//     if a > b {
//         std::mem::swap(&mut a, &mut b);
//     }

//     // We could now return `(a, b)`, but then we miss some candidates in the case where `a` can't be
//     // used as a `src`.
//     if is_local_required(a, body) {
//         std::mem::swap(&mut a, &mut b);
//     }
//     // We could check `is_local_required` again here, but there's no need - after all, we make no
//     // promise that the candidate pair is actually valid
//     Some((a, b))
// }

// /// Collects the candidates for merging
// ///
// /// This is responsible for enforcing the first and third bullet point.
// fn find_candidates<'alloc, 'tcx>(
//     body: &Body<'tcx>,
//     borrowed: &BitSet<Local>,
//     candidates: &'alloc mut FxIndexMap<Local, Vec<Local>>,
//     candidates_reverse: &'alloc mut FxIndexMap<Local, Vec<Local>>,
// ) -> Candidates<'alloc> {
//     candidates.clear();
//     candidates_reverse.clear();
//     let mut visitor = FindAssignments { body, candidates, borrowed };
//     visitor.visit_body(body);
//     // Deduplicate candidates
//     for (_, cands) in candidates.iter_mut() {
//         cands.sort();
//         cands.dedup();
//     }
//     // Generate the reverse map
//     for (src, cands) in candidates.iter() {
//         for dest in cands.iter().copied() {
//             candidates_reverse.entry(dest).or_default().push(*src);
//         }
//     }
//     Candidates { c: candidates, reverse: candidates_reverse }
// }

// struct FindAssignments<'a, 'alloc, 'tcx> {
//     body: &'a Body<'tcx>,
//     candidates: &'alloc mut FxIndexMap<Local, Vec<Local>>,
//     borrowed: &'a BitSet<Local>,
// }

// impl<'tcx> Visitor<'tcx> for FindAssignments<'_, '_, 'tcx> {
//     fn visit_statement(&mut self, statement: &Statement<'tcx>, _: Location) {
//         if let StatementKind::Assign(box (
//             lhs,
//             Rvalue::CopyForDeref(rhs) | Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs)),
//         )) = &statement.kind
//         {
//             let Some((src, dest)) = places_to_candidate_pair(*lhs, *rhs, self.body) else {
//                 return;
//             };

//             // As described at the top of the file, we do not go near things that have
//             // their address taken.
//             if self.borrowed.contains(src) || self.borrowed.contains(dest) {
//                 return;
//             }

//             // As described at the top of this file, we do not touch locals which have
//             // different types.
//             let src_ty = self.body.local_decls()[src].ty;
//             let dest_ty = self.body.local_decls()[dest].ty;
//             if src_ty != dest_ty {
//                 // FIXME(#112651): This can be removed afterwards. Also update the module description.
//                 trace!("skipped `{src:?} = {dest:?}` due to subtyping: {src_ty} != {dest_ty}");
//                 return;
//             }

//             // Also, we need to make sure that MIR actually allows the `src` to be removed
//             if is_local_required(src, self.body) {
//                 return;
//             }

//             // We may insert duplicates here, but that's fine
//             self.candidates.entry(src).or_default().push(dest);
//         }
//     }
// }

// /// Some locals are part of the function's interface and can not be removed.
// ///
// /// Note that these locals *can* still be merged with non-required locals by removing that other
// /// local.
// fn is_local_required(local: Local, body: &Body<'_>) -> bool {
//     match body.local_kind(local) {
//         LocalKind::Arg | LocalKind::ReturnPointer => true,
//         LocalKind::Temp => false,
//     }
// }

/////////////////////////////////////////////////////////
// MIR Dump

// fn dest_prop_mir_dump<'body, 'tcx>(
//     tcx: TyCtxt<'tcx>,
//     body: &'body Body<'tcx>,
//     points: &DenseLocationMap,
//     live: &SparseIntervalMatrix<Local, PointIndex>,
//     round: usize,
// ) {
//     let locals_live_at = |location| {
//         let location = points.point_from_location(location);
//         live.rows().filter(|&r| live.contains(r, location)).collect::<Vec<_>>()
//     };
//     dump_mir(tcx, false, "DestinationPropagation-dataflow", &round, body, |pass_where, w| {
//         if let PassWhere::BeforeLocation(loc) = pass_where {
//             writeln!(w, "        // live: {:?}", locals_live_at(loc))?;
//         }

//         Ok(())
//     });
// }
