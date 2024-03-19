use crate::MirPass;
use rustc_middle::ty::TyCtxt;
pub struct AssignCapstone;
use rustc_middle::mir::Body;

impl<'tcx> MirPass<'tcx> for AssignCapstone {

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        println!("running AssignCapstone on {:?}", tcx.def_path_str(body.source.def_id()));
        
        // tcx.def_path_str(body.source.def_id());
    }
}