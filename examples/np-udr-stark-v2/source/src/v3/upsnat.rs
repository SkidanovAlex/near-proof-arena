//! Honest native `upsV3` instances (table 7) of the scheduler upserts: Rust twin of
//! `TrieEntriesV3.lean`'s `honestInst` (the construction inside
//! `Rcpt/Candidates/NativeReaderOrigin.lean` `scheduler_instance_origin_inputs`, with
//! `baseI := default`, `base := default`), `TrieUpsNative.upsRanked`
//! (`physicalPrefixUps`), the window request keys `PhysicalWindowRequests.keys`
//! (`Candidates/PhysicalWindowRequests.lean`) and `TrieUpsNative.useReq`.

use super::WalkR;
use super::forest::UseRequests;
use super::native::UpsertW;
use super::ups::UpsInst;

/// `honestInsts us` (one instance per scheduler upsert, `tau` = its index).
pub fn honest_insts(_us: &[UpsertW]) -> Result<Vec<UpsInst>, String> {
    Err("v3::upsnat::honest_insts: not yet ported".into())
}

/// `upsRanked ws insts = physicalPrefixUps (ws.flatMap steps) insts`.
pub fn ups_ranked(_ws: &[WalkR], _insts: &[UpsInst]) -> Vec<UpsInst> {
    unimplemented!("v3::upsnat::ups_ranked")
}

/// `PhysicalWindowRequests.keys (upsTraceAligned js) T_UPS`.
pub fn window_keys(_js: &[UpsInst]) -> Vec<Vec<u64>> {
    unimplemented!("v3::upsnat::window_keys")
}

/// `useReq ws insts W` (unranked walks and instances).
pub fn use_req(_ws: &[WalkR], _insts: &[UpsInst], _w: Vec<Vec<u64>>) -> UseRequests {
    unimplemented!("v3::upsnat::use_req")
}
