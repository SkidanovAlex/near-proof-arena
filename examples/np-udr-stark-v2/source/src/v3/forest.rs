//! Honest native entries of the trie tables `nodeV3` (2), `valV3` (4), `headV3` (3) and
//! `uniqV3` (6): Rust twin of `Assembly/TrieNative.lean` (`nodes`, `vals`, `heads`) and
//! `Assembly/TrieUniqDup.lean` (`uniqNative`), on the native objects ([`Native`]).
//!
//! * `nodes m steps oldPost writes q = assignList q 0 (records (forestOldInputs
//!   (nativeReplayForest m steps oldPost writes)) (ChainMetadata.assign (chain m steps) 0
//!   (seedNodes m steps)))`;
//! * `vals m steps = ChainMetadata.assignValues (chain m steps) (seedVals m steps)`;
//! * `heads m steps oldPost writes keys = assignHeadUses keys (forestWalkHeads 0 0
//!   ((nativeReplayForest …).map (pre, post)))`;
//! * `uniqNative m steps = uniqBlocks (occsOf m steps)`.

use super::native::Native;
use super::node::NodeS3;
use super::{HeadE, UEnt, ValE};

/// `UseRequests` (`Rcpt/Candidates/NodeUsage.lean`): EDGE / BMAP / UPB-window request keys.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Deserialize, serde::Serialize)]
pub struct UseRequests {
    pub edges: Vec<Vec<u64>>,
    pub bmaps: Vec<Vec<u64>>,
    pub windows: Vec<Vec<u64>>,
}

/// `TrieNative.nodes m steps oldPost writes q`.
pub fn nodes(_n: &Native, _q: &UseRequests) -> Result<Vec<NodeS3>, String> {
    Err("v3::forest::nodes: not yet ported".into())
}

/// `TrieNative.vals m steps`.
pub fn vals(_n: &Native) -> Result<Vec<ValE>, String> {
    Err("v3::forest::vals: not yet ported".into())
}

/// `TrieNative.heads m steps oldPost writes keys`.
pub fn heads(_n: &Native, _keys: &[Vec<u64>]) -> Result<Vec<HeadE>, String> {
    Err("v3::forest::heads: not yet ported".into())
}

/// `TrieUniqDup.uniqNative m steps`.
pub fn uniq(_n: &Native) -> Result<Vec<UEnt>, String> {
    Err("v3::forest::uniq: not yet ported".into())
}
