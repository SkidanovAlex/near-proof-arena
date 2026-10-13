//! The native lookup walks of an accepted witness (`walkV3`, table 5): Rust twin of
//! `TrieEntriesV3.lean`'s `mainValuesOf` and of `allLookupQueries`
//! (`Rcpt/Candidates/NativeLookupQueryBounds.lean`), `nativeQueryWalks`
//! (`NativeLookupQueryList.lean`), `NativeQueueIds.resolve` (`Candidates/NativeQueueIds.lean`)
//! and `rankWalks` (`Rcpt/Candidates/WalkRanks.lean`).

use super::WalkR;
use super::native::{MainValues, Native};

/// `NativeLookupQuery`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Query {
    pub wid: u64,
    pub tau: u64,
    pub key: Vec<u8>,
}

/// The unique `MainValues` read from the main pre trie (`mainValuesOf`).
pub fn main_values(_n: &Native) -> Result<MainValues, String> {
    Err("v3::walks::main_values: not yet ported".into())
}

/// `allLookupQueries (appliedReceipts k w) m.pre v (steps.map pre) (resolve m.pre v pres)`.
pub fn queries(_n: &Native, _v: &MainValues) -> Result<Vec<Query>, String> {
    Err("v3::walks::queries: not yet ported".into())
}

/// `nativeQueryWalks pairs qs` (`pairs = (pre, post) :: steps.map (pre, post)`).
pub fn query_walks(_n: &Native, _qs: &[Query]) -> Result<Vec<WalkR>, String> {
    Err("v3::walks::query_walks: not yet ported".into())
}

/// `rankWalks [] ws`.
pub fn rank_walks(_ws: &[WalkR]) -> Vec<WalkR> {
    unimplemented!("v3::walks::rank_walks")
}
