//! x15-domain WHIR prototype driver (research only).
//!
//! Built twice by `setup_x15_crate.sh`:
//!   * `x15-proto`      against the patched backend ($NEARPROOF_PQ_DEPS/stark-backend), feature `x15`;
//!   * `x15-proto-base` against the unmodified pinned backend (pq-native), no feature,
//!     only for the byte-identity check (`ident`).
//! Config = the native SHA-384 / Ext12 (X^12 - 31) configuration, included verbatim.
use std::sync::Arc;
use openvm_stark_backend::{StarkEngine,SystemParams,AirRef,PartitionedBaseAir,prover::{CpuColMajorBackend,AirProvingContext,ProvingContext,ColMajorMatrix},
    test_utils::{TestFixture,test_system_params_small,FibFixture,InteractionsFixture11,PreprocessedFibFixture,CachedFixture11,MixtureFixture}};
use p3_air::{Air,AirBuilder,BaseAir,BaseAirWithPublicValues};
use p3_matrix::Matrix;
use p3_field::PrimeCharacteristicRing;

mod config {
    use super::*;
    include!(env!("NEARPROOF_SHA384_CONFIG_RS"));
    type Sc = SC;
    type Eng = Engine;
    type Fb = F;
    #[allow(dead_code)]
    fn keep() { let _ = transcript_vectors; }
    include!("driver.rs");
}

fn main() { config::run() }
