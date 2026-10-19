// Overlay test for lane/pq-nv-preprocessed (FAITHFUL.md §Y): append to nv/faithful_tests.rs
// after applying openvm-recursion-prep.patch; NV must support preprocessed/cached children.
// ---------------------------------------------------------------------------------------
// §Y: NV verifying preprocessed / cached children (lane/pq-nv-preprocessed)
// ---------------------------------------------------------------------------------------

fn prep_engine() -> Sha384CpuEngine {
    // round 0 on Johnson (multi-commitment rule): the small params have no O-2 table
    Sha384CpuEngine::new(child_params_small())
}

/// DOF on NV traces verifying a preprocessed child (2 commitments), the cached fixture
/// (3 commitments) and a preprocessed + 2 cached child (4 commitments).
#[test]
fn nv_dof_prep_children() {
    use openvm_stark_backend::test_utils::{CachedFixture11, PreprocessedAndCachedFixture, PreprocessedFibFixture};
    let e = prep_engine();
    let sels: Vec<bool> = (0..1 << 5).map(|i| (i * 7 + 3) % 5 < 2).collect();
    let mut bad = vec![];
    let (vk, pf) = PreprocessedFibFixture::new(0, 1, sels.clone()).keygen_and_prove(&e);
    bad.extend(dof_case("prep-fib", &vk, &pf, None));
    let (vk, pf) = CachedFixture11::new(e.config().clone()).keygen_and_prove(&e);
    bad.extend(dof_case("cached11", &vk, &pf, None));
    let (vk, pf) = PreprocessedAndCachedFixture::new(sels, e.config().clone(), 2).keygen_and_prove(&e);
    bad.extend(dof_case("prep+2cached", &vk, &pf, None));
    assert!(bad.is_empty(), "unexpected degrees of freedom: {bad:#?}");
}

