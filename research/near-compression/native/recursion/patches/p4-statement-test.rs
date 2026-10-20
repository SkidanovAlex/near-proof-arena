--- /dev/null	2026-10-01 18:21:35.412221787 +0000
+++ /dev/fd/63	2026-10-20 02:02:24.110631195 +0000
@@ -0,0 +1,56 @@
+/// **P4: the cached TAPE root is part of the statement V_d checks.**
+///
+/// A child proof whose AIR carries a cached main (the shape `pq-state-port`'s TAPE has) is
+/// verified by the NV circuit.  The statement digest must cover the cached commitment:
+///
+/// * the honest child's statement digest is `statement_digest(public_values ++ cached_limbs)`;
+/// * a statement that covers only the public values (the pre-P4 behaviour) must differ;
+/// * and a child whose cached root is swapped must produce a different statement.
+///
+/// The negative case is the one that matters: without the cached commitment in the statement,
+/// two children that differ only in their cached table have the *same* statement, so V_d would
+/// accept either.
+#[test]
+fn nv_stmt_covers_cached_root() {
+    use openvm_stark_backend::test_utils::PreprocessedAndCachedFixture;
+    let engine = Sha384CpuEngine::new(child_params_small());
+    let sels: Vec<bool> = (0..1usize << 5).map(|i| i % 3 == 0).collect();
+    let fx = PreprocessedAndCachedFixture::new(sels, engine.config().clone(), 1);
+    let (vk, proof) = fx.keygen_and_prove(&engine);
+    assert!(!vk.inner.per_air[0].params.width.cached_mains.is_empty(), "child has a cached main");
+    let cached = proof.trace_vdata[0].as_ref().unwrap().cached_commitments.clone();
+    assert_eq!(cached.len(), 1, "one cached commitment");
+
+    // the P4 statement: public values followed by the cached commitment's limbs
+    let mut with_cached: Vec<Vec<F>> = proof.public_values.clone();
+    with_cached.push(crate::nv::fmt::digest_limbs(cached[0]).to_vec());
+    let d_p4 = crate::sha384::config::statement_digest(&with_cached);
+    let d_pv_only = crate::sha384::config::statement_digest(&proof.public_values);
+    assert_ne!(d_p4, d_pv_only, "the cached root must change the statement digest");
+
+    // a child whose cached root differs gives a different P4 statement, same PV digests
+    let mut swapped = cached[0];
+    swapped[0] ^= 1;
+    let mut with_swapped: Vec<Vec<F>> = proof.public_values.clone();
+    with_swapped.push(crate::nv::fmt::digest_limbs(swapped).to_vec());
+    assert_ne!(
+        crate::sha384::config::statement_digest(&with_swapped),
+        d_p4,
+        "a swapped cached root must give a different statement"
+    );
+    assert_eq!(
+        crate::sha384::config::statement_digest(&proof.public_values),
+        d_pv_only,
+        "the public values alone are unchanged by the cached root"
+    );
+
+    // the circuit reproduces the P4 statement (its in-circuit SHA job must equal the host digest)
+    let circ = super::circuit::NvCircuit::new(vk.inner.params.k_whir(), 18, 1);
+    let (_, b) = circ.generate(&vk, &proof);
+    assert!(b.failures.is_empty(), "{:?}", b.failures);
+    assert_eq!(
+        b.statement, Some(d_p4),
+        "the NV program must expose exactly the P4 statement (public values + cached root)"
+    );
+    println!("NV_STMT cached root in statement: {d_p4:?}");
+}
