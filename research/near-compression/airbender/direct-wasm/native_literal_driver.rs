// Appended to the generated literal AIR adapter. Diagnostic parameters only.
struct PublishedChild {
    pvs: crate::bus::PublicValuesBus,
    prehash: crate::bus::PreHashBus,
}
impl<F> BaseAir<F> for PublishedChild { fn width(&self)->usize {8} }
impl<F> PartitionedBaseAir<F> for PublishedChild {}
impl<F> BaseAirWithPublicValues<F> for PublishedChild {
    fn num_public_values(&self)->usize {4891}
}
impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for PublishedChild {
    fn eval(&self,builder:&mut AB) {
        let public=builder.public_values().to_vec();
        let first=builder.is_first_row();
        let main=builder.main();
        let local=main.row_slice(0).unwrap();
        for (i,value) in public.into_iter().enumerate() {
            self.pvs.receive(builder,AB::Expr::ZERO,crate::bus::PublicValuesBusMessage {
                air_idx:AB::Expr::ZERO,pv_idx:AB::Expr::from_usize(i),value:value.into(),
            },first.clone());
        }
        self.prehash.receive(builder,AB::Expr::ZERO,crate::bus::PreHashMessage {
            vk_pre_hash: std::array::from_fn(|i|local[i]),
        },first.clone());
    }
}

#[test]
fn nearproof_literal_slice_recursion() {
    use openvm_stark_backend::codec::{Encode,Decode};
    use openvm_stark_backend::proof::Proof;
    let out=std::env::var("NEARPROOF_LITERAL_OUT").unwrap();
    let mut params=test_system_params_small(2,16,3);
    params.max_constraint_degree=8;
    // Make the native multiplicity constraint implied by the recursive shape bound.
    params.logup.max_interaction_count=1 << 20;
    let child=BabyBearPoseidon2CpuEngine::<DuplexSponge>::new(params);
    let mut parent_params=test_system_params_small(2,16,3);
    parent_params.max_constraint_degree=MAX_CONSTRAINT_DEGREE;
    let parent=BabyBearPoseidon2CpuEngine::<DuplexSponge>::new(parent_params);
    let fx=LiteralFixture;
    let (child_pk,child_vk)=fx.keygen(&child);
    let circuit=VerifierSubCircuit::<1>::new_with_options(Arc::new(child_vk.clone()),
        VerifierConfig {continuations_enabled:true,..Default::default()});
    let mut airs=circuit.airs();
    let published_index=airs.len();
    airs.push(Arc::new(PublishedChild {pvs:circuit.bus_inventory().public_values_bus,
        prehash:circuit.bus_inventory().pre_hash_bus}));
    let (parent_pk,parent_vk)=parent.keygen(&airs);
    let expected:Vec<openvm_stark_sdk::config::baby_bear_poseidon2::F>=
        std::fs::read(format!("{out}/public.bin")).unwrap().chunks_exact(4)
        .map(|x|openvm_stark_sdk::config::baby_bear_poseidon2::F::from_u32(u32::from_le_bytes(x.try_into().unwrap()))).collect();
    assert_eq!(expected.len(),4891);
    if std::env::var_os("NEARPROOF_LITERAL_REPLAY").is_some() {
        let bytes=std::fs::read(format!("{out}/parent.proof")).unwrap();
        let mut cursor=std::io::Cursor::new(&bytes);
        let outer=Proof::<BabyBearPoseidon2Config>::decode(&mut cursor).unwrap();
        assert_eq!(cursor.position() as usize,bytes.len());
        assert_eq!(outer.public_values[published_index],expected);
        parent.verify(&parent_vk,&outer).unwrap();
        println!("NEARPROOF_LITERAL_REPLAY_PASS");
        return;
    }
    let proof=fx.prove(&child,&child_pk);
    child.verify(&child_vk,&proof).unwrap();
    assert_eq!(proof.public_values[0],expected);
    let mut child_bytes=Vec::new(); proof.encode(&mut child_bytes).unwrap();
    std::fs::write(format!("{out}/child.proof"),&child_bytes).unwrap();
    println!("NEARPROOF_LITERAL_CHILD_BYTES={}",child_bytes.len());
    let ctxs=circuit.generate_proving_ctxs_base(&child_vk,
        CachedTraceCtx::PcsData(circuit.commit_child_vk(&parent,&child_vk)),
        &[proof],&(),default_duplex_sponge_recorder());
    let binding=AirProvingContext::simple(ColMajorMatrix::from_row_major(
        &RowMajorMatrix::new(child_vk.pre_hash.repeat(4),8)),expected.clone());
    let extra=parent.device().transport_proving_ctx_to_device(
        &ProvingContext::new(vec![(published_index,binding)]));
    let mut contexts:Vec<_>=ctxs.into_iter().enumerate().collect();
    contexts.extend(extra.per_trace);
    let ctx=ProvingContext::new(contexts);
    parent.debug(&airs,&ctx);
    let dpk=parent.device().transport_pk_to_device(&parent_pk);
    let outer=parent.prove(&dpk,ctx).unwrap();
    parent.verify(&parent_vk,&outer).unwrap();
    assert_eq!(outer.public_values[published_index],expected);
    let mut bytes=Vec::new();outer.encode(&mut bytes).unwrap();
    std::fs::write(format!("{out}/parent.proof"),&bytes).unwrap();
    for i in [43,44,45,46,50,72] {
        let mut bad=outer.clone();
        bad.public_values[published_index][i]+=openvm_stark_sdk::config::baby_bear_poseidon2::F::ONE;
        assert!(parent.verify(&parent_vk,&bad).is_err());
    }
    println!("NEARPROOF_LITERAL_PARENT_BYTES={} PUBLIC_FIELDS={} NEGATIVES=6",bytes.len(),expected.len());
}
