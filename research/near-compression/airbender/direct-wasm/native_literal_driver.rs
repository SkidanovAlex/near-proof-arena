// Appended to the generated literal AIR adapter. Diagnostic parameters only.
fn requested_whir(params: &mut SystemParams, stage: &str) {
    if let Ok(raw) = std::env::var("NEARPROOF_LITERAL_QUERY_BITS") {
        let bits:usize=raw.parse().unwrap();
        assert!((1..=512).contains(&bits));
        let log_final_poly_len=params.log_final_poly_len();
        if let Ok(raw)=std::env::var("NEARPROOF_LITERAL_LOG_BLOWUP") {
            params.log_blowup=raw.parse().unwrap();
            assert!((1..=8).contains(&params.log_blowup));
        }
        params.whir=openvm_stark_backend::WhirConfig::new(
            params.log_blowup,params.l_skip+params.n_stack,
            openvm_stark_backend::WhirParams {
                k:params.whir.k,log_final_poly_len,
                proximity:params.whir.proximity,
                query_phase_pow_bits:0,folding_pow_bits:0,mu_pow_bits:0,
            },bits);
        params.logup.pow_bits=0;
        println!("NEARPROOF_LITERAL_QUERY_PROFILE stage={} query_bits={} log_blowup={} queries={:?} pow=0 field=Ext4 hash=Poseidon2",
            stage,bits,params.log_blowup,params.whir.rounds.iter().map(|r|r.num_queries).collect::<Vec<_>>());
    }
}

fn literal_wire_census(stage:&str,proof:&openvm_stark_backend::proof::Proof<BabyBearPoseidon2Config>) {
    use openvm_stark_backend::codec::Encode;
    fn size<T:Encode>(x:&T)->usize {let mut bytes=Vec::new();x.encode(&mut bytes).unwrap();bytes.len()}
    let (total,gkr,relations,stacking,whir)=(size(proof),size(&proof.gkr_proof),
        size(&proof.batch_constraint_proof),size(&proof.stacking_proof),size(&proof.whir_proof));
    println!("NEARPROOF_LITERAL_CENSUS stage={} total={} gkr={} relations={} stacking={} whir={} other={}",
        stage,total,gkr,relations,stacking,whir,total-gkr-relations-stacking-whir);
}

// Counterfactual parameter screen using an actual key's shape. This does not
// construct a larger field or regenerate the SHA-384 recursive circuit.
fn literal_field_screen(stage: &str, key: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<BabyBearPoseidon2Config>) {
    use openvm_stark_backend::soundness::SoundnessCalculator;
    let original=&key.inner.params;
    let airs=&key.inner.per_air;
    let constraints=airs.iter().map(|a|a.symbolic_constraints.constraints.constraint_idx.len()).max().unwrap();
    let interactions=airs.iter().map(|a|a.symbolic_constraints.interactions.len()).max().unwrap();
    let columns=airs.iter().map(|a|a.params.width.total_width()).sum();
    fn ceil_log(n:usize)->usize {if n<=1 {0} else {usize::BITS as usize-(n-1).leading_zeros() as usize}}
    let n_logup=ceil_log(original.logup.max_interaction_count as usize).saturating_sub(original.l_skip)
        .min((ceil_log(airs.len())+ceil_log(interactions)+original.log_stacked_height()).saturating_sub(original.l_skip));
    let calculate=|params:&SystemParams,degree:usize| SoundnessCalculator::calculate(
        params,2013265921.0,degree as f64*2013265921f64.log2(),constraints,airs.len(),
        params.max_constraint_degree,params.log_stacked_height(),columns,params.w_stack,n_logup);
    let baseline=calculate(original,4);
    assert!((baseline.total_bits-SoundnessCalculator::calculate_from_vk(key).total_bits).abs()<1e-9);
    println!("NEARPROOF_FIELD_SHAPE stage={} airs={} constraints={} columns={} n_logup={} baseline={}",stage,airs.len(),constraints,columns,n_logup,baseline.total_bits);
    for target in [258usize,268] {
        let mut params=original.clone();
        params.whir=openvm_stark_backend::WhirConfig::new(params.log_blowup,params.l_skip+params.n_stack,
            openvm_stark_backend::WhirParams {k:params.whir.k,log_final_poly_len:params.log_final_poly_len(),
                proximity:params.whir.proximity,query_phase_pow_bits:0,folding_pow_bits:0,mu_pow_bits:0},target);
        params.logup.pow_bits=0;
        for degree in [4usize,8,9,10,11,12] {
            let b=calculate(&params,degree);
            println!("NEARPROOF_FIELD_SCREEN stage={} target={} degree={} min={} logup={} proximity={} query={} passes={} queries={:?}",
                stage,target,degree,b.total_bits,b.logup_bits,b.whir_details.proximity_gaps_bits,
                b.whir_details.query_bits,b.total_bits>=target as f64,
                params.whir.rounds.iter().map(|r|r.num_queries).collect::<Vec<_>>());
        }
    }
}

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
    requested_whir(&mut params,"child");
    let child=BabyBearPoseidon2CpuEngine::<DuplexSponge>::new(params);
    let mut parent_params=test_system_params_small(2,16,3);
    parent_params.max_constraint_degree=MAX_CONSTRAINT_DEGREE;
    requested_whir(&mut parent_params,"parent");
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
    for (stage,key) in [("child",&child_vk),("parent",&parent_vk)] {
        let bound=openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(key);
        println!("NEARPROOF_LITERAL_RBR stage={} min_component={} logup={} gkr_sumcheck={} gkr_batching={} zerocheck={} constraint_batching={} stacking={} whir={} query={} proximity={}",
            stage,bound.total_bits,bound.logup_bits,bound.gkr_sumcheck_bits,bound.gkr_batching_bits,
            bound.zerocheck_sumcheck_bits,bound.constraint_batching_bits,bound.stacked_reduction_bits,
            bound.whir_bits,bound.whir_details.query_bits,bound.whir_details.proximity_gaps_bits);
    }
    if std::env::var_os("NEARPROOF_LITERAL_FIELD_SCREEN").is_some() {
        literal_field_screen("child",&child_vk);
        literal_field_screen("parent",&parent_vk);
        return;
    }
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
        literal_wire_census("parent",&outer);
        println!("NEARPROOF_LITERAL_REPLAY_PASS");
        return;
    }
    let proof=fx.prove(&child,&child_pk);
    child.verify(&child_vk,&proof).unwrap();
    literal_wire_census("child",&proof);
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
    literal_wire_census("parent",&outer);
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
