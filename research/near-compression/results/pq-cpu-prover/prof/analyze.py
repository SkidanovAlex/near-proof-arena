import sys,re,collections
txt=open(sys.argv[1]).read()
samples=txt.split("=== SAMPLE ")[1:]
cats=[("gkr_input_eval_interactions",["prove_zerocheck_and_logup::{closure#1}"]),
 ("gkr_tree_build",["fractional_sumcheck_with"],["sumcheck_round_poly_evals","fold_mle_evals","evals_eq"]),
]
keys=["eval_interactions","acc_constraints","sumcheck_round_poly_evals_rm","fold_mle_evals_rm","sumcheck_round_poly_evals","fold_mle_evals","evals_eq_hypercube","fractional_sumcheck_with","sumcheck_uni_round0_zerocheck_packed","sumcheck_uni_round0_batch","fold_ple_evals_rowmajor","rs_code","merkle","stacked","whir","prove_zerocheck_and_logup","eval_nodes","malloc","free","realloc","memcpy","memmove"]
top=collections.Counter(); ctx=collections.Counter(); inner=collections.Counter(); nthr=0
for s in samples:
    for th in s.split("\nThread ")[1:]:
        frames=[re.sub(r"^#\d+\s+(0x[0-9a-f]+ in )?","",l).split(" (")[0] for l in th.split("\n") if l.startswith("#")]
        if not frames: continue
        f0=frames[0]
        if any(x in f0 for x in ["syscall","futex","epoll","sched_yield","__GI___clock_nanosleep","wait"]) or "rayon_core::sleep" in " ".join(frames[:6]): continue
        nthr+=1
        inner[re.sub(r"<.*","",f0)]+=1
        joined=" | ".join(frames)
        # context = outermost-ish informative frames
        c=[]
        for k in ["fractional_sumcheck_with","sumcheck_polys_eval","sumcheck_uni_round0_polys","fold_ple_evals","fold_mle_evals","prove_zerocheck_and_logup::{closure","stacked_commit","whir","prove_stacked_opening","keygen","generate","verify"]:
            if k in joined: c.append(k)
        for k in ["eval_interactions","acc_constraints","eval_nodes","sumcheck_round_poly_evals","fold_mle","evals_eq_hypercube","malloc","free","memcpy","realloc"]:
            if k in joined: c.append(k)
        ctx[" / ".join(c) or "other:"+re.sub(r"<.*","",f0)]+=1
print("busy thread-samples",nthr)
for k,v in ctx.most_common(30): print("%5.1f%% %s"%(100*v/nthr,k))
print("--- innermost")
for k,v in inner.most_common(25): print("%5.1f%% %s"%(100*v/nthr,k))
