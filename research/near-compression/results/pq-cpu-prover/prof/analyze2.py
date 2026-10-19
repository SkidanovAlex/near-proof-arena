import sys,re,collections
txt=open(sys.argv[1]).read()
keys=sys.argv[2].split(",") if len(sys.argv)>2 else ["fill_inner","level_from_input","level_up","gkr::pass","round_evals","run_base","round0::round0","from_ple","zc::SoaTable","fold","rows_packed","horner","stream_commit","hash_coset_batch","sha384_x8","compress_pairs","dft_batch","coset_dft","eval_to_coeff","evals_eq","w_evals","stacked_reduction","prove_whir","fractional","sumcheck","malloc","free","memcpy","memmove"]
inner=collections.Counter(); outer=collections.Counter(); n=0
for s in txt.split("=== SAMPLE ")[1:]:
    for th in s.split("\nThread ")[1:]:
        fr=[re.sub(r"^#\d+\s+(0x[0-9a-f]+ in )?","",l) for l in th.split("\n") if l.startswith("#")]
        if not fr: continue
        j=" | ".join(fr[:6])
        if any(x in fr[0] for x in ["syscall","futex","epoll","sched_yield","nanosleep"]) or "rayon_core::sleep" in j or "wait_until" in j: continue
        n+=1
        hit=[k for f in fr for k in keys if k in f.split(" (")[0]]
        inner[hit[0] if hit else "?:"+fr[0].split(" (")[0][:60]]+=1
        outer[hit[-1] if hit else "?"]+=1
print("samples",n)
print("-- innermost known:"); [print("%5.1f%% %s"%(100*v/n,k)) for k,v in inner.most_common(25)]
print("-- outermost known:"); [print("%5.1f%% %s"%(100*v/n,k)) for k,v in outer.most_common(12)]
