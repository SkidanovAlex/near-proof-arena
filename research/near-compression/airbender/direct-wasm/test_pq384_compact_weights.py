"""Independent dense-fold comparison, including zero accumulated factors."""
import json,random
from pq384_batched_fold import weights,fold,ONE,ZERO,add,sub,mul,P
rng=random.Random(38418)
cases=0
for n in range(1,13):
    for mode in range(3):
        point=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(n)]
        challenges=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(n)]
        if mode==1:point[0]=ZERO;challenges[0]=ONE
        if mode==2:point[0]=ONE;challenges[0]=ZERO
        dense=weights(point);factor=ONE
        for k in range(n+1):
            compact=[mul(factor,w) for w in weights(point[k:])]
            assert compact==dense
            cases+=1
            if k<n:
                dense=fold(dense,challenges[k])
                factor=mul(factor,add(ONE,mul(challenges[k],sub(point[k],ONE))))
print(json.dumps({'status':'PASS','dense_compact_comparisons':cases,
    'zero_factors_included':True,'scope':'Exact implementation parity; no cryptographic soundness claim'},indent=2))
