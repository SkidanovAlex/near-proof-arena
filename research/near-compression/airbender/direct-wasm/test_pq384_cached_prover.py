"""Exact proof/transcript parity with original all-Python prover."""
import argparse,sys
from array import array


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--library',required=True)
    a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_batched_fold as ref
    from pq384_cached_prover import prove_cached
    from pq384_native_fft import NativeFFT
    from packed_claim_handoff import packing_context,mle_ext
    from pq384_one_fold import base,ZERO
    from pq384_primitives import P
    native=NativeFFT(a.library)
    for packing,width in [(16,19),(32,64)]:
        rows=[[((i+3)*(j+7)+i*i)%P for j in range(width)] for i in range(8)]
        degree=8*packing;matrices=[]
        for lane in range((width+packing-1)//packing):
            cs=[rows[i][lane*packing+j] if lane*packing+j<width else 0 for j in range(packing) for i in range(8)]
            bit=1
            while bit<degree:
                for i in range(degree):
                    if i&bit:cs[i]=(cs[i]-cs[i^bit])%P
                bit*=2
            matrices.append([base(v) for v in cs])
        ctx=packing_context(3,width,packing);root,layers,leaves=ref.source_tree(matrices,ctx)
        class Cache:
            def coefficients(self,lane):return array('I',(v[0] for v in matrices[lane]))
            def opening(self,i):return ref.opening(layers,leaves,i)
        cache=Cache();cache.root=root;cache.context=ctx;cache.degree=degree;cache.lanes=len(matrices)
        point=[(2,3,5,7),(11,13,17,19),(23,29,31,37)]
        claims=[mle_ext([base(row[j]) for row in rows],point) for j in range(width)]
        args=dict(statement=b'cached parity',parent_binding=b'parity',expected_root=root,
                  log_rows=3,width=width,packing=packing,row_point=point,column_claims=claims)
        original=ref.prove(rows,**args);accelerated=prove_cached(cache,native,**args)
        assert accelerated==original
        assert ref.verify(accelerated,**args)
    print('PASS: exact proof parity for D128/2lanes and D256/2lanes')

if __name__=='__main__':main()
