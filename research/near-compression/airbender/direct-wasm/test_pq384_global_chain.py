"""Completeness, exact projection arithmetic and malformed/forged-stage tests."""
import argparse,copy,json,sys
from array import array
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--library',required=True)
    a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_global_chain as gc
    import pq384_batched_fold as old
    from pq384_native_fft import NativeFFT
    from pq384_cached_prover import FlatTree,flat
    from packed_claim_handoff import packing_context,mle_ext
    from pq384_one_fold import base
    native=NativeFFT(a.library);P=gc.P
    rows=[[((i+3)*(j+7)+i*i)%P for j in range(19)] for i in range(8)]
    matrices=[];degree=128
    for lane in range(2):
        cs=[rows[i][lane*16+j] if lane*16+j<19 else 0 for j in range(16) for i in range(8)]
        bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:cs[i]=(cs[i]-cs[i^bit])%P
            bit*=2
        matrices.append([base(v) for v in cs])
    ctx=packing_context(3,19,16);root,layers,leaves=old.source_tree(matrices,ctx)
    class Cache:
        def coefficients(self,lane):return array('I',(v[0] for v in matrices[lane]))
        def opening(self,i):return old.opening(layers,leaves,i)
    cache=Cache();cache.root=root;cache.context=ctx;cache.degree=degree;cache.lanes=2
    point=[(2,3,5,7),(11,13,17,19),(23,29,31,37)]
    args=dict(statement=b'global-chain test',parent_binding=b'fixed-parent',expected_root=root,
              log_rows=3,width=19,packing=16,row_point=point,
              column_claims=[mle_ext([base(row[j]) for row in rows],point) for j in range(19)])
    rejected=0
    for terminal in (1,64):
        proof=gc.prove_cached(cache,native,terminal_degree=terminal,**args)
        assert gc.verify(proof,terminal_degree=terminal,**args)
        def reject(p):
            nonlocal rejected
            try:gc.verify(p,terminal_degree=terminal,**args)
            except (ValueError,KeyError,IndexError,TypeError):rejected+=1
            else:raise AssertionError('forgery accepted')
        p=copy.deepcopy(proof);p['rounds'][0]['next_root']='00'*48;reject(p)
        p=copy.deepcopy(proof);p['rounds'][0]['quadratic'][0][0]^=1;reject(p)
        p=copy.deepcopy(proof);p['terminal']['coefficients'][0][0][0]^=1;reject(p)
        p=copy.deepcopy(proof);p['queries'][0][0]['next']['leaf'][0]^=1;reject(p)
        p=copy.deepcopy(proof);p['queries'][0][0]['source']['path'][0]='00'*48;reject(p)
        p=copy.deepcopy(proof);p['queries'][0].pop();reject(p)
        p=copy.deepcopy(proof);p['queries'].pop();reject(p)
        # A genuine alternate polynomial/tree does not match committed stage.
        alternate=FlatTree(native.lde4_words(flat([(13,17,19,23)]*(degree//2))),b'forged-intermediate')
        p=copy.deepcopy(proof);p['rounds'][0]['next_root']=alternate.root.hex()
        p['queries'][0][0]['next']=alternate.opening(0);reject(p)
        try:gc.verify(proof,terminal_degree=65-terminal,**args)
        except ValueError:rejected+=1
        else:raise AssertionError('wrong trusted terminal profile accepted')
    # Independently evaluate actual polynomials at every initial-domain point.
    # Full Ext4 coefficients and challenge; repeated squaring through constant.
    from pq384_terminal import horner
    from check_whir_handoff import add,sub,mul
    coefficients=[(i+1,2*i+3,3*i+5,7*i+11) for i in range(16)]
    r=(5,7,11,13);checks=0;initial=16
    while len(coefficients)>1:
        d=len(coefficients);omega0=pow(440564289,(1<<27)//(4*initial),P)
        omega=pow(440564289,(1<<27)//(4*d),P)
        folded=old.fold(coefficients,r)
        for s in range(4*initial):
            x=pow(omega,s%(4*d),P);assert x==pow(pow(omega0,s,P),initial//d,P)
            pair_index=s%(2*d);canonical_x=pow(omega,pair_index,P)
            aa=horner(coefficients,base(canonical_x));bb=horner(coefficients,base(-canonical_x%P))
            even=tuple(v*pow(2,-1,P)%P for v in add(aa,bb))
            odd=tuple(v*pow(2*canonical_x,-1,P)%P for v in sub(aa,bb))
            expected=add(even,mul(r,sub(odd,even)))
            next_omega=omega*omega%P;next_x=pow(next_omega,s%d,P)
            pair=[horner(folded,base(next_x)),horner(folded,base(-next_x%P))]
            assert expected==pair[(s%(2*d))//d]==horner(folded,base(x*x%P));checks+=1
        coefficients=folded
    print(json.dumps(dict(status='PASS',terminal_profiles=[1,64],negative_checks=rejected,
                         independent_full_domain_chain_checks=checks)))

if __name__=='__main__':main()
