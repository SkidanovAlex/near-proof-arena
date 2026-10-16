"""Counterfactual grouped-fold geometry calibrated against actual proof bytes.
No alternative rate/folding protocol or associated soundness theorem is implied.
"""
import argparse,gzip,hashlib,json,random
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import pq384_ext8_weighted_codec as codec
import sha384_call_ext8_pcs as calls


def minimum_queries(factor,bits):
    q=0
    while 2*factor**q>Fraction(1,1<<bits):q+=1
    assert q==0 or 2*factor**(q-1)>Fraction(1,1<<bits)
    return q


def geometry(branches,degree,rate,samples,*,grouped,merkle_layout="paired",first_group=None):
    n=degree.bit_length()-1
    def opening(half,width,step,k):
        if merkle_layout=='coset':
            # Existing low-degree sources need fewer distinct values under
            # the virtual x^(D/d) embedding; keep at least paired leaves.
            factor=max(1,half//step)
            width*=factor;half//=factor
            indices={s%half for s in samples}
        else:
            assert merkle_layout=='paired'
            indices={((s+j*step)%half) for s in samples for j in range(1<<(k-1))}
        leaves=len(indices)*width;auth=len(codec.mp.boundary(half,list(indices)))*48
        return leaves+auth,leaves,auth
    def source_cost(k):
        seen=set();tot=[0,0,0]
        for b in branches:
            d=(1<<b['log_rows'])*b['packing'];half=rate*d//2
            key=(b['root'],b['log_rows'],b['width'],b['packing'])
            if key in seen:continue
            seen.add(key)
            x=opening(half,8*len(b['lanes']),rate*degree//(1<<k),k)
            tot=[a+b for a,b in zip(tot,x)]
        return tuple(tot)
    @lru_cache(None)
    def tail(logd):
        if logd==0:return (0,[],0,0)
        candidates=[]
        for k in range(1,min(4 if grouped else 1,logd)+1):
            size,leaves,auth=opening(rate*(1<<logd)//2,64,rate*(1<<logd)//(1<<k),k)
            rest,path,rl,ra=tail(logd-k)
            candidates.append((size+48+rest,[k]+path,leaves+rl,auth+ra))
        return min(candidates,key=lambda x:x[0])
    candidates=[]
    for k in ([first_group] if first_group is not None else range(1,min(4 if grouped else 1,n)+1)):
        assert 1<=k<=min(4 if grouped else 1,n)
        source,sl,sa=source_cost(k);rest,path,fl,fa=tail(n-k)
        groups=[k]+path;header=40+192*n+48*len(groups)
        candidates.append(dict(bytes=header+source+rest-48*len(path),groups=groups,header_bytes=header,source_leaf_bytes=sl,source_auth_bytes=sa,fold_leaf_bytes=fl,fold_auth_bytes=fa))
    best=min(candidates,key=lambda x:x['bytes'])
    assert best['bytes']==sum(best[k] for k in ('header_bytes','source_leaf_bytes','source_auth_bytes','fold_leaf_bytes','fold_auth_bytes'))
    return best


def main():
    p=argparse.ArgumentParser();p.add_argument('--capture',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];read=lambda path:json.loads(path.read_text())
    cfg=read(a.capture/'opening.json');proof=read(a.capture/'proof.json');D=1<<len(proof['rounds'])
    samples=codec.p.replay(proof,bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']),cfg['branches'],cfg['claim'],queries=cfg['queries'])[-1]
    c=geometry(cfg['branches'],D,4,samples,grouped=False)
    assert c['bytes']==(a.capture/'proof.bin').stat().st_size==1636192
    callpath=package/'results/call-ext8-q309/proof.json.gz';cp=json.loads(gzip.decompress(callpath.read_bytes()))
    statement=json.loads(gzip.decompress((package/'results/call-ext8-q309/statement.json.gz').read_bytes()))
    receipt=read(package/'results/ext8-node-batch/expected-use.json');cs=read(package/'results/ext8-linked-calls/calls.json')
    layout,st,binding,_=calls.compile_layout(statement,receipt,cs,queries=309);ob=calls.g.verify(layout,binding,cp['gkr']);bs=calls.branches(statement,ob)
    call_samples=codec.p.replay(cp['opening'],st,calls.parent(binding,cp['gkr']),bs,ob['private_claim'],queries=309)[-1]
    cd=1<<len(cp['opening']['rounds']);cal=geometry(bs,cd,4,call_samples,grouped=False)
    assert cal['bytes']==103064-19528
    fixed=117352+19528+5858+731
    assert fixed+c['bytes']+cal['bytes']==1863197
    records=[]
    for bits in (128,220):
        for rate in (4,16,64,256):
            for regime,factor in [('current',Fraction(2*rate+1,3*rate)),('upstream_unique',Fraction(rate+1,2*rate)),('upstream_johnson',Fraction(21,20*int(rate**.5)))]:
                q=minimum_queries(factor,bits);runs=[]
                for seed in range(4):
                    rng=random.Random(901000+seed)
                    large=[rng.randrange(rate*D) for _ in range(q)];small=[rng.randrange(rate*cd) for _ in range(q)]
                    x=geometry(cfg['branches'],D,rate,large,grouped=True,merkle_layout='coset');y=geometry(bs,cd,rate,small,grouped=True,merkle_layout='coset')
                    runs.append(dict(seed=seed,compression=x,calls=y,combined_bytes=fixed+x['bytes']+y['bytes']))
                records.append(dict(query_union_target_bits=bits,blowup=rate,regime=regime,agreement_factor=str(factor),queries=q,min_bytes=min(x['combined_bytes'] for x in runs),max_bytes=max(x['combined_bytes'] for x in runs),runs=runs))
    out=dict(status='CALIBRATED_COUNTERFACTUAL_GEOMETRY',baseline=dict(compression=c,calls=cal,combined_bytes=1863197),fixed_bytes=fixed,records=records,
        upstream_commit='afec1fac27c1c8cc7331aa5668bc9800f104d92c',source='https://github.com/worldfnd/whir/blob/afec1fac27c1c8cc7331aa5668bc9800f104d92c/src/protocols/params/regime.rs',
        scope='Simulates changing domain blowup and committing after groups of1..4binary folds, retaining all quadratic messages and exact coset leaf/frontier costs. Whole fold cosets are newly committed as single leaves; low-degree source embeddings retain at least paired leaves. Same original query indices propagate through groups. Source widths/packings and upstream scalar overhead fixed. New root layouts/rates/groups/unique/Johnson bounds are NOT implemented or certified for our protocol. No capacity conjecture or grinding. Excludes new error terms, OOD/code-switch messages, full recursion, trusted static AIR/spec and QROM. Query union targets are hypothetical component budgets, not quantum-security conversions.',
        hashes={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in [Path(__file__),a.capture/'opening.json',a.capture/'proof.bin',callpath]})
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    for bits in (128,220):
        best=min((r for r in records if r['query_union_target_bits']==bits),key=lambda r:r['min_bytes'])
        print(bits,best['regime'],best['blowup'],best['queries'],best['min_bytes'],best['max_bytes'])

if __name__=='__main__':main()
