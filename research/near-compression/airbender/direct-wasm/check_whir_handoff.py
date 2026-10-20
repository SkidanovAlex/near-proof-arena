#!/usr/bin/env python3
"""Independent full-witness WHIR handoff diagnostic, NOT full WHIR verification."""
import json,sys
from pathlib import Path
from copy import deepcopy
from check_commitment import opening
P=2013265921
INV_R=pow(2**32,-1,P)
ZERO=(0,0,0,0)
ONE=(1,0,0,0)
def ext(x):
    # Tower coordinates [1,u,v,uv], u^2=11, v^2=u -> [1,v,v^2,v^3].
    vals=[x['c0']['c0'],x['c1']['c0'],x['c0']['c1'],x['c1']['c1']]
    assert all(type(v)is int and 0<=v<P for v in vals)
    return tuple(v*INV_R%P for v in vals)
def add(a,b):return tuple((x+y)%P for x,y in zip(a,b))
def sub(a,b):return tuple((x-y)%P for x,y in zip(a,b))
def mul(a,b):
    v=[0]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b):v[i+j]=(v[i+j]+x*y)%P
    for i in range(6,3,-1):v[i-4]=(v[i-4]+11*v[i])%P
    return tuple(v[:4])
def mle(values,point):
    values=[(v,0,0,0) for v in values]
    for r in point:values=[add(a,mul(r,sub(b,a))) for a,b in zip(values[::2],values[1::2])]
    assert len(values)==1
    return values[0]
def verify_claims(proof,rows,point):
    claims=proof['witness_commitment']['evals'];assert len(claims)==104
    for c,v in enumerate(claims):assert ext(v)==mle([r[c] for r in rows],point),'claim mismatch'
    batch=ext(proof['batching_challenge']);power=ONE;acc=ZERO
    for claim in claims:acc=add(acc,mul(power,ext(claim)));power=mul(power,batch)
    assert ext(proof['batched_opening'])==acc,'batch mismatch'
    coeff=[ext(c) for c in proof['sumcheck_polys'][0]];assert len(coeff)==3
    assert add(add(add(coeff[0],coeff[0]),coeff[1]),coeff[2])==acc,'initial sumcheck mismatch'
def main():
    artifact,source,commitment,report=map(Path,sys.argv[1:]);x=json.loads(artifact.read_text());proof=x['proof']
    rows=json.loads(source.read_text())['rows'];point=[ext(p) for p in x['evaluation_point']]
    assert proof['original_evaluation_point']==x['evaluation_point']
    verify_claims(proof,rows,point)
    commit=json.loads(commitment.read_text());root=commit['root']
    assert proof['witness_commitment']['commitment']['cap']['cap']==[root]
    expected={q['tree_index']:q for q in commit['openings']}
    for query in proof['witness_commitment']['queries']:
        e=expected[query['index']];raw=query['leaf_values_concatenated'];assert len(raw)==208
        q={'tree_index':query['index'],'raw_words':[raw[:104],raw[104:]],'path':query['path']}
        assert q['raw_words']==e['raw_words'] and opening(q,root),'base opening mismatch'
    rejected=0
    for i in range(104):
        bad=deepcopy(proof);v=bad['witness_commitment']['evals'][i]['c0'];v['c0']=(v['c0']+1)%P
        try:verify_claims(bad,rows,point)
        except AssertionError:rejected+=1
        else:raise AssertionError('bad claim accepted')
    out={'status':'PASS','opening_claims_recomputed':104,'changed_claims_rejected':rejected,
         'base_query_openings_checked':len(proof['witness_commitment']['queries']),
         'initial_sumcheck_identity_checked':True,'fresh_whir_artifact_generated':True,
         'artifact_bincode_bytes':x['bincode_bytes'],'full_whir_verified':False,
         'limitations':['Full witness used to recompute claims.','Fiat-Shamir replay, intermediate openings, OOD mixing, final folding and polynomial checks remain.','Toy parameters; no GKR proof, recursion or quantum-security claim.']}
    report.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
