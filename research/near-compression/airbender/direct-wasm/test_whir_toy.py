#!/usr/bin/env python3
"""Negative tests for the fixed-profile WHIR verifier; no soundness certification."""
from copy import deepcopy
import json,sys,hashlib
from pathlib import Path
from verify_whir_toy import verify,P,Transcript,words,ext,ZERO,ONE,add,mul

def change(v,path):
    for k in path[:-1]:v=v[k]
    v[path[-1]]=(v[path[-1]]+1)%P

def main():
    src,statement,out=map(Path,sys.argv[1:]);x=json.loads(src.read_text());root=json.loads(statement.read_text())['root'];verify(x,root)
    paths=[];p=['proof']
    for i in range(104):paths.append(p+['witness_commitment','evals',i,'c0','c0'])
    for i in range(3):paths.append(['evaluation_point',i,'c1','c1'])
    for i in range(2):
        for j in range(3):
            for a,b in [('c0','c0'),('c0','c1'),('c1','c0'),('c1','c1')]:paths.append(p+['sumcheck_polys',i,j,a,b])
    paths.extend([p+['ood_samples',0,'c0','c1'],p+['pow_nonces',0],p+['pow_nonces',1]])
    for i in range(2):paths.append(p+['final_monomials',i,'c0','c0'])
    for i in range(8):
        prefix=p+['witness_commitment','queries',i]
        for j in [0,51,103,104,155,207]:paths.append(prefix+['leaf_values_concatenated',j])
        for j in range(4):paths.append(prefix+['path',j,0])
        paths.append(prefix+['index'])
        prefix=p+['intermediate_whir_oracles',0,'queries',i]
        for j in range(2):paths.append(prefix+['leaf_values_concatenated',j,'c0','c0'])
        for j in range(3):paths.append(prefix+['path',j,0])
        paths.append(prefix+['index'])
    paths.append(p+['intermediate_whir_oracles',0,'commitment','cap','cap',0,0])
    rejected=0
    def rejects(bad):
        nonlocal rejected
        try:verify(bad,root)
        except (ValueError,KeyError,IndexError,TypeError):rejected+=1
        else:raise RuntimeError('corruption accepted')
    for path in paths:
        bad=deepcopy(x);change(bad,path);rejects(bad)
    # Preserve q(0)+q(1) while changing the polynomial and transcript.
    bad=deepcopy(x);cs=bad['proof']['sumcheck_polys'][0]
    cs[0]['c0']['c0']=(cs[0]['c0']['c0']+1)%P
    cs[1]['c0']['c0']=(cs[1]['c0']['c0']-2)%P
    rejects(bad)
    # Change a claim AND coherently recompute the handoff seed, batching challenge,
    # and batched claim. This reaches the first sumcheck instead of failing seed binding.
    bad=deepcopy(x);change(bad,p+['witness_commitment','evals',0,'c0','c0'])
    t=Transcript(bad['statement_words']);t.draw(3,True);t.commit_ext(bad['proof']['witness_commitment']['evals']);batch=t.draw(1,True)[0]
    def encode(e):
        v=[e[i]*2**32%P for i in (0,2,1,3)]
        return {'c0':{'c0':v[0],'c1':v[1]},'c1':{'c0':v[2],'c1':v[3]}}
    import struct
    bad['initial_whir_seed']=list(struct.unpack('<8I',t.seed));bad['proof']['batching_challenge']=encode(batch)
    acc=ZERO;power=ONE
    for claim in bad['proof']['witness_commitment']['evals']:acc=add(acc,mul(power,ext(claim)));power=mul(power,batch)
    bad['proof']['batched_opening']=encode(acc);rejects(bad)
    for name in ['sumcheck_polys','final_monomials','ood_samples','pow_nonces']:
        for extra in [False,True]:
            bad=deepcopy(x);v=bad['proof'][name]
            if extra:v.append(deepcopy(v[-1]))
            else:v.pop()
            rejects(bad)
    bad=deepcopy(x);bad['proof']['whir_schedule']['whir_queries_schedule']=[1,1];rejects(bad)
    bad=deepcopy(x);bad['proof']['witness_commitment']['evals'][0]['c0']['c0']=P;rejects(bad)
    badroot=root.copy();badroot[0]^=1
    try:verify(x,badroot)
    except ValueError:rejected+=1
    else:raise RuntimeError('wrong trusted root accepted')
    result={'status':'PASS','honest_proofs_accepted':1,'mutations_rejected':rejected,
            'coherent_handoff_mutation_rejected':True,'sumcheck_identity_preserving_mutation_rejected':True,
            'witness_required':False,'full_fixed_profile_whir_checks':True,
            'scope':'Fixed eight-row toy opening only; no GKR or NEAR transition proof; no security claim.',
            'sha256':{str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in [src,statement,Path(__file__),Path(__file__).with_name('verify_whir_toy.py')]}}
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
