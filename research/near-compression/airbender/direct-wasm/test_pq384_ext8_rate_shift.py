#!/usr/bin/env python3
import argparse,copy,json,hashlib,subprocess,sys
from pathlib import Path
import pq384_ext8_rate_shift as r
p=r.p;e=r.e

def naive(cs,x):
    out=e.ZERO
    for i,c in enumerate(cs):out=e.add(out,e.mul(c,e.power(x,i)))
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--verify-only',action='store_true');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    if a.verify_only:
        env=json.loads((a.output/'proof.json').read_text());assert r.verify(env['proof'],env['config'],bytes.fromhex(env['root']));print('PASS fresh rate-shift algebra verifier');return
    coeff=[(i*i*541+i*173+11)%e.P for i in range(32)];point=[tuple((i+7)*(j+19) for j in range(8)) for i in range(5)]
    claim=e.ZERO
    for i,c in enumerate(coeff):
        w=e.ONE
        for j,u in enumerate(point):w=e.mul(w,u if(i>>j)&1 else e.sub(e.ONE,u))
        claim=e.add(claim,e.scale(w,c))
    cfg=dict(profile=p.PROFILE,degree=32,queries=4,point=[list(u) for u in point],claim=list(claim),statement=b'rate-shift-prerequisite'.hex(),source_namespace=b'rate-shift-base32'.hex())
    source=p.source_tree(coeff,cfg);root=source['root'];proof=r.prove(coeff,cfg,root);assert r.verify(proof,cfg,root);state=r.inspect(proof,cfg,root);assert all(x==e.ZERO for x in state['errors'])
    # Independent powersum evaluation vs candidate FFT across full newdomain.
    omega=pow(440564289,(1<<27)//64,e.P);vals=e.fft(state['coefficients']+[e.ZERO]*56,omega)
    assert vals==[naive(state['coefficients'],e.base(pow(omega,i,e.P))) for i in range(64)]
    t=r.start(cfg,root);cs=[e.base(x) for x in coeff];rs=[];cl=claim
    for wire in proof['quadratics']:
        x,cl=p.round_start(t,wire,cl);rs.append(x);cs=e.affine_fold(cs,x)
    omegaold=pow(440564289,(1<<27)//32,e.P)
    for i in range(32):
        val=r.folded_query([p.opening(source,i),p.opening(source,i+32)],root,p.source_context(cfg),i,rs)
        assert val==naive(cs,e.base(pow(omegaold,i,e.P)))
    negatives=[]
    def reject(name,pf,cfg1=cfg,root1=root):
        try:r.verify(pf,cfg1,root1)
        except (ValueError,TypeError,KeyError,IndexError):negatives.append(name)
        else:raise AssertionError(name)
    def preserving(cs,w):
        out=list(cs);j=next(i for i,x in enumerate(w) if x!=e.ZERO);k=(j+1)%8
        out[k]=e.add(out[k],e.ONE);out[j]=e.sub(out[j],e.mul(w[k],e.inv(w[j])));assert r.dot(out,w)==r.dot(cs,w);return out
    forged=r.prove(coeff,cfg,root,alter=preserving);fs=r.inspect(forged,cfg,root)
    assert fs['errors'][0]==e.ZERO and fs['errors'][1]==e.ZERO and any(x!=e.ZERO for x in fs['errors'][2:])
    reject('coherent changedcandidate preservingoldfunctional validOODandpaths',forged)
    (a.output/'coherent-false-candidate.json').write_text(json.dumps(dict(proof=forged,config=cfg,root=root.hex(),errors=fs['errors'],gamma=fs['gamma'],residual=fs['residual'])))
    forgedood=r.prove(coeff,cfg,root,wrong_ood=True);r.inspect(forgedood,cfg,root);reject('coherent falseOOD freshquerytranscript',forgedood)
    (a.output/'coherent-false-ood.json').write_text(json.dumps(dict(proof=forgedood,config=cfg,root=root.hex())))
    for key,value in [('terminal',[[0]*8]*8),('next_root','00'*48),('ood_value',[0]*8),('profile','wrong'),('source_queries',proof['source_queries'][:-1])]:
        bad=copy.deepcopy(proof);bad[key]=value;reject(key,bad)
    reject('wrongroot',proof,cfg,bytes(48));reject('wrongstatement',proof,{**cfg,'statement':'00'});reject('wrongqueryprofile',proof,{**cfg,'queries':314})
    # No false claim of perfect mixing: gamma0 discards newconstraints.
    assert e.evaluate(fs['errors'],e.ZERO)==e.ZERO
    zero_bad_event=dict(candidate_has_false_query_constraints=True,aggregate_accepts_at_gamma_zero=True,
        explanation='Expected root of a nonzero mixing-error polynomial; actual transcript gamma rejected. No divide-by-weight or claimed perfect soundness.')
    env=dict(proof=proof,config=cfg,root=root.hex());data=json.dumps(env,separators=(',',':')).encode();(a.output/'proof.json').write_bytes(data)
    fresh=subprocess.run([sys.executable,__file__,'--output',str(a.output),'--verify-only'],check=True,capture_output=True,text=True)
    report=dict(status='PASS',source_degree=32,source_domain=128,next_degree=8,next_domain=64,queries=4,diagnostic_only=True,
        independent_newdomain_evaluations=64,all_prior_coset_fold_checks=32,negative_count=len(negatives),negatives=negatives,
        mixing_zero_bad_event=zero_bad_event,whole_json_bytes=len(data),fresh_process=fresh.stdout.strip(),
        scope='One constrained rate-shift accumulator with disclosed8coeff candidate, not complete WHIR or improved soundness.',
        files=[dict(path=str(x),sha256=hashlib.sha256(x.read_bytes()).hexdigest()) for x in [Path(__file__),Path(r.__file__)]])
    (a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
