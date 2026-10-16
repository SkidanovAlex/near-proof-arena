"""Fresh-verifier and malformed-chain checks; no source rows at verification."""
import argparse,copy,json,random,subprocess,sys,time
from pathlib import Path
import ext8_code_switch_stage as s
import pq384_ext8_reference as f


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    rng=random.Random(927164);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8));started=time.perf_counter();cases=[]
    saved=None
    for log,k,B,nextB in [(3,1,4,8),(5,2,4,16),(7,2,4,8),(8,3,4,16)]:
        cs=[scalar() for _ in range(1<<log)];weights=[scalar() for _ in cs];claim=s.algebra.dot(cs,weights)
        namespace=s.h.hash_parts(b'code-switch/test-namespace',s.h.u64(log)).hex()
        root=s.tree(cs,namespace,B,k)['root'].hex()
        # A second stage consumes the first stage's updated functional.
        nextk=min(2,log-k-1)
        config=dict(profile=s.PROFILE,degree=len(cs),blowup=B,fold_bits=k,next_blowup=nextB,next_fold_bits=nextk,queries=8,
                    namespace=namespace,parent=s.h.hash_parts(b'code-switch/test-parent').hex(),root=root)
        schedule=([dict(next_blowup=16,next_fold_bits=1,queries=8),dict(next_blowup=8,next_fold_bits=0,queries=8)] if log==7 else [dict(next_blowup=16,next_fold_bits=0,queries=8)])
        proof=s.prove_chain(cs,config,weights,claim,schedule)
        statement=dict(config=config,weights=weights,claim=claim,schedule=schedule)
        assert s.verify_chain(json.loads(json.dumps(proof)),config,weights,claim,schedule)
        case=dict(log_degree=log,fold_bits=([k,nextk,1] if log==7 else [k,nextk]),blowups=([B,nextB,16,8] if log==7 else [B,nextB,16]),json_bytes=len(s.canonical_json(proof)),terminal_coefficients=len(proof['terminal']))
        cases.append(case);saved=(proof,statement)
    proof,statement=saved
    (a.output/'proof.json').write_bytes(s.canonical_json(proof))
    (a.output/'statement.json').write_bytes(s.canonical_json(statement))
    fresh=subprocess.run([sys.executable,s.__file__,'--proof',str(a.output/'proof.json'),'--statement',str(a.output/'statement.json')],capture_output=True,text=True)
    (a.output/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode()
    negatives=[]
    def verify(p,st=statement):return s.verify_chain(p,st['config'],st['weights'],st['claim'],st['schedule'])
    def reject(name,p,st=statement):
        try:verify(p,st)
        except ValueError:negatives.append(name)
        else:raise AssertionError(name)
    def mutate(name,fn):
        p=copy.deepcopy(proof);fn(p);reject(name,p)
    def flip(v):v[0]=(v[0]+1)%f.P
    mutate('quadratic',lambda p:flip(p['stages'][0]['rounds'][0][0]))
    mutate('second-stage-quadratic',lambda p:flip(p['stages'][1]['rounds'][0][0]))
    mutate('stage-order',lambda p:p['stages'].reverse())
    mutate('child-root',lambda p:p['stages'][0].__setitem__('child_root','ab'*48))
    mutate('ood-answer',lambda p:flip(p['stages'][0]['ood_answer']))
    mutate('source-value',lambda p:flip(p['stages'][0]['source_openings'][0]['values'][0]))
    mutate('source-path',lambda p:p['stages'][0]['source_openings'][0]['path'].__setitem__(0,'ab'*48))
    mutate('missing-query',lambda p:p['stages'][0]['source_openings'].pop())
    mutate('missing-round',lambda p:p['stages'][0]['rounds'].pop())
    mutate('missing-stage',lambda p:p['stages'].pop())
    mutate('terminal-coefficient',lambda p:flip(p['terminal'][0]))
    mutate('terminal-shape',lambda p:p['terminal'].pop())
    mutate('noncanonical',lambda p:p['stages'][0]['ood_answer'].__setitem__(0,f.P))
    mutate('proof-selected-weights',lambda p:p['stages'][0].__setitem__('weights',[]))
    mutate('unknown-chain-field',lambda p:p.__setitem__('accepted',True))
    for key,value in [('root','cd'*48),('namespace','ef'*48),('parent','12'*48),('next_blowup',8),('queries',9)]:
        st=copy.deepcopy(statement);st['config'][key]=value;reject('external-'+key,proof,st)
    st=copy.deepcopy(statement);st['schedule'][0]['queries']=9;reject('external-schedule',proof,st)
    st=copy.deepcopy(statement);st['claim']=list(st['claim']);flip(st['claim']);reject('external-claim',proof,st)
    st=copy.deepcopy(statement);st['weights']=[list(w) for w in st['weights']];flip(st['weights'][0]);reject('external-weights',proof,st)
    # Even a forged state passing its root check must fail a wrong continuing claim.
    st=statement;cfg=s.chain_start(st['config'],st['schedule']);state=s.verify_stage(proof['stages'][0],cfg,st['weights'],st['claim'])
    cfg=s.follow_config(state,st['schedule'][0]);state=s.verify_stage(proof['stages'][1],cfg,state['weights'],state['claim'])
    flip(state['claim'])
    try:s.close_terminal(state,proof['terminal'])
    except ValueError as exc:assert str(exc)=='terminal residual';negatives.append('unproved-continuing-claim')
    else:raise AssertionError('terminal residual bypass')
    report=dict(status='PASS',cases=cases,negative_cases=negatives,fresh_verifier=fresh.stdout.strip(),seconds=time.perf_counter()-started,
        scope='Experimental two/three-stage scalar Ext8 protocol with full terminal disclosure; JSON size only, not a compressed envelope or security certificate. No integration into full SHA384/NEAR slice.')
    (a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
