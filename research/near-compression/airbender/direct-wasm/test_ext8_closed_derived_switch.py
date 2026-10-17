"""Full closed-adapter proof, negative bindings and baseline isolation checks."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import ext8_closed_derived_switch as closed
import ext8_weighted_code_switch as baseline
from pq384_ext8_native import Kernel
from test_ext8_input_weights import coefficient_claim
from measure_ext8_recursive_hash_work import measure

ROOT=Path(__file__).resolve().parents[2]


def main():
    p=argparse.ArgumentParser();p.add_argument('--native-library',type=Path,required=True);p.add_argument('--output-dir',type=Path,required=True);a=p.parse_args()
    a.output_dir.mkdir(parents=True,exist_ok=True);rng=random.Random(674084);f=baseline.f;native=Kernel(a.native_library)
    scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8));caches=[];branches=[];claim=f.ZERO
    original_start=baseline.stage.start
    for n,width,packing in [(4,5,4),(2,3,2)]:
        rows=[[rng.randrange(f.P) for _ in range(width)] for _ in range(1<<n)]
        cache=baseline.pcs.Source(rows,packing,native);caches.append(cache)
        b=dict(root=cache.root.hex(),log_rows=n,width=width,packing=packing,row_point=[scalar() for _ in range(n)],lanes=[[[scalar() if j*packing+c<width else f.ZERO for c in range(packing)] for _ in range(2)] for j in range(cache.lanes)])
        branches.append(b);claim=f.add(claim,coefficient_claim(rows,b))
    config=dict(queries=8,child_blowup=8,child_fold_bits=2,tail_steps=[dict(next_blowup=16,next_fold_bits=1,queries=8),dict(next_blowup=8,next_fold_bits=0,queries=8)])
    s=dict(statement=b'closed-test'.hex(),parent=b'parent'.hex(),branches=branches,claim=list(claim),config=config)
    args=(bytes.fromhex(s['statement']),bytes.fromhex(s['parent']),branches,claim,config)
    old=baseline.prove(caches,native,*args);proof=closed.prove(caches,native,*args)
    assert baseline.stage.start is original_start and baseline.verify(old,*args,native=native)
    assert closed.verify(json.loads(json.dumps(proof)),*args,native=native)
    negatives=[]
    def verify(pr,st):return closed.verify(pr,bytes.fromhex(st['statement']),bytes.fromhex(st['parent']),st['branches'],st['claim'],st['config'],native=native)
    def reject(name,fn):
        try:fn()
        except ValueError:negatives.append(name)
        else:raise AssertionError('accepted '+name)
    reject('baseline-proof-in-closed-profile',lambda:verify(old,s))
    reject('closed-proof-in-baseline-profile',lambda:baseline.verify(proof,*args,native=native))
    relabeled=copy.deepcopy(old);relabeled['profile']=closed.PROFILE
    reject('baseline-proof-relabeled-closed',lambda:verify(relabeled,s))
    relabeled_back=copy.deepcopy(proof);relabeled_back['profile']=baseline.PROFILE
    reject('closed-proof-relabeled-baseline',lambda:baseline.verify(relabeled_back,*args,native=native))
    for key in ('statement','parent','claim','source-root','source-weight','query-count','schedule'):
        st=copy.deepcopy(s)
        if key in ('statement','parent'):st[key]=b'changed'.hex()
        elif key=='claim':st['claim'][0]=(st['claim'][0]+1)%f.P
        elif key=='source-root':st['branches'][0]['root']='00'*48
        elif key=='source-weight':st['branches'][0]['lanes'][0][0][0]=list(f.ONE)
        elif key=='query-count':st['config']['queries']=9
        else:st['config']['tail_steps'][0]['next_blowup']=8
        reject(key,lambda st=st:verify(proof,st))
    for key in ('input-reduction','first-root','first-ood','tail-round','terminal','injected-weight-field'):
        pr=copy.deepcopy(proof)
        if key=='first-root':pr['first']['child_root']='00'*48
        elif key=='injected-weight-field':pr['tail'][0]['weights']=[list(f.ZERO)]
        else:
            v=pr['reduction'][0][0] if key=='input-reduction' else pr['first']['ood_answer'] if key=='first-ood' else pr['tail'][0]['rounds'][0][0] if key=='tail-round' else pr['terminal'][0]
            v=list(v);v[0]=(v[0]+1)%f.P
            if key=='input-reduction':pr['reduction'][0][0]=v
            elif key=='first-ood':pr['first']['ood_answer']=v
            elif key=='tail-round':pr['tail'][0]['rounds'][0][0]=v
            else:pr['terminal'][0]=v
        reject(key,lambda pr=pr:verify(pr,s))
    for name,value in [('proof.json',proof),('statement.json',s)]:(a.output_dir/name).write_bytes(baseline.stage.canonical_json(value))
    fresh=subprocess.run([sys.executable,closed.__file__,'--proof',str(a.output_dir/'proof.json'),'--statement',str(a.output_dir/'statement.json')],capture_output=True,text=True)
    (a.output_dir/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode()
    measurements=dict(baseline=measure(lambda:baseline.verify(old,*args,native=native)),closed=measure(lambda:closed.verify(proof,*args,native=native)))
    paths=[Path(__file__),Path(closed.__file__),Path(baseline.__file__),Path(baseline.stage.__file__),Path(baseline.f.__file__),Path(baseline.stage.h.__file__),Path(Kernel.__init__.__code__.co_filename),Path(measure.__code__.co_filename)]+[a.output_dir/name for name in ('proof.json','statement.json','fresh-verifier.log')]
    report=dict(status='CLOSED_DERIVED_TRANSCRIPT_DIAGNOSTIC_VERIFIED',negative_cases=negatives,baseline_isolation_verified=True,fresh_verifier_passed=True,hash_measurements=measurements,json_proof_bytes=(a.output_dir/'proof.json').stat().st_size,
        scope='One small heterogeneous complete packed-root/code-switch proof under separate experimental profile. Full adapter derives all weights; standalone stage unchanged. Dense arithmetic still used. No compact full-NEAR proof, full-size benchmark, universal derived-state/FS/QROM proof or PQ128 claim.',
        sha256={str(p.resolve().relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (a.output_dir/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
