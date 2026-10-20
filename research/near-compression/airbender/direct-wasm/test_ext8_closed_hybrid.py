"""Dense/hybrid acceptance, exact transcript and transition parity."""
import argparse
import copy
import hashlib
import inspect
import json
from pathlib import Path
import random
import subprocess
import sys
import ext8_closed_hybrid_verify as hybrid
import ext8_closed_derived_switch as dense
from pq384_ext8_native import Kernel
from test_ext8_input_weights import coefficient_claim
from measure_ext8_recursive_hash_work import measure,frame
f=hybrid.f
ROOT=Path(__file__).resolve().parents[2]


def main():
    p=argparse.ArgumentParser();p.add_argument('--native-library',type=Path,required=True);p.add_argument('--output-dir',type=Path,required=True);a=p.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True)
    for actual,original in [(hybrid.obligation,dense.original_stage.obligation),(hybrid.initial_obligation,dense.original_adapter.initial_obligation)]:
        assert inspect.getsource(actual)==inspect.getsource(original).replace('weights=[list(w) for w in weights]','weights=weights')
    native=Kernel(a.native_library);rng=random.Random(46437380);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8))
    n=10;rows=[[rng.randrange(f.P) for _ in range(2)] for _ in range(1<<n)];cache=dense.original_adapter.pcs.Source(rows,1,native)
    b=dict(root=cache.root.hex(),log_rows=n,width=2,packing=1,row_point=[scalar() for _ in range(n)],lanes=[[[scalar()] for _ in range(2)] for _ in range(2)])
    claim=coefficient_claim(rows,b);config=dict(queries=31,child_blowup=8,child_fold_bits=2,tail_steps=[dict(next_blowup=16,next_fold_bits=1,queries=31),dict(next_blowup=8,next_fold_bits=0,queries=31)])
    s=dict(statement=b'hybrid-test'.hex(),parent=b'parent'.hex(),branches=[b],claim=claim,config=config)
    args=(bytes.fromhex(s['statement']),bytes.fromhex(s['parent']),s['branches'],s['claim'],config)
    proof=dense.prove([cache],native,*args);assert dense.verify(proof,*args,native=native)
    events=[];assert hybrid.verify(proof,*args,native=native,events=events)
    assert any(e.get('structured') is True for e in events) and any(e.get('structured') is False for e in events)
    assert any(e['kind']=='materialize' for e in events)
    # Identical proof/statement/profile: exact hash census must match, including dedup.
    measurements=[measure(lambda:fn(proof,*args,native=native)) for fn in (dense.verify,hybrid.verify)]
    assert measurements[0]['tags']==measurements[1]['tags'] and measurements[0]['totals']==measurements[1]['totals']
    transcripts=[]
    for fn in (dense.verify,hybrid.verify):
        frames=[]
        def profile(call,event,arg):
            if event=='call' and call.f_code is hybrid.h.hash_parts.__code__:
                frames.append(frame(call.f_locals['tag'],call.f_locals['parts']))
        sys.setprofile(profile)
        try:assert fn(proof,*args,native=native)
        finally:sys.setprofile(None)
        transcripts.append(frames)
    assert transcripts[0]==transcripts[1]
    negatives=[]
    for key in ('terminal','ood','tail','source','external-claim','injected-weights'):
        bad=copy.deepcopy(proof);badargs=list(args)
        if key=='external-claim':badargs[3]=f.add(claim,f.ONE)
        elif key=='injected-weights':bad['tail'][0]['weights']=[list(f.ZERO)]
        else:
            if key=='terminal':target=bad['terminal'][0]
            elif key=='ood':target=bad['first']['ood_answer']
            elif key=='tail':target=bad['tail'][0]['rounds'][0][0]
            else:target=bad['first']['source_openings'][0][0]['leaf']
            target[0]=(target[0]+1)%f.P
        for fn in (dense.verify,hybrid.verify):
            try:fn(bad,*badargs,native=native)
            except ValueError:pass
            else:raise AssertionError('accepted '+key)
        negatives.append(key)
    # Every coefficient across representation changes, independently of proof acceptance.
    comparisons=0;point=[scalar() for _ in range(8)];weights=hybrid.eqs(point);state=hybrid.Weights(hybrid.Functional.equality(point),native,[]);claim=f.ZERO
    for step in range(8):
        points=[f.ZERO,f.ONE,scalar()];answers=[scalar() for _ in points];mixers=[scalar() for _ in points]
        prior_claim=claim
        weights,claim=native.inject(weights,prior_claim,points,answers,mixers);state,c=state.inject(prior_claim,points,answers,mixers)
        assert c==claim
        assert state.expanded()==weights;comparisons+=len(weights)
        r=f.ZERO if step==0 else f.ONE if step==1 else scalar()
        weights=native.affine_fold(weights,r);state=state.fold(r)
        assert state.expanded()==weights;comparisons+=len(weights)
    for name,value in [('proof.json',proof),('statement.json',s)]:(a.output_dir/name).write_bytes(hybrid.canonical_json(value))
    fresh=subprocess.run([sys.executable,hybrid.__file__,'--proof',str(a.output_dir/'proof.json'),'--statement',str(a.output_dir/'statement.json')],capture_output=True,text=True)
    (a.output_dir/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode()
    paths=[Path(__file__),Path(hybrid.__file__),Path(dense.__file__),Path(hybrid.Functional.fold.__code__.co_filename),Path(Kernel.__init__.__code__.co_filename),Path(dense.original_stage.__file__),Path(dense.original_adapter.__file__),Path(f.__file__),Path(hybrid.algebra.__file__)]+[a.output_dir/name for name in ('proof.json','statement.json','fresh-verifier.log')]
    report=dict(status='CLOSED_HYBRID_VERIFIER_PARITY',degree=1024,queries=31,events=events,hash_census=measurements[0]['totals'],exact_hash_census_match=True,exact_ordered_hash_preimages_match=True,compared_transition_coefficients=comparisons,negative_cases=negatives,fresh_verifier_passed=True,
        scope='One generated degree1024 closed-profile proof verified by dense and hybrid implementations with identical hash census and fresh pure-Python hybrid verification. Additional transition equality checks cover zero/one/random folds and zero/base/extension points. No full NEAR, formal Python refinement, PQ128 certificate, full-size proof or verifier speedup claim.',
        sha256={str(p.resolve().relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (a.output_dir/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
