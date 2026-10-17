#!/usr/bin/env python3
"""Prove current/cyclic-next claims using the same committed source columns.
Fixed WHIR profile is diagnostic only; no AIR/bus or PQ security claim.
"""
import argparse,json,struct,subprocess,hashlib,random
from copy import deepcopy
from pathlib import Path
import shift_opening as reduction
from constraint_sumcheck import encode
from verify_whir_toy import Transcript,_verify_with_handoff,require,ext,P,ZERO,ONE,base,add,sub,mul
from run_kernel import PIN

def statement(root):
    require(len(root)==8,'root length')
    return list(b'NEAR-CYCLIC-NEXT-WHIR-EXPERIMENT-V1')+[8,104,4,1,1,2,1,1,8,8,4,0,0]+root

def verify_combined(proof,root):
    words=statement(root);t=Transcript(words);point=t.draw(3,True)
    opening=proof['opening'];require(opening['statement_words']==words,'shift statement')
    final=opening['proof']['witness_commitment']['evals']
    at=reduction.verify(proof['shift_reduction'],point,104,t,final)
    _verify_with_handoff(opening,root,(t,at))
    return True

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('airbender',type=Path)
    ap.add_argument('--heavy',default='/data/illia/nearproof-deps/bin/heavy');a=ap.parse_args()
    here=Path(__file__).resolve().parent;research=here.parent.parent;out=research/'results';repo=a.airbender.resolve()
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()!=PIN:raise SystemExit('Upstream revision mismatch')
    subprocess.run(['git','diff','--exit-code','HEAD','--','prover','cs','field','fft','transcript','blake2s_u32'],cwd=repo,check=True)
    for name in ('near_wasm_constraint_whir.rs','near_wasm_commitment.rs'):
        src=here/name;dst=repo/'prover/examples'/name
        if dst.exists() and dst.read_bytes()!=src.read_bytes():raise SystemExit('Different existing example')
        dst.write_bytes(src.read_bytes())
    def save(name,x):
        p=out/name;p.write_text(json.dumps(x,indent=2)+'\n');return p
    def run(example,*args):
        with (out/'direct-wasm-shift-run.log').open('a') as log:
            subprocess.run([a.heavy,'cargo','run','-p','prover','--example',example,'--',*map(str,args)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,check=True)
    source=out/'direct-wasm-air-export.json';rows=json.loads(source.read_text())['rows']
    cp=out/'direct-wasm-shift-commitment.json';run('near_wasm_commitment',source,cp);root=json.loads(cp.read_text())['root']
    words=statement(root);t=Transcript(words);point=t.draw(3,True)
    proof,at,final=reduction.prove(rows,point,t)
    hp=save('direct-wasm-shift-handoff.json',{'root':root,'statement_words':words,
            'pre_opening_seed':list(struct.unpack('<8I',t.seed)),'evaluation_point':[encode(v) for v in at]})
    op=out/'direct-wasm-shift-opening.json';run('near_wasm_constraint_whir',source,op,hp)
    opening=json.loads(op.read_text())
    require([ext(v) for v in opening['proof']['witness_commitment']['evals']]==final,'prover final parity')
    combined={'shift_reduction':proof,'opening':opening};verify_combined(combined,root)
    save('direct-wasm-shift-proof.json',combined);save('direct-wasm-shift-statement.json',{'root':root})
    rejected=[]
    def reject(label,bad,expected=root):
        try:verify_combined(bad,expected)
        except (ValueError,TypeError,KeyError,IndexError):rejected.append(label)
        else:raise AssertionError('Accepted '+label)
    for name in ('current_evals','next_evals'):
        for i in range(104):
            bad=deepcopy(combined);bad['shift_reduction'][name][i]['c0']['c0']^=1
            reject(f'{name} {i}',bad)
    for i in range(3):
        for j in range(3):
            bad=deepcopy(combined);bad['shift_reduction']['rounds'][i][j]['c0']['c0']^=1
            reject(f'round {i} coefficient {j}',bad)
    bad=deepcopy(combined);cs=bad['shift_reduction']['rounds'][0]
    cs[1]=encode(add(ext(cs[1]),ONE));cs[2]=encode(sub(ext(cs[2]),ONE));reject('identity preserving round',bad)
    bad=deepcopy(combined);bad['opening']['proof']['witness_commitment']['evals'][0]['c0']['c0']^=1;reject('final opening',bad)
    bad=deepcopy(combined);bad['opening']['evaluation_point'][0]['c0']['c0']^=1;reject('final point',bad)
    bad=deepcopy(combined);bad['shift_reduction']['rounds'][0].append(encode(ZERO));reject('excess degree',bad)
    badroot=root[:];badroot[0]^=1;reject('changed root',combined,badroot)
    # The logarithmic kernel is checked against its complete Boolean expansion.
    rng=random.Random(20261015);checks=0
    for n in range(1,7):
        for _ in range(3):
            point=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(n)]
            x=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(n)];expected=ZERO
            for j in range(2**n):
                bits=[base((j>>i)&1) for i in range(n)]
                prev=[base((((j-1)%2**n)>>i)&1) for i in range(n)]
                expected=add(expected,mul(reduction.eq_point(x,bits),reduction.eq_point(point,prev)))
            require(expected==reduction.shift_kernel(point,x),'shift kernel expansion');checks+=1
        data=[[rng.randrange(P) for _ in range(3)] for _ in range(2**n)]
        pt=Transcript([1,n]);point=pt.draw(n,True);pr,at,vals=reduction.prove(data,point,pt)
        vt=Transcript([1,n]);vp=vt.draw(n,True)
        require(reduction.verify(pr,vp,3,vt,[encode(v) for v in vals])==at and vt.seed==pt.seed,'dimension reduction')
    report={'status':'PASS','original_columns_authenticated':104,'current_claims':104,'cyclic_next_claims':104,
            'whir_verified':True,'verifier_witness_used':False,'mutations_rejected':len(rejected),
            'kernel_expansion_checks':checks,'generic_dimensions_tested':[1,2,3,4,5,6],
            'shift_weight_verifier_cost':'O(log rows), two field-state accumulators','sumcheck_degree':2,
            'upstream_commit':PIN,'limitations':['Fixed eight-row WHIR adapter; generic algebra tested through64rows.',
            'No AIR constraint or bus proof in this opening-only experiment.','Toy BLAKE2s/BabyBearExt4 profile, no PQ security claim.',
            'No complete Lean verifier/implementation refinement.'],
            'sha256':{str(p.relative_to(research)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                      [here/'shift_opening.py',here/'run_shift_whir.py',out/'direct-wasm-shift-proof.json']}}
    save('direct-wasm-shift-verified.json',report);print(json.dumps(report))
if __name__=='__main__':main()
