#!/usr/bin/env python3
"""Bind eight public (a,b,c) instruction claims to the toy committed witness.
The verifier checks proof/spec/root only, never the private rows. No PQ claim.
"""
import argparse,json,subprocess,hashlib
from pathlib import Path
from copy import deepcopy
from constraint_sumcheck import specification,prove_sumcheck,verify,begin,batched,base,ONE,ZERO
from verify_whir_toy import _verify_with_handoff
from run_kernel import PIN

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
    def read(name):return json.loads((out/name).read_text())
    def save(name,value):
        path=out/name;path.write_text(json.dumps(value,indent=2)+'\n');return path
    def run(example,*args):
        with (out/'direct-wasm-public-constraint-run.log').open('a') as log:
            subprocess.run([a.heavy,'cargo','run','-p','prover','--example',example,'--',*map(str,args)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,check=True)
    source=read('direct-wasm-air-export.json')
    # Fixture claim calculated from public operands, not witness result columns.
    public=[[a,b,(a+b)%2**32] for a,b in source['inputs']]
    spec=specification(source,public);save('direct-wasm-public-constraint-spec.json',spec)
    def generate(prefix,export):
        ep=save(prefix+'-export.json',export);cp=out/(prefix+'-commitment.json')
        run('near_wasm_commitment',ep,cp);root=json.loads(cp.read_text())['root']
        rounds,handoff=prove_sumcheck(spec,root,export['rows']);hp=save(prefix+'-handoff.json',handoff)
        op=out/(prefix+'-opening.json');run('near_wasm_constraint_whir',ep,op,hp)
        proof={'constraint_sumcheck':rounds,'opening':json.loads(op.read_text())}
        save(prefix+'-proof.json',proof);save(prefix+'-statement.json',{'root':root})
        return proof,root
    proof,root=generate('direct-wasm-public-constraint',source);verify(proof,spec,root)
    rejected=[]
    def reject(label,bad,s=spec,r=root):
        try:verify(bad,s,r)
        except (ValueError,KeyError,TypeError,IndexError):rejected.append(label)
        else:raise AssertionError('Accepted '+label)
    for i in range(8):
        for j in range(3):
            bad=deepcopy(spec);bad['public_instructions'][i][j]^=1
            reject(f'expected public row {i} component {j}',proof,bad)
    for value in (-1,2**32,True):
        bad=deepcopy(spec);bad['public_instructions'][0][0]=value
        reject('noncanonical public value '+str(value),proof,bad)
    bad=deepcopy(spec);bad['public_instructions'].pop();reject('missing public row',proof,bad)
    bad=deepcopy(proof);bad['opening']['statement_words'][0]^=1;reject('public statement bytes',bad)
    # Swap two valid addition rows: every local instruction remains correct,
    # but the committed witness no longer matches the public instruction order.
    swapped=deepcopy(source);swapped['rows'][0],swapped['rows'][1]=swapped['rows'][1],swapped['rows'][0]
    from constraint_sumcheck import evaluate
    if any(evaluate(e,[base(v) for v in row])!=ZERO for row in swapped['rows'] for e in spec['constraints']):
        raise AssertionError('Expected locally valid swapped rows')
    wrong,wrongroot=generate('direct-wasm-public-swapped',swapped)
    _,t,_,_=begin(spec,wrongroot);point=[]
    for cs in wrong['constraint_sumcheck']:
        t.commit_ext(cs);point.append(t.draw(1,True)[0])
    _verify_with_handoff(wrong['opening'],wrongroot,(t,point))
    reject('valid instructions in wrong public order',wrong,r=wrongroot)
    # Existing constraint-only proofs must not verify under the public profile.
    reject('constraint-only proof substituted',read('direct-wasm-constraint-proof.json'))
    report={'status':'PASS','honest_proofs_accepted':1,'mutations_rejected':len(rejected),
            'swapped_rows_satisfy_all_local_constraints':True,'swapped_rows_whir_opening_verified':True,
            'swapped_rows_public_binding_rejected':True,'verifier_witness_used':False,
            'public_instruction_count':8,'public_limb_binding_constraints':6,'local_constraints':106,
            'sumcheck_rounds':3,'sumcheck_degree_bound':3,'upstream_commit':PIN,
            'limitations':['Toy BLAKE2s/BabyBearExt4 profile; no quantum-security claim.',
            'Public independent additions only, no program/stack/memory/control/gas/host-state transition.',
            'No formal refinement of this Python/Rust protocol to Lean.'],
            'rejected_cases':rejected,
            'sha256':{str(p.relative_to(research)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
            [here/'constraint_sumcheck.py',here/'run_public_constraint_whir.py',out/'direct-wasm-public-constraint-spec.json',out/'direct-wasm-public-constraint-proof.json']}}
    save('direct-wasm-public-constraint-verified.json',report)
    print(json.dumps({k:v for k,v in report.items() if k not in ('sha256','rejected_cases')}))
if __name__=='__main__':main()
