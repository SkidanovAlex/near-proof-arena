#!/usr/bin/env python3
"""Reproduce canonical source table-local proof with authenticated next rows."""
import argparse,json,subprocess,hashlib
from pathlib import Path
from copy import deepcopy
import table_constraint_whir as tableproof
from table_constraint_whir import P,ZERO,ONE,ext,encode,add,sub
import shift_opening as shift
from verify_whir_toy import _verify_with_handoff
from reference import evaluate
from run_kernel import PIN

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('airbender',type=Path)
    ap.add_argument('--heavy',default='/data/illia/nearproof-deps/bin/heavy');a=ap.parse_args()
    here=Path(__file__).resolve().parent;research=here.parent.parent;out=research/'results';repo=a.airbender.resolve()
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()!=PIN:raise SystemExit('Upstream revision mismatch')
    subprocess.run(['git','diff','--exit-code','HEAD','--','prover','cs','field','fft','transcript','blake2s_u32'],cwd=repo,check=True)
    for name in ('near_air_commitment.rs','near_air_table_whir.rs'):
        src=here/name;dst=repo/'prover/examples'/name
        if dst.exists() and dst.read_bytes()!=src.read_bytes():raise SystemExit('Different existing example')
        dst.write_bytes(src.read_bytes())
    fixture_source=here.parent/'generic-air/TableFixture.lean'
    completed=subprocess.run([a.heavy,'lake','env','lean','--run',str(fixture_source)],cwd=research,text=True,capture_output=True,check=True)
    fixture=json.loads(completed.stdout);assert fixture['field_modulus']==P
    def save(name,x):
        p=out/name;p.write_text(json.dumps(x,indent=2)+'\n');return p
    save('generic-air-table-fixture.json',fixture)
    def run(example,*args):
        with (out/'generic-air-table-run.log').open('a') as log:
            subprocess.run([a.heavy,'cargo','run','-p','prover','--example',example,'--',*map(str,args)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,check=True)
    # Reference source-language parity on every cell/constraint of all cases.
    table=fixture['air']['tables'][0];comparisons=0
    for case in fixture['cases']:
        for i,row in enumerate(case['rows']):
            for j,e in enumerate(table['constraints']):
                assert evaluate(e,case['rows'],i,case['public'])==case['residuals'][i][j]
                comparisons+=1
    spec=tableproof.specification(fixture);save('generic-air-table-spec.json',spec)
    def generate(label,rows,spec):
        ep=save(label+'-witness.json',{'rows':rows});cp=out/(label+'-commitment.json')
        run('near_air_commitment',ep,cp);root=json.loads(cp.read_text())['root']
        proof,handoff=tableproof.prove(spec,root,rows);hp=save(label+'-handoff.json',handoff)
        op=out/(label+'-opening.json');run('near_air_table_whir',ep,op,hp)
        proof['opening']=json.loads(op.read_text());save(label+'-proof.json',proof)
        save(label+'-statement.json',{'root':root});return proof,root
    proof,root=generate('generic-air-table',fixture['rows'],spec);tableproof.verify(proof,spec,root)
    assert any(ext(cs[-1])!=ZERO for cs in proof['constraint_rounds']),'degree17 term must be exercised'
    rejected=[]
    def reject(label,bad,s=spec,r=root):
        try:tableproof.verify(bad,s,r)
        except (ValueError,KeyError,TypeError,IndexError):rejected.append(label)
        else:raise AssertionError('Accepted '+label)
    for i in range(3):
        for j in range(18):
            bad=deepcopy(proof);bad['constraint_rounds'][i][j]['c0']['c0']^=1;reject(f'round{i}coef{j}',bad)
    bad=deepcopy(proof);cs=bad['constraint_rounds'][0]
    cs[1]=encode(add(ext(cs[1]),ONE));cs[2]=encode(sub(ext(cs[2]),ONE));reject('identity preserving mutation',bad)
    for name in ('current_evals','next_evals'):
        for i in range(2):
            bad=deepcopy(proof);bad['shift_reduction'][name][i]['c0']['c0']^=1;reject(f'{name}{i}',bad)
    bad=deepcopy(proof);bad['constraint_rounds'][0].pop();reject('degree downgrade',bad)
    bad=deepcopy(proof);bad['opening']['proof']['witness_commitment']['queries'][0]['path'][0][0]^=1;reject('opening path',bad)
    badspec=deepcopy(spec);badspec['public'][0]^=1;reject('expected public input',proof,badspec)
    badspec=deepcopy(spec);badspec['air']['tables'][0]['constraints'][0]=['c',0];reject('expected AIR substitution',proof,badspec)
    badroot=root[:];badroot[0]^=1;reject('expected root',proof,r=badroot)
    # Invalid source trace receives a genuine current/next opening proof.
    invalidcase=fixture['cases'][1];invalid,ir=generate('generic-air-table-invalid',invalidcase['rows'],spec)
    _,t,_,_=tableproof.begin(spec,ir);point=[]
    for cs in invalid['constraint_rounds']:
        t.commit_ext(cs);point.append(t.draw(1,True)[0])
    opening=invalid['opening'];at=shift.verify(invalid['shift_reduction'],point,2,t,opening['proof']['witness_commitment']['evals'])
    _verify_with_handoff(opening,ir,(t,at),width=2)
    reject('fresh invalid witness with valid next/WHIR proof',invalid,r=ir)
    alternate=fixture['cases'][2];alt_spec=deepcopy(spec);alt_spec['public']=alternate['public']
    alt,ar=generate('generic-air-table-alternate',alternate['rows'],alt_spec);tableproof.verify(alt,alt_spec,ar)
    reject('valid proof for different public statement',alt,r=ar)
    report={'status':'PASS','honest_table_proofs_accepted':2,'mutations_rejected':len(rejected),
            'source_lean_residual_comparisons':comparisons,'source_constraints':len(table['constraints']),
            'source_max_degree':16,'zerocheck_max_degree':17,'nonzero_degree17_coefficient_exercised':True,
            'table_rows':8,'table_columns':2,'current_and_cyclic_next_authenticated':True,
            'fresh_invalid_trace_opening_verified':True,'fresh_invalid_trace_constraint_proof_rejected':True,
            'verifier_witness_used':False,'protocol_stages':['canonical AIR zerocheck','current/cyclic-next reduction','original-column WHIR opening'],
            'limitations':['Table-local proof only. Declared interactions do not imply bus balance or HoldsP.',
            'Fixed8row toy PCS; no PQ security or production proof-size claim.',
            'No full Lean verifier implementation refinement or full NEAR state-transition proof.'],
            'upstream_commit':PIN,
            'sha256':{str(p.relative_to(research)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                       [here/'table_constraint_whir.py',here/'run_table_constraint_whir.py',here/'near_air_commitment.rs',here/'near_air_table_whir.rs',here/'verify_whir_toy.py',fixture_source,out/'generic-air-table-proof.json']}}
    save('generic-air-table-verified.json',report);print(json.dumps(report))
if __name__=='__main__':main()
