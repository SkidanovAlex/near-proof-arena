#!/usr/bin/env python3
"""Reproduce toy direct instruction constraint proof, including invalid fresh witness."""
import argparse,json,subprocess,struct,hashlib
from copy import deepcopy
from pathlib import Path
from constraint_sumcheck import specification,prove_sumcheck,verify,begin,ext,poly,ZERO,ONE,add,encode
from verify_whir_toy import _verify_with_handoff

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('airbender',type=Path)
    ap.add_argument('--heavy',default='/data/illia/nearproof-deps/bin/heavy');a=ap.parse_args()
    here=Path(__file__).resolve().parent;research=here.parent.parent;out=research/'results';repo=a.airbender.resolve()
    subprocess.run(['python3',str(here/'run_commitment.py'),str(repo),'--heavy',a.heavy],check=True)
    src=here/'near_wasm_constraint_whir.rs';dst=repo/'prover/examples'/src.name
    if dst.exists() and dst.read_bytes()!=src.read_bytes():raise SystemExit('Different existing example')
    dst.write_bytes(src.read_bytes())
    def read(name):return json.loads((out/name).read_text())
    def save(name,value):
        path=out/name;path.write_text(json.dumps(value,indent=2)+'\n');return path
    def run(example,*args):
        with (out/(example+'-constraint-run.log')).open('a') as log:
            subprocess.run([a.heavy,'cargo','run','-p','prover','--example',example,'--',*map(str,args)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,check=True)
    source=read('direct-wasm-air-export.json');spec=specification(source)
    root=read('direct-wasm-commitment-data.json')['root'];save('direct-wasm-constraint-spec.json',spec)
    save('direct-wasm-constraint-statement.json',{'root':root})
    def generate(prefix,export,cap):
        rounds,handoff=prove_sumcheck(spec,cap,export['rows'])
        ep=save(prefix+'-export.json',export);hp=save(prefix+'-handoff.json',handoff)
        op=out/(prefix+'-opening.json');run('near_wasm_constraint_whir',ep,op,hp)
        proof={'constraint_sumcheck':rounds,'opening':json.loads(op.read_text())}
        save(prefix+'-proof.json',proof);return proof
    proof=generate('direct-wasm-constraint',source,root)
    verify(proof,spec,root)
    rejected=[]
    def reject(label,bad,s=spec,r=root):
        try:verify(bad,s,r)
        except (ValueError,TypeError,KeyError,IndexError):rejected.append(label)
        else:raise AssertionError('Accepted '+label)
    for i in range(3):
        for j in range(4):
            bad=deepcopy(proof);bad['constraint_sumcheck'][i][j]['c0']['c0']^=1
            reject(f'coefficient {i}/{j}',bad)
    # A nonzero perturbation q(X)+X-X² preserves q(0)+q(1).
    bad=deepcopy(proof);cs=bad['constraint_sumcheck'][0]
    from constraint_sumcheck import sub
    cs[1]=encode(add(ext(cs[1]),ONE));cs[2]=encode(sub(ext(cs[2]),ONE))
    reject('identity preserving polynomial mutation',bad)
    for i in range(104):
        bad=deepcopy(proof);bad['opening']['proof']['witness_commitment']['evals'][i]['c0']['c0']^=1
        reject(f'opening claim {i}',bad)
    bad=deepcopy(proof);bad['opening']['evaluation_point'][0]['c0']['c0']^=1;reject('opening point',bad)
    bad=deepcopy(proof);bad['opening']['statement_words'][0]^=1;reject('statement',bad)
    bad=deepcopy(proof);bad['constraint_sumcheck'].pop();reject('missing round',bad)
    bad=deepcopy(proof);bad['constraint_sumcheck'][0].append(encode(ZERO));reject('excess degree',bad)
    bad=deepcopy(proof);bad['opening']['proof']['witness_commitment']['queries'][0]['path'][0][0]^=1;reject('Merkle path',bad)
    badspec=deepcopy(spec);badspec['constraints'][0]={'const':0};reject('changed expected constraints',proof,badspec)
    badroot=root[:];badroot[0]^=1;reject('changed expected root',proof,r=badroot)
    # Recommit an invalid trace and generate a fully consistent WHIR opening.
    invalid=deepcopy(source);invalid['rows'][0][4]=1
    ip=save('direct-wasm-invalid-export.json',invalid);cp=out/'direct-wasm-invalid-commitment.json'
    run('near_wasm_commitment',ip,cp);invalidroot=json.loads(cp.read_text())['root']
    invalidproof=generate('direct-wasm-invalid-constraint',invalid,invalidroot)
    # Opening alone must accept; the constraint identity must reject.
    _,t,_,_=begin(spec,invalidroot);point=[]
    for cs in invalidproof['constraint_sumcheck']:
        t.commit_ext(cs);point.append(t.draw(1,True)[0])
    _verify_with_handoff(invalidproof['opening'],invalidroot,(t,point))
    reject('fresh invalid witness with valid opening',invalidproof,r=invalidroot)
    bad=deepcopy(proof);bad['opening']=invalidproof['opening'];reject('cross proof opening splice',bad)
    # A deliberately false zero sumcheck is rejected at terminal constraints.
    bad=deepcopy(invalidproof);bad['constraint_sumcheck']=[[encode(ZERO)]*4 for _ in range(3)]
    reject('invalid witness zero residual shortcut',bad,r=invalidroot)
    report={'status':'PASS','honest_combined_proofs_accepted':1,'mutations_rejected':len(rejected),
            'fresh_invalid_witness_opening_valid':True,'fresh_invalid_witness_constraint_proof_rejected':True,
            'verifier_witness_used':False,'rows':8,'columns':104,'constraints':106,
            'sumcheck_rounds':3,'degree_per_round':3,'rejected_cases':rejected,
            'whir_bincode_bytes':proof['opening']['bincode_bytes'],
            'sumcheck_field_payload_bytes':3*4*16,
            'limitations':['Fixed toy parameters; no security-level claim.','Constraint satisfaction only: no public operand binding, program/control/memory/gas/host execution proof.',
                           'No recursive aggregation or full NEAR transition proof.','Python/Rust verifier and transcript not formally refined to Lean.'],
            'sha256':{str(p.relative_to(research)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                      [here/'constraint_sumcheck.py',here/'run_constraint_whir.py',src,out/'direct-wasm-constraint-proof.json',out/'direct-wasm-constraint-spec.json']}}
    save('direct-wasm-constraint-verified.json',report)
    print(json.dumps({k:v for k,v in report.items() if k not in ('rejected_cases','sha256')}))
if __name__=='__main__':main()
