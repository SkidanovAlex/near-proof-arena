#!/usr/bin/env python3
"""Regenerate and independently verify toy WHIR openings at every n=1,2,3,4,7,10,13.

Artifacts live in research/near-compression/results. No witness is passed to the
independent verifier. Not an AIR proof, recursion or security-level benchmark.
"""
import argparse
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
from constraint_sumcheck import encode
from verify_whir_toy import P,Transcript,require
from verify_whir_scheduled import verify_with_handoff,schedule
from run_kernel import PIN


def statement(root,log_rows,width):
    profile=schedule(log_rows);folds=profile['whir_steps_schedule']
    return list(b'NEAR-SCHEDULED-WHIR-OPENING-EXPERIMENT-V1')+[log_rows,1<<log_rows,width,
        4,1,len(folds)]+folds+[8]*len(folds)+[4]*(len(folds)-1)+[0]*len(folds)+root


def checked_verify(artifact,root,log_rows,width):
    words=statement(root,log_rows,width)
    require(artifact['statement_words']==words,'scheduled statement encoding')
    require(type(artifact['log_rows'])is int and artifact['log_rows']==log_rows,'artifact dimension')
    t=Transcript(words);point=t.draw(log_rows,True)
    return verify_with_handoff(artifact,root,(t,point),width,log_rows)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('airbender',type=Path)
    ap.add_argument('--heavy',default='/data/illia/nearproof-deps/bin/heavy')
    args=ap.parse_args()
    here=Path(__file__).resolve().parent;research=here.parent.parent
    out=research/'results';out.mkdir(exist_ok=True)
    repo=args.airbender.resolve()
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()!=PIN:
        raise SystemExit('Upstream revision mismatch')
    subprocess.run(['git','diff','--exit-code','HEAD','--','prover','cs','field','fft','transcript','blake2s_u32'],cwd=repo,check=True)
    for name in ('near_scheduled_commitment.rs','near_scheduled_whir.rs'):
        source=here/name;target=repo/'prover/examples'/name
        if target.exists() and target.read_bytes()!=source.read_bytes():
            raise SystemExit('Different existing example: '+str(target))
        target.write_bytes(source.read_bytes())
    log_path=out/'scheduled-whir-run.log'
    environment=dict(os.environ,HEAVY_MEM='8G',CARGO_BUILD_JOBS='2')
    def run(example,*paths):
        with log_path.open('a') as log:
            subprocess.run(['taskset','-c','8-15,24-31',args.heavy,'cargo','run','-p','prover',
                            '--example',example,'--',*map(str,paths)],cwd=repo,env=environment,
                           stdout=log,stderr=subprocess.STDOUT,check=True)
    def save(name,data):
        path=out/name;path.write_text(json.dumps(data,indent=2)+'\n');return path
    profiles=[];all_rejections=[];artifacts=[]
    width=3
    for n in (1,2,3,4,7,10,13):
        prefix=f'scheduled-whir-n{n}'
        rows=[[r,(r*r+17)%P,(r*r*r+31*r+9)%P] for r in range(1<<n)]
        source=save(prefix+'-source.json',{'rows':rows})
        commitment=out/(prefix+'-commitment.json');run('near_scheduled_commitment',source,commitment)
        root=json.loads(commitment.read_text())['root']
        words=statement(root,n,width);t=Transcript(words);point=t.draw(n,True)
        handoff=save(prefix+'-handoff.json',{'log_rows':n,'root':root,'statement_words':words,
            'pre_opening_seed':list(struct.unpack('<8I',t.seed)),'evaluation_point':[encode(v) for v in point]})
        trusted=save(prefix+'-statement.json',{'root':root,'log_rows':n,'width':width})
        proof_path=out/(prefix+'-opening.json');run('near_scheduled_whir',source,proof_path,handoff)
        proof=json.loads(proof_path.read_text());checked_verify(proof,root,n,width)
        rejected=[]
        def reject(label,bad,r=root,dimension=n,w=width):
            try:checked_verify(bad,r,dimension,w)
            except (ValueError,KeyError,TypeError,IndexError):rejected.append(label)
            else:raise AssertionError(f'n{n}: accepted '+label)
        if n==1:
            final=[]
            for row in range(2):
                for c in range(width):
                    bad=deepcopy(proof);bad['proof']['rows'][row][c]^=1;reject('two-row disclosure mutation',bad)
            bad=deepcopy(proof);bad['proof']['rows'].pop();reject('missing disclosed row',bad)
            bad=deepcopy(proof);bad['format']='scheduled-whir-v1';reject('format confusion',bad)
        else:
            final=proof['proof']['final_monomials']
            require(len(final)==1<<(n-sum(schedule(n)["whir_steps_schedule"])),'terminal coefficient count')
            for index in range(len(final)):
                bad=deepcopy(proof);value=bad['proof']['final_monomials'][index]['c0']
                value['c0']=(value['c0']+1)%P
                reject('final coefficient '+str(index),bad)
            bad=deepcopy(proof);bad['proof']['final_monomials'].pop();reject('truncated final polynomial',bad)
            bad=deepcopy(proof);bad['evaluation_point'].pop();reject('short evaluation point',bad)
            bad=deepcopy(proof);bad['proof']['original_evaluation_point'].pop();reject('short original point',bad)
            for layer in ['base']+list(range(len(proof['proof']['intermediate_whir_oracles']))):
                bad=deepcopy(proof)
                queries=(bad['proof']['witness_commitment']['queries'] if layer=='base'
                         else bad['proof']['intermediate_whir_oracles'][layer]['queries'])
                queries[0]['index']^=1;reject(str(layer)+' query index',bad)
                bad=deepcopy(proof)
                queries=(bad['proof']['witness_commitment']['queries'] if layer=='base'
                         else bad['proof']['intermediate_whir_oracles'][layer]['queries'])
                queries[0]['path'][0][0]^=1;reject(str(layer)+' Merkle path',bad)
        bad=deepcopy(proof);bad['statement_words'][0]^=1;reject('statement words',bad)
        bad=deepcopy(proof);bad['log_rows']=n+1;reject('artifact log rows',bad)
        reject('wrong trusted log rows',proof,dimension=n+1 if n<13 else n-1)
        reject('wrong trusted width',proof,w=width+1)
        wrong_root=root.copy();wrong_root[0]^=1;reject('wrong trusted commitment',proof,r=wrong_root)
        profile={'log_rows':n,'rows':1<<n,'width':width,'final_coefficients':len(final),'opening_format':proof['format'],
                 'bincode_bytes':proof['bincode_bytes'],'negatives_rejected':len(rejected),
                 'external_verifier_witness_used':False,'full_trace_disclosed':n==1}
        profiles.append(profile);all_rejections.extend(f'n{n}: {s}' for s in rejected)
        artifacts.extend([source,commitment,handoff,trusted,proof_path,Path(str(proof_path)+'.bin')])
        print(json.dumps(profile),flush=True)
    sources=[here/name for name in ('run_scheduled_whir.py','near_scheduled_commitment.rs',
        'near_scheduled_whir.rs','verify_whir_scheduled.py')]
    report={'status':'PASS','upstream_commit':PIN,'profiles':profiles,
            'honest_proofs_accepted':len(profiles),'mutations_rejected':len(all_rejections),
            'external_verifier_witness_used':False,'rejected_cases':all_rejections,
            'limitations':['Toy dimension-derived BLAKE2s/BabyBearExt4 PCS opening profile; no security level claimed.',
                          'Two-row tables explicitly disclose all source rows; not zero knowledge.',
                          'No AIR constraints, buses, recursion or full NEAR state-transition proof.',
                          'Serialized opening sizes are not full-protocol proof sizes.'],
            'sha256':{str(path.relative_to(research)):hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in sources+artifacts}}
    save('scheduled-whir-verified.json',report)
    print(json.dumps({'status':'PASS','profiles':len(profiles),'mutations_rejected':len(all_rejections)}))


if __name__=='__main__':main()
