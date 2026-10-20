#!/usr/bin/env python3
"""PCS integration on exact exported D1 tables; not a state-transition proof."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import time
from copy import deepcopy
from constraint_sumcheck import encode
from verify_whir_toy import P,Transcript,require
from run_scheduled_whir import statement,checked_verify
from run_kernel import PIN


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('airbender',type=Path);ap.add_argument('trace_directory',type=Path)
    ap.add_argument('--tables',type=int,nargs='+',default=[0,16,18]);args=ap.parse_args()
    here=Path(__file__).resolve().parent;out=here.parent.parent/'results'/'actual-d1-pcs'
    out.mkdir(parents=True,exist_ok=True);repo=args.airbender.resolve()
    require(subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN,'upstream pin')
    subprocess.run(['git','diff','--exit-code','HEAD','--','prover','cs','field','fft','transcript','blake2s_u32'],cwd=repo,check=True)
    native=json.loads((args.trace_directory/'report.json').read_text());profiles=[]
    env=dict(os.environ,HEAVY_MEM='8G',CARGO_BUILD_JOBS='2')
    def save(path,data):path.write_text(json.dumps(data,separators=(',',':'))+'\n');return path
    def run(example,*paths):
        with (out/'run.log').open('a') as log:
            subprocess.run(['taskset','-c','8-15,24-31','/data/illia/nearproof-deps/bin/heavy',
                'cargo','run','-p','prover','--example',example,'--',*map(str,paths)],
                cwd=repo,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
    for index in args.tables:
        meta=native['tables'][index];source=args.trace_directory/meta['file'];raw=source.read_bytes()
        n,width=struct.unpack_from('<2I',raw);require(len(raw)==8+4*(1<<n)*width,'raw trace length')
        require(n==meta['log_rows'] and width==meta['width'],'native metadata')
        cells=struct.unpack_from('<'+'I'*((len(raw)-8)//4),raw,8)
        require(all(v<P for v in cells),'canonical trace')
        rows=[cells[r*width:(r+1)*width] for r in range(1<<n)]
        prefix=out/f'table-{index:02d}-{meta["name"]}'
        src=save(Path(str(prefix)+'-source.json'),{'rows':rows})
        commitment=Path(str(prefix)+'-commitment.json');started=time.monotonic()
        run('near_scheduled_commitment',src,commitment,'--root-only')
        cap=json.loads(commitment.read_text());require(cap['root_only'] and 'rows' not in cap and 'openings' not in cap,'root-only output')
        root=cap['root'];words=statement(root,n,width);t=Transcript(words);point=t.draw(n,True)
        handoff=save(Path(str(prefix)+'-handoff.json'),{'log_rows':n,'root':root,'statement_words':words,
            'pre_opening_seed':list(struct.unpack('<8I',t.seed)),'evaluation_point':[encode(v) for v in point]})
        proofpath=Path(str(prefix)+'-proof.json');run('near_scheduled_whir',src,proofpath,handoff)
        generation=time.monotonic()-started;proof=json.loads(proofpath.read_text());started=time.monotonic()
        checked_verify(proof,root,n,width);verification=time.monotonic()-started
        bad=deepcopy(proof);bad['proof']['witness_commitment']['evals'][0]['c0']['c0']^=1
        try:checked_verify(bad,root,n,width)
        except (ValueError,KeyError,TypeError,IndexError):pass
        else:raise AssertionError('altered opening accepted')
        result={'table':index,'name':meta['name'],'log_rows':n,'rows':1<<n,'width':width,
            'opening_format':proof['format'],'full_trace_disclosed':n==1,
            'binary_payload_bytes':proof['bincode_bytes'],'proof_json_bytes':proofpath.stat().st_size,
            'generation_seconds_including_subprocesses':generation,'verification_seconds':verification,
            'raw_trace_sha256':hashlib.sha256(raw).hexdigest(),'proof_sha256':hashlib.sha256(proofpath.read_bytes()).hexdigest(),
            'opening_verified':True,'mutated_claim_rejected':True}
        profiles.append(result);print(json.dumps(result),flush=True)
    save(out/'verified.json',{'status':'PASS','upstream_commit':PIN,'tables':profiles,
        'limitations':['Exact exported D1 table PCS openings only; no AIR or global bus proof.',
            'Diagnostic BLAKE2s/BabyBearExt4 profile without security-level claim.',
            'Two-row path discloses the full table; no zero-knowledge claim.',
            'Binary payload sizes are not complete state-transition proof sizes.']})


if __name__=='__main__':main()
