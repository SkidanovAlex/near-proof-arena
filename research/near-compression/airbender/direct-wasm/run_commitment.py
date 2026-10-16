#!/usr/bin/env python3
"""Reproduce the pinned direct-Wasm RS commitment and independent diagnostic."""
import argparse,json,subprocess,hashlib
from pathlib import Path
PIN='129f827003b34acd64a3315a5863eac75bc09fe6'
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('airbender',type=Path);p.add_argument('--heavy',default='/data/illia/nearproof-deps/bin/heavy');a=p.parse_args()
    here=Path(__file__).resolve().parent;research=here.parent.parent;repo=a.airbender.resolve()
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN
    subprocess.run(['git','diff','--exit-code','HEAD','--','prover','field','fft'],cwd=repo,check=True)
    src=here/'near_wasm_commitment.rs';dst=repo/'prover/examples'/src.name
    if dst.exists() and dst.read_bytes()!=src.read_bytes():raise SystemExit('Different existing example')
    dst.parent.mkdir(exist_ok=True);dst.write_bytes(src.read_bytes())
    export=research/'results/direct-wasm-air-export.json'
    with export.open('w') as out:subprocess.run([a.heavy,'lake','env','lean','--run','InstructionGKRExport.lean'],cwd=research,stdout=out,check=True)
    data=research/'results/direct-wasm-commitment-data.json';report=research/'results/direct-wasm-commitment-check.json';log=research/'results/direct-wasm-commitment.log'
    with log.open('w') as out:subprocess.run([a.heavy,'cargo','run','-p','prover','--example','near_wasm_commitment','--',str(export),str(data)],cwd=repo,stdout=out,stderr=subprocess.STDOUT,check=True)
    subprocess.run(['python3',str(here/'check_commitment.py'),str(data),str(export),str(report)],check=True)
    result=json.loads(report.read_text());result['upstream_commit']=PIN
    result['sha256'][str(src)]=hashlib.sha256(src.read_bytes()).hexdigest()
    result['integration_note']='Full-round tree selected explicitly; upstream associated leaf verifier uses global reduced-round setting and is not used by this independent checker.'
    result['log']=str(log);report.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
