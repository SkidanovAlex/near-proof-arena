#!/usr/bin/env python3
"""Export actual Lean AIR and exercise pinned Airbender kernels; no proof generation."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN='129f827003b34acd64a3315a5863eac75bc09fe6'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('airbender',type=Path)
    parser.add_argument('--heavy',default='/data/illia/nearproof-deps/bin/heavy')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    research=here.parent.parent
    repo=args.airbender.resolve()
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN
    subprocess.run(['git','diff','--exit-code','HEAD','--','prover','cs','field'],cwd=repo,check=True)
    src=here/'near_wasm_kernel.rs';dst=repo/'prover/examples/near_wasm_kernel.rs'
    if dst.exists() and dst.read_bytes()!=src.read_bytes():
        raise SystemExit('Refusing to overwrite different example')
    dst.parent.mkdir(exist_ok=True);dst.write_bytes(src.read_bytes())
    export=research/'results/direct-wasm-air-export.json'
    with export.open('w') as out:
        subprocess.run([args.heavy,'lake','env','lean','--run','InstructionGKRExport.lean'],cwd=research,stdout=out,check=True)
    data=json.loads(export.read_text())
    assert len(data['constraints'])==106 and data['field_modulus']==2013265921
    report=research/'results/direct-wasm-airbender-kernel.json'
    log=research/'results/direct-wasm-airbender-kernel.log'
    with log.open('w') as out:
        subprocess.run([args.heavy,'cargo','run','-p','prover','--example','near_wasm_kernel','--',str(export),str(report)],cwd=repo,stdout=out,stderr=subprocess.STDOUT,check=True)
    result=json.loads(report.read_text())
    result['source_sha256']={str(p.relative_to(research)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [src,export,research/'InstructionGKRExport.lean']}
    result['log']=str(log)
    report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__':main()
