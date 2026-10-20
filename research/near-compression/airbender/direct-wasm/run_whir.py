#!/usr/bin/env python3
"""Generate and independently verify the fixed toy WHIR opening profile."""
import argparse,subprocess,json,hashlib
from pathlib import Path

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('airbender',type=Path);p.add_argument('--heavy',default='/data/illia/nearproof-deps/bin/heavy');a=p.parse_args()
    here=Path(__file__).resolve().parent;root=here.parent.parent;repo=a.airbender.resolve()
    # Regenerate original Lean witness and independently check its commitment;
    # this runner also pins the upstream commit and checks tracked source edits.
    subprocess.run(['python3',str(here/'run_commitment.py'),str(repo),'--heavy',a.heavy],check=True)
    src=here/'near_wasm_whir.rs';dst=repo/'prover/examples'/src.name
    if dst.exists() and dst.read_bytes()!=src.read_bytes():raise SystemExit('Different existing example')
    dst.write_bytes(src.read_bytes())
    export=root/'results/direct-wasm-air-export.json';artifact=root/'results/direct-wasm-whir-opening.json'
    log=root/'results/direct-wasm-whir.log';report=root/'results/direct-wasm-whir-handoff-check.json'
    with log.open('w') as out:subprocess.run([a.heavy,'cargo','run','-p','prover','--example','near_wasm_whir','--',str(export),str(artifact)],cwd=repo,stdout=out,stderr=subprocess.STDOUT,check=True)
    subprocess.run(['python3',str(here/'check_whir_handoff.py'),str(artifact),str(export),str(root/'results/direct-wasm-commitment-data.json'),str(report)],check=True)
    result=json.loads(report.read_text());result['sha256']={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [src,here/'check_whir_handoff.py',artifact]};result['log']=str(log)
    report.write_text(json.dumps(result,indent=2)+'\n')
    statement=root/'results/direct-wasm-whir-statement.json'
    statement.write_text(json.dumps({'root':json.loads((root/'results/direct-wasm-commitment-data.json').read_text())['root']},indent=2)+'\n')
    subprocess.run(['python3',str(here/'verify_whir_toy.py'),str(artifact),str(statement),str(root/'results/direct-wasm-whir-verified.json')],check=True)
    subprocess.run(['python3',str(here/'test_whir_toy.py'),str(artifact),str(statement),str(root/'results/direct-wasm-whir-negative-tests.json')],check=True)

if __name__=='__main__':main()
