"""Canonical Lean-export length/framing boundary tests; no extra trace proofs."""
import argparse,hashlib,json,subprocess
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--lean-project',required=True);p.add_argument('--exporter',required=True);p.add_argument('--output-directory',required=True);a=p.parse_args();out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);results=[]
    cases=[('min',1,[[0,0]],True),('max',1024,[[0,0],[1023,0]],True),('zero',0,[],False),('too-long',1025,[],False),('duplicate',2,[[0,0],[0,0]],False),('unsorted',2,[[1,0],[0,0]],False),('index-bound',2,[[2,0]],False),('byte-bound',2,[[0,256]],False)]
    for name,n,fixed,valid in cases:
        d=out/name;d.mkdir(exist_ok=True);(d/'message.bin').write_bytes(bytes(n));(d/'fixed.json').write_text(json.dumps(fixed))
        result=subprocess.run(['lake','env','lean','--run',a.exporter,str(d/'message.bin'),str(d/'fixed.json'),str(d/'spec.json')],cwd=a.lean_project,capture_output=True,text=True);assert (result.returncode==0)==valid,(name,result.stderr,result.stdout)
        if valid:
            spec=json.loads((d/'spec.json').read_text());assert spec['air']['tables'][2]['width']==8*n and spec['log_rows'][2]==1;assert spec['public'][:48]==list(hashlib.sha384(bytes(n)).digest())
        (d/'export.log').write_text(result.stdout+result.stderr);results.append(dict(case=name,length=n,accepted=valid))
    report=dict(status='PASS',cases=results,scope='Canonical exporter/profile bounds only; min/max synthetic bytes are not claimed as proved workload cases.')
    (out/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
