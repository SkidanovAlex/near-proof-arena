#!/usr/bin/env python3
"""Concrete tower/flat-coordinate parity for packed polynomial evaluation."""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source-results',type=Path,required=True)
    ap.add_argument('--reference-directory',type=Path,required=True)
    ap.add_argument('--lean-directory',type=Path,required=True)
    ap.add_argument('--fixture',type=Path,required=True)
    ap.add_argument('--temporary-olean-directory',type=Path)
    ap.add_argument('--output-directory',type=Path,required=True)
    a=ap.parse_args();sys.path.insert(0,str(a.reference_directory))
    from verify_whir_toy import P,base,add,mul
    from packed_disclosure import prove_disclosure
    points=[(0,0,0,0),(1,0,0,0),(P-1,0,0,0),(0,1,0,0),(0,0,0,1),(13,27,41,59),(P-1,P-2,P-3,P-4)]
    inputs=[];expected=[]
    for c in json.loads((a.source_results/'inputs.json').read_text()):
        c={k:c[k] for k in ['n','p','width','rows']};c['points']=points;inputs.append(c)
        coeffs=prove_disclosure(c['rows'],2**c['p'])['coefficients']
        evaluated=[]
        for point in points:
            lanes=[]
            for coeff in coeffs:
                value=base(0)
                for word in reversed(coeff):value=add(base(word),mul(point,value))
                lanes.append(list(value))
            evaluated.append(lanes)
        expected.append(evaluated)
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    ip=out/'inputs.json';op=out/'lean-results.json';ip.write_text(json.dumps(inputs))
    command=['lake','env']
    if a.temporary_olean_directory:
        lp=subprocess.check_output(command+['printenv','LEAN_PATH'],cwd=a.lean_directory,text=True).strip()
        command+=['env','LEAN_PATH='+str(a.temporary_olean_directory)+':'+lp]
    subprocess.run(command+['lean','--run',str(a.fixture),str(ip),str(op)],cwd=a.lean_directory,check=True)
    assert json.loads(op.read_text())==expected
    files=[Path(__file__),a.fixture,ip,op,a.reference_directory/'verify_whir_toy.py',a.reference_directory/'packed_disclosure.py']
    report=dict(status='PASS',tables=len(inputs),points_per_table=len(points),nonbase_points_per_table=4,
                polynomial_evaluations=sum(len(xs) for table in expected for xs in table),
                files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files],
                limits=['Bounded flat-coordinate parity; formal embedding/evaluation theorems carry universal algebra.',
                        'No unknown-root extraction or cryptographic security conclusion.'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
