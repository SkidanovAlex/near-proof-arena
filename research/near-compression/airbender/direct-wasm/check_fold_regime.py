#!/usr/bin/env python3
import argparse,hashlib,json
from fractions import Fraction
from pathlib import Path


def check(d,t):
    n=4*d;assert d>0 and 0<=t<=n
    near=2*(n-t)+d<=n;tensor=2*n+d-1<3*t;fold=2*n+d<3*t
    assert fold==(t>=3*d+1)
    assert (near and tensor and fold)==(t>=3*d+1)
    return dict(D=d,N=n,T=t,near=near,tensor=tensor,fold=fold,minimum_combined=3*d+1,
                fold_strict_slack=3*t-(2*n+d))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--accounting',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    parameters=json.loads(a.accounting.read_text())['parameters'];assert parameters['N']==4*parameters['D']
    checked=0
    for exponent in range(26):
        d=2**exponent
        for t in sorted({0,2*d,(5*d+1)//2,3*d-1,3*d,3*d+1,4*d}):check(d,t);checked+=1
    current=check(parameters['D'],parameters['T'])
    tail=Fraction(current['T']-1,current['N'])**8
    report=dict(status='PASS',boundary_checks=checked,current_conditional_parameters=current,
                fullheight_boundary=[check(262144,786432),check(262144,786433)],
                conditional_query_tail_Q8=dict(numerator=tail.numerator,denominator=tail.denominator),
                limits=['The prior tensor inequality has -1; folding inequality does not. Its minimum T is one larger.',
                        'Query fraction is a conditional counting term, not demonstrated protocol security or an attack success probability.',
                        'Acceptance-to-fixed-oracles, adaptive strategy causality and FS/QROM correspondence remain explicit.'],
                security_certified=False,
                files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in [Path(__file__),a.accounting]])
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
