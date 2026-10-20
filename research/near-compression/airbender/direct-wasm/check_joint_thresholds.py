#!/usr/bin/env python3
"""Exact arithmetic only: no inferred proximity from a sampled PCS transcript."""
import argparse,hashlib,json
from pathlib import Path


def checks(d,t):
    n=4*d
    assert 0<d and 0<=t<=n
    near=2*(n-t)+d<=n
    far=2*n+d-1<3*t
    assert near==(5*d<=2*t)==((5*d+1)//2<=t)
    assert far==(3*d<=t)
    assert (near and far)==(3*d<=t)
    return dict(D=d,N=n,T=t,near_condition=near,far_condition=far,
                near_minimum=(5*d+1)//2,far_minimum=3*d,
                near_slack=n-(2*(n-t)+d),far_strict_slack=3*t-(2*n+d-1))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--accounting',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    account=json.loads(a.accounting.read_text());params=account['parameters']
    assert params['N']==4*params['D']
    current=checks(params['D'],params['T'])
    boundaries=[]
    for exponent in range(26):
        d=2**exponent;n=4*d
        for t in sorted({0,d,2*d,(5*d+1)//2-1,(5*d+1)//2,3*d-1,3*d,3*d+1,n}):
            if 0<=t<=n:boundaries.append(checks(d,t))
    report=dict(status='PASS',boundary_checks=len(boundaries),conditional_accounting=current,
                fullheight_rate_four_example=checks(262144,3*262144),
                excluded_examples=[checks(131072,2*131072),checks(131072,3*131072-1)],
                facts=['Near recovery requires T>=ceil(5D/2), i.e. agreement >=5/8 of N at rate four.',
                       'Existing far tensor condition requires T>=3D, i.e. agreement >=3/4 of N.',
                       f'Conditional accounting T={params["T"]}; minimum far threshold is {3*params["D"]}.',
                       'Threshold conditions are satisfiable but no runtime verifier check establishes T-agreement.',
                       'Q8 is a diagnostic query setting, not a certificate of either threshold or 128-bit security.'],
                security_certified=False,
                files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in [Path(__file__),a.accounting]])
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('files','facts')}))

if __name__=='__main__':main()
