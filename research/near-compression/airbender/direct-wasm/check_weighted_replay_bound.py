#!/usr/bin/env python3
"""Conditional arithmetic of the proved replay count; no FS/security certification."""
import argparse,hashlib,json
from fractions import Fraction
from pathlib import Path


def fraction(x):
    return dict(numerator=x.numerator,denominator=x.denominator)


def case(d,t,p,q):
    n=d.bit_length()-1;assert d==2**n and d>0
    N=4*d;assert 0<t<=N and 2*N+d<3*t
    sizes=[N//2**i for i in range(n+1)]
    error=sum(max(sizes[i+1],2) for i in range(n))
    assert error==N-4
    field=Fraction(error,p**4);query=Fraction(t-1,N)**q
    bits=0
    if error:
        while field*2**(bits+1)<=1:bits+=1
    return dict(D=d,N=N,T=t,fold_rounds=n,queries=q,E=error,
                ideal_field_cardinality=p**4,extraction_term=fraction(field),query_term=fraction(query),
                total_conditional_term=fraction(field+query),isolated_extraction_integer_bits=bits,
                this_bound_certifies_128_bits=field+query<=Fraction(1,2**128))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--accounting',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    params=json.loads(a.accounting.read_text())['parameters'];assert params['N']==4*params['D']
    report=dict(status='PASS',current=case(params['D'],params['T'],params['p'],8),
                fullheight=case(262144,786433,params['p'],8),
                limits=['The listed field cardinality and independent sampling instantiate an ideal finite experiment only.',
                        'These sufficient bounds do not certify128-bit security; failure to certify is not an attack or an upper bound on actual security.',
                        'Root binding, FS/QROM and upstream GKR/AIR/bus errors are excluded.'],security_certified=False,
                files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in [Path(__file__),a.accounting]])
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({key:{name:report[key][name] for name in ('D','N','T','E','isolated_extraction_integer_bits','this_bound_certifies_128_bits')} for key in ('current','fullheight')}))

if __name__=='__main__':main()
