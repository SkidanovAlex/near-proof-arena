"""Exact conditional error ledger; not a protocol soundness theorem.
BCSS25 Theorem4.6, PDF2025-11-11, uses m=ceil(sqrt(rho)/eta).
Ordinary Theorem1.5 uses ceil(sqrt(rho)/(2eta)); do not substitute it.
"""
import hashlib
import json
import math
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction as F
from pathlib import Path
from pq384_ext8_reference import P

ROOT=Path(__file__).resolve().parents[2]


def ceil(x):return -(-x.numerator//x.denominator)


def mca(degree,rate):
    n=degree*rate
    # Paper uses maximum degree k, not dimension k+1.
    rho=F(degree-1,n)
    scale=1<<64
    root=math.isqrt(rho.numerator*scale*scale//rho.denominator)
    lo,hi=F(root,scale),F(root+1,scale)
    assert lo*lo<=rho<hi*hi
    agreement=F(21,20*math.isqrt(rate));gamma=1-agreement
    assert 0<lo<hi<agreement<1
    # Increasing sqrt(rho) increases sqrt(rho)/(agreement-sqrt(rho)).
    m=max(ceil(hi/(agreement-hi)),3)
    assert ceil(lo/(agreement-lo))==m  # bracket pins the integer exactly
    t=F(2*m+1,2)
    # Exact upper bound: denominator uses lower sqrt; all other terms exact.
    bound=(2*t**5+3*t*gamma*rho)*n/(3*lo**3)+t/lo
    # Independent high-precision evaluation checks transcription and enclosure.
    with localcontext() as ctx:
        ctx.prec=100
        dec=lambda x:Decimal(x.numerator)/Decimal(x.denominator)
        root_decimal=dec(rho).sqrt()
        m_decimal=max(int((root_decimal/(dec(agreement)-root_decimal)).to_integral_value(rounding=ROUND_CEILING)),3)
        assert m_decimal==m
        td=Decimal(m)+Decimal('0.5')
        direct=(2*td**5+3*td*dec(gamma)*dec(rho))*n/(3*root_decimal**3)+td/root_decimal
        assert dec(bound)>=direct
        assert dec(bound)/direct-1<Decimal('1e-15')
    # Upstream leading-only expression, nominal dimension/rate, m=10.
    upstream=F(2,3)*F(21,2)**5*degree*rate**2*math.isqrt(rate)
    return bound,dict(degree=degree,domain=n,m=m,
        exception_count_upper_ceil=ceil(bound),
        full_to_upstream_leading_ratio=float(bound/upstream))


def bits(x):return math.log2(x.denominator)-math.log2(x.numerator)


def main():
    source=ROOT/'results/weighted-code-switch-screen.json'
    schedules=json.loads(source.read_text());records=[]
    for record in schedules['results']:
        if record['regime']!='johnson':continue
        path=record['best']['path'];terms=[]
        for s in path:
            degree,rate,k,q=s['degree'],s['rate'],s['skipped'],s['queries']
            # Hypothetical binary virtual-fold application; actual protocol bridge open.
            folding=[];fold_count=F(0)
            for i in range(k):
                count,detail=mca(degree//(1<<i),rate)
                fold_count+=count;folding.append(detail)
            next_degree=degree//(1<<k);L=10*s['next_rate']
            # Single OOD sample, target-list pair separation; mixture uses
            # conservative count1+q*2^k, including full queried cosets.
            ood=F(L*(L-1),2)*(next_degree-1)
            mixing=L*(1+q*(1<<k))
            sumcheck=2*(10*rate)*k
            query=F(21,20*math.isqrt(rate))**q
            terms.append(dict(folds=folding,mca=fold_count,ood=ood,
                              mixing=F(mixing),sumcheck=F(sumcheck),query=query))
        numerator=sum((t[key] for t in terms for key in ('mca','ood','mixing','sumcheck')),F(0))
        query=sum((t['query'] for t in terms),F(0))
        fields=[]
        for extension in (8,12):
            algebra=numerator/P**extension;partial=algebra+query
            fields.append(dict(extension=extension,algebra_only_bits=bits(algebra),
                               partial_ledger_bits=bits(partial),
                               partial_meets_128=partial<=F(1,2**128),
                               partial_meets_192=partial<=F(1,2**192),
                               partial_meets_214=partial<=F(1,2**214)))
        # Serialize fractions as exact strings, with bits only for presentation.
        rows=[]
        for t in terms:
            rows.append({key:str(value) if isinstance(value,F) else value for key,value in t.items()})
        records.append(dict(query_bits_per_stage=record['query_bits_per_stage'],stages=rows,
                            algebra_numerator=str(numerator),query_sum_bits=bits(query),fields=fields))
    report=dict(status='PARTIAL_CONDITIONAL_LEDGER_NOT_SECURITY_CERTIFICATE',records=records,
        schedule_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        paper_url='https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf',
        paper_sha256='4added3e55b83c15fcc8a698fb57e137f5bd83e79ea25ce79382817c1ad26a46',
        theorem='4.6, printed pages28-29; m=ceil(sqrt(rho)/eta), full lower-order terms',
        assumptions=['Each virtual fold satisfies Theorem4.6 with M=1 and degree bound degree-1.',
                     'Johnson target list bound10*nextRate is available before OOD and mixing.',
                     'OOD, mixing and sumcheck terms transfer to the proposed weighted protocol.',
                     'Stages compose by a union bound with independent uniform challenges.'],
        excluded=['Proofs of every assumption above, including functional preservation and weighted source extraction.',
                  'Local/GKR/bus and initial weighted source reduction errors.',
                  'Commitment binding, FS/QROM, hash-query/adversary cost bounds.',
                  'Envelope sizes and any Ext12 implementation/size changes.'],
        interpretation='Passing a partial ledger is not sufficient. Failing its upper bound does not exhibit an attack. '
                       'Ext12 is an arithmetic field-size sensitivity only. No accepted parameters or gate changed.')
    (ROOT/'results/code-switch-algebra-ledger.json').write_text(json.dumps(report,indent=2)+'\n')
    for r in records:print(r['query_bits_per_stage'],r['query_sum_bits'],r['fields'])

if __name__=='__main__':main()
