#!/usr/bin/env python3
"""Exact conditional parameter ledger; not a protocol security certificate."""
import argparse, hashlib, json
from fractions import Fraction as F
from pathlib import Path
P=2013265921

def frac(x): return {'numerator':x.numerator,'denominator':x.denominator}
def minimum(pred):
    for x in range(1,10000):
        if pred(x): return x
    raise ValueError('search bound')
def mul(a,b,degree,c):
    v=[0]*(2*degree-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):v[i+j]=(v[i+j]+x*y)%P
    for i in range(len(v)-1,degree-1,-1):v[i-degree]=(v[i-degree]+c*v[i])%P
    return v[:degree]
def power(a,n,d,c):
    v=[1]+[0]*(d-1)
    while n:
        if n&1:v=mul(v,a,d,c)
        a=mul(a,a,d,c);n//=2
    return v

def irreducible_binomial(d,c):
    # Rabin test for d=5 prime, or d=8 with only prime divisor2.
    # gcd(x^(p^(d/l))-x, x^d-c)=1 via Euclidean polynomial arithmetic.
    assert d in (5,8)
    x=[0,1]+[0]*(d-2)
    def trim(a):
        while a and a[-1]==0:a.pop()
        return a
    def rem(a,b):
        a=a[:]
        while len(a)>=len(b):
            k=len(a)-len(b);v=a[-1]*pow(b[-1],P-2,P)%P
            for j,t in enumerate(b):a[k+j]=(a[k+j]-v*t)%P
            trim(a)
        return a
    a=[(-c)%P]+[0]*(d-1)+[1]
    b=power(x,P**(d//(5 if d==5 else 2)),d,c);b[1]=(b[1]-1)%P;b=trim(b)
    while b:a,b=b,rem(a,b)
    return len(a)==1 and power(x,P**d,d,c)==x

def run():
    rows=[]
    for D in (131072,262144):
        E=4*D-4
        for bits in (128,130,160):
            target=F(1,2**bits)
            q=minimum(lambda q:F(3,4)**q<=target)
            k=minimum(lambda k:F(E,P**k)<=target)
            qs=minimum(lambda q:F(E,P**k)+F(3,4)**q<=target)
            rows.append(dict(D=D,N=4*D,T=3*D+1,target_bits=bits,E=E,
                minimum_isolated_extension_degree=k,minimum_isolated_queries=q,
                minimum_queries_for_sum_at_minimum_degree=qs,
                extraction=frac(F(E,P**k)),query=frac(F(3,4)**qs),
                sum=frac(F(E,P**k)+F(3,4)**qs)))
    repeat=[]; E=4*262144-4
    for r in (2,3,4,8):
        q=minimum(lambda q:(F(E,P**4)+F(3,4)**q)**r<=F(1,2**128))
        repeat.append(dict(repetitions=r,minimum_queries_per_repetition=q,total_queries=r*q,
            conditional_product=frac((F(E,P**4)+F(3,4)**q)**r)))
    fields=[dict(degree=d,polynomial=f'x^{d}-11',rabin_irreducible=irreducible_binomial(d,11),
                 canonical_word_bytes=4*d,ratio_to_ext4=F(d,4).__str__()) for d in (5,8)]
    assert all(f['rabin_irreducible'] for f in fields)
    assert not irreducible_binomial(5,1) and not irreducible_binomial(8,1)
    return dict(status='PASS exact integer/rational arithmetic',current={'p':P,'extension_degree':4,
        'query_count':8,'query_tail':frac(F(3,4)**8),'extraction':frac(F(E,P**4))},
        isolated_and_combined_replay_terms=rows,conditional_sequential_repetition=repeat,
        candidate_fields=fields,
        recommendation='Prefer a separately versioned Ext8 profile for headroom; Ext5 is arithmetic-minimal for the isolated128/130 replay budget. Neither fixes root extraction or QROM.',
        field_changes=['Prove chosen extension irreducible and canonical base embedding; Rabin result here is executable evidence only.',
          'Replace all hardcoded4-coordinate kernels, serializers, GKR/PCS arithmetic and size bounds; new context/profile must bind degree and polynomial.',
          'Base BabyBear FFT domain can stay unchanged; extension butterflies operate componentwise with base twiddles.',
          'Draw5 or8 rejection-sampled coordinates; sampler supports it but does not establish hash uniformity.',
          'Query count must be verifier configuration, bound before challenges; remove hardcoded8 checks in new profile only.'],
        repetition_contract=['Product bound requires for EVERY prior history a conditional bound on the SAME false statement, with fresh independent ideal randomness and committed current messages before each challenge.',
          'Shared source commitments are allowed only after fixed-oracle binding; that common binding failure is added ONCE, not exponentiated.',
          'Different candidate polynomials or initial functional points across repetitions may satisfy different relations; an additional common-witness/candidate composition theorem is required.',
          'Repeating query draws alone shrinks the query tail but leaves extraction term E/p^4 unchanged.',
          'Reusing fold challenges or query seeds provides no product bound; domain separation alone is not independent ideal randomness or a QROM proof.'],
        composition_ledger='epsilon_total <= epsilon_binding + epsilon_FS + epsilon_upstream + epsilon_replay; proven replay ideal term E/|K|+(3/4)^q. Product replacement only under stated conditional-history contract.',
        budget_notes=['130bits per isolated replay target reserves only a fraction of128bit union budget; upstream errors are not yet accounted.',
          'For m independent or dependent bad events, union bound requires each <=2^-(128+ceil(log2 m)); independence is unnecessary for union bound.',
          'Full quantum security additionally needs appropriate reduction losses and adversary query bounds; no 128bit or PQ certification here.',
          'Field byte ratios do not equal full proof/runtime ratios; queries and Merkle siblings dominate current measured proof.'],
        security_certified=False)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    report=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'rows':report['isolated_and_combined_replay_terms'],'fields':report['candidate_fields'],'repetitions':report['conditional_sequential_repetition']},indent=2))
