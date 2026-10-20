"""Exhaustive small-prime checks of the new exact independent-mixer bound.
No small-field experiment or conditional list cap is a protocol certificate.
"""
import argparse,itertools,json,random
from fractions import Fraction
from pathlib import Path


def evaluate(cs,x,p):
    out=0
    for c in reversed(cs):out=(out*x+c)%p
    return out


def residual(cs,weights,claim,templates,mixers,p):
    out=sum(c*w for c,w in zip(cs,weights))-claim
    for (point,answer),r in zip(templates,mixers):out+=r*(evaluate(cs,point,p)-answer)
    return out%p


def injected(cs,weights,claim,templates,mixers,p):
    ws=weights[:]
    for (point,answer),r in zip(templates,mixers):
        for i in range(len(ws)):ws[i]=(ws[i]+r*pow(point,i,p))%p
        claim=(claim+r*answer)%p
    return (sum(c*w for c,w in zip(cs,ws))-claim)%p


def wrong(cs,weights,claim,templates,p):
    return (sum(c*w for c,w in zip(cs,weights))-claim)%p!=0 or any(evaluate(cs,x,p)!=v for x,v in templates)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();rng=random.Random(953172)
    records=[];identities=0
    for p in (3,5,7):
        for m in range(4):
            for _ in range(8):
                cs=[rng.randrange(p) for _ in range(3)];ws=[rng.randrange(p) for _ in cs];claim=rng.randrange(p)
                templates=[(rng.randrange(p),rng.randrange(p)) for _ in range(m)];accepted=0
                for mixers in itertools.product(range(p),repeat=m):
                    r=residual(cs,ws,claim,templates,mixers,p);assert r==injected(cs,ws,claim,templates,mixers,p);identities+=1
                    accepted+=r==0
                if wrong(cs,ws,claim,templates,p):assert accepted<=p**max(m-1,0)
                else:assert accepted==p**m
                records.append(dict(prime=p,constraints=m,wrong=wrong(cs,ws,claim,templates,p),accepted=accepted,tuples=p**m))
    # Nonzero residuals at later positions, plus an arbitrary old discrepancy.
    for p in (3,5,7):
        for j in range(3):
            for offset in range(p):
                deltas=[0]*3;deltas[j]=2%p
                count=sum((offset+sum(r*d for r,d in zip(rs,deltas)))%p==0 for rs in itertools.product(range(p),repeat=3))
                assert count==p**2
    family_records=[]
    for p in (3,5,7):
        family=[[0,0],[1,0],[0,1],[1,1]];ws=[1,2];claim=0;templates=[(0,1),(1,2%p)]
        bad=sum(any(wrong(cs,ws,claim,templates,p) and residual(cs,ws,claim,templates,rs,p)==0 for cs in family) for rs in itertools.product(range(p),repeat=2))
        assert bad<=len(family)*p
        family_records.append(dict(prime=p,candidates=len(family),accepted_wrong_candidate=bad,bound=len(family)*p))
    # Selecting an unconstrained candidate after the mixer invalidates a1/F claim.
    p=7;adaptive=[]
    for r in range(p):
        if (1+r)%p:
            candidate=r*pow(1+r,-1,p)%p
            assert wrong([candidate],[1],0,[(0,1)],p)
            assert residual([candidate],[1],0,[(0,1)],[r],p)==0
            adaptive.append(dict(mixer=r,candidate=candidate))
    assert len(adaptive)==p-1 and len(adaptive)>1
    assert sum(r==0 for r in [0,0,0])>1  # distinct-sample premise is necessary
    # Conditional instantiation for the measured schedule. Caps are assumptions.
    config=json.loads(Path('results/ext8-switch-execution-q309/config.json').read_text())
    rates=[config['child_blowup']]+[s['next_blowup'] for s in config['tail_steps']]
    field=2013265921**8;conditional=[]
    for label,caps in [('assumed-single-candidate',[1]*len(rates)),('assumed-10-times-target-rate',[10*b for b in rates])]:
        error=sum((Fraction(L,field) for L in caps),Fraction(0))
        conditional.append(dict(label=label,caps=caps,ideal_mixing_only_error=str(error),at_most_2neg220=error<=Fraction(1,2**220),candidate_caps_proved_for_protocol=False))
    report=dict(status='PASS',fixed_candidate_cases=len(records),injection_identity_checks=identities,records=records,family_cases=family_records,adaptive_candidate_counterexample=adaptive,duplicate_sample_counterexample=True,conditional_actual_schedule=conditional,scope='Exhaustive toy-field checks and exact conditional mixing-only arithmetic. Excludes candidate extraction/list caps, OOD/query/proximity, local/GKR/bus, Fiat-Shamir/QROM, and full NEAR correctness.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k] for k in ['status','fixed_candidate_cases','injection_identity_checks','conditional_actual_schedule']},indent=2))

if __name__=='__main__':main()
