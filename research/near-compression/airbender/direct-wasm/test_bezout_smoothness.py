"""Construct and verify Bezout certificates; use them to certify Hensel slopes."""
import json
import random
from test_bivariate_multiplicity import add,mul,trim,compose
from test_bivariate_curve_division import equal
from test_synthetic_multiplicity import quotient
from test_hensel_coefficient_step import slope,order
from test_hensel_bounded_reconstruction import lift
from test_independent_constraint_mixing import evaluate


def derivative(q,p):return [(i+1)*c%p for i,c in enumerate(q[1:])]
def sub(a,b,p):return add(a,[-c%p for c in b],p)


def divide(a,b,p):
    r=trim(a);b=trim(b);assert b
    out=[0]*max(len(r)-len(b)+1,0)
    while r and len(r)>=len(b):
        j=len(r)-len(b);c=r[-1]*pow(b[-1],-1,p)%p;out[j]=c
        r=trim(sub(r,[0]*j+[c*x%p for x in b],p))
    return trim(out),r


def egcd(a,b,p):
    r0,r1=trim(a),trim(b);s0,s1=[1],[];t0,t1=[],[1]
    while r1:
        q,r=divide(r0,r1,p)
        r0,r1=r1,r;s0,s1=s1,sub(s0,mul(q,s1,p),p);t0,t1=t1,sub(t0,mul(q,t1,p),p)
    if not r0:return [],s0,t0
    c=pow(r0[-1],-1,p)
    return [c*x%p for x in r0],[c*x%p for x in s0],[c*x%p for x in t0]


def main():
    rng=random.Random(69_78)
    checked=certified=rejected=roots=lifts=derivative_checks=mutations=0
    witnesses=[]
    for p in (2,3,5,17):
        for _ in range(150):
            q=[rng.randrange(p) for _ in range(rng.randrange(1,8))]
            dq=derivative(q,p)
            g,A,B=egcd(q,dq,p)
            assert equal(add(mul(A,q,p),mul(B,dq,p),p),g)
            checked+=1
            for a in range(p):
                assert evaluate(dq,a,p)==evaluate(quotient(q,a,p),a,p)
                derivative_checks+=1
            if len(trim(g))!=1:
                rejected+=1
                continue
            assert equal(g,[1]);certified+=1
            if len(witnesses)<4 and any(evaluate(q,a,p)==0 for a in range(p)):
                witnesses.append(dict(prime=p,polynomial=q,derivative=dq,A=A,B=B))
            assert not equal(add(mul(add(A,[1],p),q,p),mul(B,dq,p),p),[1])
            mutations+=1
            rows=[[c,rng.randrange(p),rng.randrange(p)] for c in q]
            for a in range(p):
                if evaluate(q,a,p)!=0:continue
                assert evaluate(dq,a,p)!=0 and slope(rows,[a],p)==evaluate(dq,a,p)
                roots+=1
                f=lift(rows,a,3,p)
                assert order(compose(rows,f,p),4)
                lifts+=1
    # Denominator-cleared identity for Q=Y^2-Z:
    # -Q+(Y/2)Q'=Z. It certifies all specialized roots only when Z!=0.
    specialized=0
    for p in (3,5,17):
        for z in range(p):
            q=[-z%p,0,1];dq=derivative(q,p);A=[-1%p];B=[0,pow(2,-1,p)]
            assert equal(add(mul(A,q,p),mul(B,dq,p),p),[z])
            for a in range(p):
                if evaluate(q,a,p)!=0:continue
                assert (evaluate(dq,a,p)==0)==(z==0)
                if z:specialized+=1
    # A zero right-hand side does not prove smoothness, even with a valid identity.
    q=[1,1,1]  # (Y-1)^2 over F3.
    assert equal(add(mul([],q,3),mul([],derivative(q,3),3),3),[0])
    assert evaluate(q,1,3)==0 and evaluate(derivative(q,3),1,3)==0
    g,_,_=egcd(q,derivative(q,3),3);assert len(g)>1
    print(json.dumps(dict(extended_euclid_certificates=checked,nonzero_constant_certificates=certified,
        noncoprime_cases_rejected=rejected,derivative_quotient_evaluation_checks=derivative_checks,
        certified_initial_roots=roots,certified_hensel_lifts=lifts,mutated_certificates_rejected=mutations,
        cleared_denominator_smooth_roots=specialized,zero_certificate_counterexamples=1,witnesses=witnesses,
        scope='Checked Bezout identity implies smoothness of existing initial roots. General certificate existence, factorization, algebraic root/extension construction and full MCA remain open.'),indent=2))


if __name__=='__main__':main()
