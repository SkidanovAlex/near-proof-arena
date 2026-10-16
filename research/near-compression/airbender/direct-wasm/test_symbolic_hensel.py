"""Generic expression-polynomial Hensel lifting versus independent field lifts."""
import json
import random
from test_common_denominator import expand,normalize
from test_rational_specialization import poly,plus,times,neg,ev
from test_bivariate_multiplicity import add,mul,compose
from test_bivariate_curve_division import equal
from test_hensel_bounded_reconstruction import lift
from test_independent_constraint_mixing import evaluate

ZERO=poly([])

def sadd(a,b):return [plus(a[i],b[i]) if i<len(a) and i<len(b) else a[i] if i<len(a) else b[i] for i in range(max(len(a),len(b)))]
def smul(a,b):
    out=[]
    for c in reversed(a):out=sadd([times(c,d) for d in b],[ZERO]+out)
    return out

def scompose(rows,f):
    out=[]
    for row in reversed(rows):out=sadd(row,smul(f,out))
    return out

def slift(rows,a,n):
    f=[a]
    for i in range(1,n+1):
        residual=scompose(rows,f)
        c=times(neg(residual[i] if i<len(residual) else ZERO),('r',))
        f=sadd(f,[ZERO]*i+[c])
    return f

def specialize(f,s,z,p):return [ev(expand(e,tuple(s)),z,p)[0] for e in f]
def minus(a,p):return [-c%p for c in a]


def main():
    rng=random.Random(835_656)
    arithmetic=fixtures=coefficients=certificates=0
    records=[]
    for p in (2,3,5,17):
        for _ in range(30):
            s=(1,1);z=rng.choice([z for z in range(p) if (z+1)%p])
            f,g=[[poly([rng.randrange(p) for _ in range(rng.randrange(3))]) for _ in range(rng.randrange(5))] for _ in range(2)]
            assert equal(specialize(sadd(f,g),s,z,p),add(specialize(f,s,z,p),specialize(g,s,z,p),p))
            assert equal(specialize(smul(f,g),s,z,p),mul(specialize(f,s,z,p),specialize(g,s,z,p),p))
            rows=[f,g,[poly([1])]]
            assert equal(specialize(scompose(rows,g),s,z,p),compose([specialize(r,s,z,p) for r in rows],specialize(g,s,z,p),p))
            arithmetic+=1
        for _ in range(3):
            A,B,U,V=[[rng.randrange(p),rng.randrange(p)] for _ in range(4)]
            S=add(A,B,p)
            if not any(S):B[0]=(B[0]+1)%p;S=add(A,B,p)
            t=rng.randrange(p)
            # (Y-F(X,Z))*(Y+B(Z)+tX), F=A+UX+VX^2.
            q0=[minus(mul(A,B,p),p),minus(add(mul(U,B,p),[t*c%p for c in A],p),p),minus(add(mul(V,B,p),[t*c%p for c in U],p),p),minus([t*c%p for c in V],p)]
            q1=[add(B,minus(A,p),p),add([t],minus(U,p),p),minus(V,p)]
            raw=[q0,q1,[[1]]]
            rows=[[poly(c) for c in row] for row in raw]
            f=slift(rows,poly(A),3)
            num,exponent,budget=normalize(f[3],tuple(S),p)
            assert not any(num)
            safe=[]
            for z in range(p):
                if evaluate(S,z,p)==0:continue
                safe.append(z)
                actual_rows=[[evaluate(c,z,p) for c in row] for row in raw]
                initial=evaluate(A,z,p)
                actual=lift(actual_rows,initial,3,p)
                symbolic=specialize(f,S,z,p)
                target=[evaluate(c,z,p) for c in (A,U,V)]+[0]
                assert equal(symbolic,actual) and equal(actual,target)
                assert not any(compose(actual_rows,symbolic,p))
                coefficients+=len(symbolic)
            enough=len(safe)>=budget+1
            certificates+=enough
            records.append(dict(prime=p,denominator=S,safe_challenges=len(safe),high_coefficient_numerator_budget=budget,
                high_coefficient_denominator_exponent=exponent,enough_for_zero_certificate=enough))
            fixtures+=1
    # A nonzero but incorrect denominator does NOT reproduce the Hensel lift.
    rows=[[poly([0]),poly([4])],[poly([2])],[poly([1])]]
    symbolic=slift(rows,poly([0]),1)
    wrong=specialize(symbolic,[1],0,5)
    correct=lift([[0,4],[2],[1]],0,1,5)
    assert not equal(wrong,correct)
    # Zero denominator is outside the safe domain even if totalized evaluation exists.
    assert not ev(expand(('r',),(0,)),0,5)[1]
    print(json.dumps(dict(arithmetic_fixtures=arithmetic,generic_hensel_fixtures=fixtures,
        matched_specialized_coefficients=coefficients,sufficient_sample_zero_certificates=certificates,
        fixtures=records,incorrect_nonzero_slope_counterexamples=1,zero_slope_exclusions=1,
        scope='Generic symbolic/numeric Hensel correspondence with explicit initial-root and actual-slope premises. Useful factors, common branch construction, algebraic extensions and full MCA remain open.'),indent=2))


if __name__=='__main__':main()
