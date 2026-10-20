"""Independent binomial jets check multi-center quotient/multiplicity laws."""
import itertools
import json
import math
from test_synthetic_multiplicity import quotient


def jet(cs,a,i,p):
    return sum(cs[j]*math.comb(j,i)*pow(a,j-i,p) for j in range(i,len(cs)))%p


def main():
    polynomials=commutations=preserved=certificates=0
    for p,limit in [(2,6),(3,6),(5,5)]:
        for n in range(limit+1):
            for cs in itertools.product(range(p),repeat=n):
                polynomials+=1
                orders={}
                if any(cs):
                    degree=max(i for i,c in enumerate(cs) if c)
                    for a in range(p):
                        orders[a]=next(i for i in range(n) if jet(cs,a,i,p))
                    assert sum(orders.values()) <= degree
                    # Reverse center order; zero multiplicities remain allowed.
                    current=list(cs)
                    for a in reversed(range(p)):
                        for _ in range(orders[a]):
                            assert jet(current,a,0,p)==0
                            current=quotient(current,a,p)
                    certificates+=1
                for a in range(p):
                    qa=quotient(cs,a,p)
                    for b in range(p):
                        assert quotient(qa,b,p)==quotient(quotient(cs,b,p),a,p)
                        commutations+=1
                        for i in range(n):
                            assert jet(cs,b,i+1,p)==(jet(qa,b,i,p)+(b-a)*jet(qa,b,i+1,p))%p
                        if a!=b and any(cs) and jet(cs,a,0,p)==0:
                            for i in range(orders[b]):
                                assert jet(qa,b,i,p)==0
                                preserved+=1
        # Missing distinctness doubles the same actual root.
        cs=[0,1]
        assert jet(cs,0,0,p)==0 and 1+1>=len(cs)
        # Missing removed-root premise: X has a root at 0, but division at 1
        # has quotient 1, so the other root is not preserved.
        assert jet(quotient(cs,1,p),0,0,p)==1
    print(json.dumps(dict(polynomials=polynomials, quotient_commutations=commutations,
        other_center_zero_jets_preserved=preserved, multipoint_certificates=certificates,
        negative_premises=['distinct centers','removed point is a root'],
        scope='Univariate multi-point multiplicity foundation; bivariate substitution, GS interpolation existence and MCA error bound remain open.'),indent=2))


if __name__ == '__main__':
    main()
