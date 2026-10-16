"""Independent binomial checks of synthetic-jet linearity and matrix rows."""
import itertools
import json
import math
import random
from test_synthetic_multiplicity import taylor
from test_bivariate_multiplicity import add


def binomial_jet(cs,a,r,p):
    return sum(cs[j]*math.comb(j,r)*pow(a,j-r,p) for j in range(r,len(cs)))%p


def main():
    matrices=padding=0
    for p in (2,3,5):
        for n in range(6):
            for cs in itertools.product(range(p),repeat=n):
                for a in range(p):
                    expected=taylor(cs,a,p,n+2)
                    for r in range(n+2):
                        row=[taylor([0]*j+[1],a,p,r+1)[r] for j in range(n)]
                        result=sum(c*v for c,v in zip(cs,row))%p
                        assert result==expected[r]==binomial_jet(cs,a,r,p)
                        matrices+=1
                    assert taylor(list(cs)+[0,0],a,p,n+4)==expected+[0,0]
                    padding+=1
    rng=random.Random(558263)
    linear=0
    for p in (2,3,5,7):
        for _ in range(200):
            left=[rng.randrange(p) for _ in range(rng.randrange(8))]
            right=[rng.randrange(p) for _ in range(rng.randrange(8))]
            c,a=rng.randrange(p),rng.randrange(p)
            combined=add(left,[c*x%p for x in right],p)
            length=max(len(left),len(right))+3
            actual=taylor(combined,a,p,length)
            lhs=taylor(left,a,p,length)
            rhs=taylor(right,a,p,length)
            assert actual==[(x+c*y)%p for x,y in zip(lhs,rhs)]
            linear+=1
    print(json.dumps(dict(jet_matrix_rows=matrices,zero_padding_checks=padding,
        linear_combinations=linear,
        scope='Formal univariate jet linearity and coefficient-matrix identity. Bivariate mixed-jet/translation identification remains open.'),indent=2))


if __name__=='__main__':main()
