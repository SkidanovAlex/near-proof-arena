"""Formal product order and zero-product cancellation over small fields."""
import itertools
import json
import random
from test_bivariate_multiplicity import mul
from test_independent_constraint_mixing import evaluate


def first(p):return next((i for i,c in enumerate(p) if c),None)
def coeff(p,i):return p[i] if i<len(p) else 0


def check(a,b,p):
    product=mul(a,b,p)
    assert (not any(product))==((not any(a)) or (not any(b)))
    m,n=first(a),first(b)
    if m is not None and n is not None:
        assert first(product)==m+n
        assert coeff(product,m+n)==coeff(a,m)*coeff(b,n)%p
    # All permitted lower-order bounds, including bounds below exact order
    # and zero polynomials: the formal theorem does not assume exact order.
    am=range((m if m is not None else len(a))+1)
    bn=range((n if n is not None else len(b))+1)
    orders=0
    for r in am:
        for s in bn:
            assert coeff(product,r+s)==coeff(a,r)*coeff(b,s)%p
            orders+=1
    return orders


def main():
    pairs=orders=0
    for p in (2,3,5):
        polys=[list(a) for n in range(4) for a in itertools.product(range(p),repeat=n)]
        for a in polys:
            for b in polys:
                orders+=check(a,b,p);pairs+=1
    rng=random.Random(0x0db211109)
    for _ in range(500):
        a=[0]*rng.randrange(8)+[rng.randrange(17) for _ in range(rng.randrange(9))]
        b=[0]*rng.randrange(8)+[rng.randrange(17) for _ in range(rng.randrange(9))]
        orders+=check(a,b,17);pairs+=1
    for p in (2,3,5,17):
        a=[0]*(p+1);a[1]=-1%p;a[p]=1
        assert all(evaluate(a,x,p)==0 for x in range(p))
        assert any(mul(a,a,p))
        check(a,a,p)
    # Dropping the domain hypothesis is unsound: Z/6Z has zero divisors.
    assert any([2]) and any([3]) and not any(mul([2],[3],6))
    print(json.dumps(dict(product_pairs=pairs,order_coefficient_checks=orders,
        zero_function_products=4,nonfield_counterexamples=1,
        scope='Formal product order and no zero divisors. Substitution through a curve-factor identity and preservation of other roots remain open.'),indent=2))


if __name__=='__main__':main()
