"""Degree-sensitive derivative obstruction and recorded interpolation heights."""
import itertools
import json
import random
from pathlib import Path
from test_hensel_coefficient_step import slope


def derivative(rows,p):return [[j*c%p for c in row] for j,row in enumerate(rows) if j]
def nonzero(rows):return any(c for row in rows for c in row)


def main():
    exhaustive=random_cases=0
    for p,width in ((2,2),(3,2),(5,1)):
        for flat in itertools.product(range(p),repeat=p*width):
            rows=[list(flat[j*width:(j+1)*width]) for j in range(p)]
            assert (not nonzero(derivative(rows,p)))==(not nonzero(rows[1:]))
            exhaustive+=1
    rng=random.Random(6_176017)
    for p in (2,3,5,17):
        for _ in range(100):
            rows=[[rng.randrange(p) for _ in range(rng.randrange(6))] for _ in range(rng.randrange(p+1))]
            d=derivative(rows,p)
            assert (not nonzero(d))==(not nonzero(rows[1:]))
            for i in range(7):
                for j in range(len(rows)+2):
                    actual=d[j][i] if j<len(d) and i<len(d[j]) else 0
                    source=rows[j+1][i] if j+1<len(rows) and i<len(rows[j+1]) else 0
                    assert actual==(j+1)*source%p
            random_cases+=1
        # At degree p, Y^p is nonconstant but derivative zero.
        rows=[[] for _ in range(p)]+[[1]]
        assert nonzero(rows[1:]) and not nonzero(derivative(rows,p))
    # Below characteristic, repeated factors can still have singular roots.
    repeated=[]
    for p in (3,5,17):
        rows=[[1],[-2%p],[1]]
        assert len(rows)<=p and nonzero(derivative(rows,p)) and slope(rows,[1],p)==0
        repeated.append(p)
    root=Path(__file__).resolve().parents[2]
    previous=json.loads((root/'results/trivariate-interpolation/report.json').read_text())
    prime=2013265921
    screen=[]
    for g in previous['representative_dimension_screen']:
        h=g['height']
        assert h<=prime and all(j%prime!=0 for j in range(1,h))
        screen.append(dict(dimension=g['dimension'],rate=g['rate'],height=h,max_y_degree=h-1,
            characteristic=prime,below_characteristic=True))
    assert [r['height'] for r in screen]==[58,83,116,165,236,379,464]
    print(json.dumps(dict(exhaustive_bivariate_polynomials=exhaustive,random_coefficient_checks=random_cases,
        characteristic_boundary_counterexamples=4,nonzero_derivative_singular_root_examples=repeated,
        recorded_dimension_screen=screen,
        scope='Nonconstant low-Y-degree polynomials have nonzero formal derivative; does not establish squarefreeness, irreducibility, smooth branches or full MCA. Recorded dimension screen is not an approved security parameter set.'),indent=2))


if __name__=='__main__':main()
