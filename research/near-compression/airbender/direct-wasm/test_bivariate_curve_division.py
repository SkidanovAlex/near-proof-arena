"""Formal coefficient division by Y-curve(X), including small characteristic."""
import json
import random
from test_bivariate_multiplicity import add,mul,compose
from test_independent_constraint_mixing import evaluate


def quotient(rows,curve,p):
    # Operational synthetic division, independent of the Lean drop/substitute definition.
    acc=[]
    out=[]
    for row in reversed(rows[1:]):
        acc=add(row,mul(curve,acc,p),p)
        out.append(acc)
    return list(reversed(out))


def row(rows,j):return rows[j] if j<len(rows) else []
def nonzero(rows):return any(c for r in rows for c in r)
def equal(a,b):return all((a[i] if i<len(a) else 0)==(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b))))
def weighted(rows,k,D):return all(c==0 or i+k*j<D for j,r in enumerate(rows) for i,c in enumerate(r))


def factor(q,curve,p):
    return [add(row([[]]+q,j),[-c%p for c in mul(curve,row(q,j),p)],p) for j in range(len(q)+1)]


def check(rows,curve,k,D,p):
    q=quotient(rows,curve,p)
    remainder=compose(rows,curve,p)
    assert len(q)==max(len(rows)-1,0)
    assert all(equal(r,compose(rows[j+1:],curve,p)) for j,r in enumerate(q))
    product=factor(q,curve,p)
    rebuilt=product[:]
    rebuilt[0]=add(rebuilt[0],remainder,p)
    assert all(equal(row(rows,j),row(rebuilt,j)) for j in range(max(len(rows),len(rebuilt))+2))
    divides=all(equal(row(rows,j),row(product,j)) for j in range(max(len(rows),len(product))+2))
    assert divides==(not any(remainder))
    if nonzero(rows) and not any(remainder):assert nonzero(q)
    assert weighted(rows,k,D) and weighted(q,k,max(D-k,0))
    return not any(remainder),nonzero(rows)


def main():
    rng=random.Random(60477208)
    cases=roots=nonzero_roots=0
    for p in (2,3,5,17):
        for _ in range(200):
            k,D=rng.randrange(4),rng.randrange(10)
            curve=[rng.randrange(p) for _ in range(k+1)]
            rows=[[rng.randrange(p) if i+k*j<D else 0 for i in range(rng.randrange(10))] for j in range(rng.randrange(8))]
            root,nz=check(rows,curve,k,D,p)
            cases+=1;roots+=root;nonzero_roots+=root and nz
            # Generate an actual factor; quotient weight is D-k.
            q=[[rng.randrange(p) if i+k*j<max(D-k,0) else 0 for i in range(8)] for j in range(5)]
            rows=factor(q,curve,p)
            root,nz=check(rows,curve,k,D,p)
            assert root
            cases+=1;roots+=root;nonzero_roots+=root and nz
        # Formal polynomial X^p-X is zero as a function but is not a curve root.
        formal=[0]*(p+1);formal[1]=-1%p;formal[p]=1
        assert all(evaluate(formal,x,p)==0 for x in range(p))
        root,nz=check([formal],[0],0,p+1,p)
        assert nz and not root
    print(json.dumps(dict(division_cases=cases,root_cases=roots,nonzero_root_cases=nonzero_roots,
        zero_function_nonroots=4,scope='Formal linear-factor identity, quotient nonzeroness and weighted degree only. Repeated-factor extraction, useful factors and full MCA exception count remain open.'),indent=2))


if __name__=='__main__':main()
