"""Check monomial indexing, canonical encoding and kernel-to-row transport."""
import json
import random
from test_bivariate_weighted_degree import kernel_vector


def monomials(k,D,height):
    return [(i,j) for j in range(height) for i in range(max(D-k*j,0))]


def encode(k,D,height,values):
    return [[values[i,j] for i in range(max(D-k*j,0))] for j in range(height)]


def main():
    rng=random.Random(32_21)
    spaces=encodings=kernels=0
    for k in range(7):
        for D in range(21):
            for height in range(9):
                indices=monomials(k,D,height)
                assert len(set(indices))==len(indices)
                assert len(indices)==sum(max(D-k*j,0) for j in range(height))
                assert set(indices)=={(i,j) for i in range(D) for j in range(height) if i+k*j<D}
                spaces+=1
                for p in (2,3,5):
                    values={index:rng.randrange(p) for index in indices}
                    rows=encode(k,D,height,values)
                    for j in range(height+2):
                        for i in range(D+2):
                            actual=rows[j][i] if j<len(rows) and i<len(rows[j]) else 0
                            assert actual==(values[i,j] if j<height and i+k*j<D else 0)
                    assert any(c for row in rows for c in row)==any(values.values())
                    encodings+=1
                if 0<len(indices)<=12:
                    p=3;n=len(indices);m=rng.randrange(n)
                    matrix=[[rng.randrange(p) for _ in indices] for _ in range(m)]
                    v,_=kernel_vector(matrix,n,p)
                    values=dict(zip(indices,v))
                    rows=encode(k,D,height,values)
                    assert any(c for row in rows for c in row)
                    assert all(sum(a*rows[j][i] for a,(i,j) in zip(row,indices))%p==0 for row in matrix)
                    kernels+=1
    counts=0
    for m in range(13):
        orders=[(r,t-r) for t in range(m) for r in range(t+1)]
        assert len(set(orders))==len(orders)
        assert set(orders)=={(r,s) for r in range(m) for s in range(m) if r+s<m}
        for N in range(10):
            constraints=[(point,order) for point in range(N) for order in orders]
            assert 2*len(constraints)==N*m*(m+1)
            counts+=1
    # Out-of-support vector entries cannot witness a nonzero interpolant.
    assert encode(1,0,3,{(9,9):1})==[[],[],[]]
    print(json.dumps(dict(monomial_spaces=spaces,coefficient_encodings=encodings,
        kernel_to_polynomial_witnesses=kernels,constraint_counts=counts,
        scope='Formal monomial and generic linear-interpolant construction; mixed-jet matrix equivalence and general GS interpolation remain open.'),indent=2))


if __name__=='__main__':main()
