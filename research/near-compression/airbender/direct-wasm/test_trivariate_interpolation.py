"""Exact trivariate support/count checks and independent concrete witnesses."""
import json
import math
from test_jet_center_polynomial import term
from test_bivariate_weighted_degree import kernel_vector
from test_bivariate_multiplicity import add


def monomials(k,DX,height,DZ):
    # Matches Lean: Y first, Z second, X third.
    return [(i,j,h) for j in range(height) for h in range(max(DZ-j,0))
            for i in range(max(DX-k*j,0))]


def ceil_sqrt_ratio(num,den):
    q=math.isqrt(num//den)
    return q+(q*q*den<num)


def main():
    supports=counts=0
    for k in range(4):
        for DX in range(9):
            for height in range(7):
                for DZ in range(8):
                    indices=monomials(k,DX,height,DZ)
                    assert len(indices)==len(set(indices))
                    assert set(indices)=={(i,j,h) for i in range(DX) for j in range(height)
                        for h in range(DZ) if i+k*j<DX and j+h<DZ}
                    assert len(indices)==sum(max(DX-k*j,0)*max(DZ-j,0) for j in range(height))
                    supports+=1
    for N in range(6):
        for m in range(9):
            for DZ in range(9):
                orders=monomials(1,m,m,DZ)
                assert len(orders)==sum((m-s)*max(DZ-s,0) for s in range(m))
                assert set(orders)=={(r,s,t) for r in range(m) for s in range(m)
                    for t in range(DZ) if r+s<m and s+t<DZ}
                assert N*len(orders)==N*sum((m-s)*max(DZ-s,0) for s in range(m))
                counts+=1
    witnesses=[]
    for p in (3,5,17):
        indices=monomials(1,6,5,5)
        orders=monomials(1,2,2,5)
        sources=[(x,(x*x+1)%p,(x+2)%p) for x in range(3)]
        matrix=[]
        for x,u,v in sources:
            for r,s,t in orders:
                polys=[term(i,j,h,r,s,x,u,v,p) for i,j,h in indices]
                matrix.append([q[t] if t<len(q) else 0 for q in polys])
        assert len(indices)==70>len(matrix)==42
        vector,rank=kernel_vector(matrix,len(indices),p)
        assert any(vector)
        for x,u,v in sources:
            for r,s in ((0,0),(1,0),(0,1)):
                q=[]
                for c,(i,j,h) in zip(vector,indices):q=add(q,[c*a%p for a in term(i,j,h,r,s,x,u,v,p)],p)
                assert not any(q)
        witnesses.append(dict(prime=p,rank=rank,coefficients=vector))
    # Representative dimension-only screening, not a mapped protocol budget.
    # Multiplicity20 and integer ceilings of the prior MCA interpolation shape.
    geometry=[]
    for degree,rate in [(131072,8),(16384,16),(2048,32),(256,64),(32,128),(4,256),(2,256)]:
        n=degree*rate;k=degree-1;m=20
        DX=ceil_sqrt_ratio((2*m+1)**2*n*k,4)
        height=ceil_sqrt_ratio((2*m+1)**2*n,4*k)
        DZ=((2*m+1)**2*n+12*k-1)//(12*k)
        variables=sum(max(DX-k*j,0)*max(DZ-j,0) for j in range(height))
        equations=n*sum((m-s)*max(DZ-s,0) for s in range(m))
        assert variables>equations
        geometry.append(dict(dimension=degree,rate=rate,n=n,multiplicity=m,
            DX=DX,height=height,DZ=DZ,variables=variables,equations=equations,slack=variables-equations))
    print(json.dumps(dict(support_cases=supports,constraint_count_cases=counts,
        witnesses=witnesses,representative_dimension_screen=geometry,
        scope='General sparse-vector controlled-Z interpolation exists under the proved dimension inequality. Geometry screen is dimension-only; specialization, MCA error and protocol/QROM composition remain open.'),indent=2))


if __name__=='__main__':main()
