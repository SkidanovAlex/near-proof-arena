"""Specialization identity and annihilation bound checks over finite fields."""
import json
import random
from pathlib import Path
from test_trivariate_interpolation import monomials
from test_jet_center_polynomial import term
from test_bivariate_translation import translate
from test_independent_constraint_mixing import evaluate


def specialize(k,DX,height,DZ,indices,values,z,p):
    rows=[[0]*max(DX-k*j,0) for j in range(height)]
    for i,j,h in indices:rows[j][i]=(rows[j][i]+values[i,j,h]*pow(z,h,p))%p
    return rows


def coeff(rows,r,s):
    return rows[s][r] if s<len(rows) and r<len(rows[s]) else 0


def main():
    rng=random.Random(498646)
    vectors=mixed_checks=0
    for p in (2,3,5,17):
        for _ in range(50):
            k,DX,height,DZ=rng.randrange(4),rng.randrange(1,8),rng.randrange(1,6),rng.randrange(1,7)
            indices=monomials(k,DX,height,DZ)
            values={index:rng.randrange(p) for index in indices};values[indices[0]]=1
            x,u,v=[rng.randrange(p) for _ in range(3)]
            zeros=0
            for z in range(p):
                rows=specialize(k,DX,height,DZ,indices,values,z,p)
                zeros+=not any(c for row in rows for c in row)
                assert all(c==0 or i+k*j<DX for j,row in enumerate(rows) for i,c in enumerate(row))
                translated=translate(rows,x,(u+z*v)%p,p)
                for r in range(3):
                    for s in range(3):
                        right=sum(values[i,j,h]*evaluate(term(i,j,h,r,s,x,u,v,p),z,p) for i,j,h in indices)%p
                        assert coeff(translated,r,s)==right
                        mixed_checks+=1
            assert zeros<=DZ-1
            vectors+=1
    root=Path(__file__).resolve().parents[2]
    prior=json.loads((root/'results/trivariate-interpolation/report.json').read_text())
    retained=[]
    for witness in prior['witnesses']:
        p=witness['prime'];indices=monomials(1,6,5,5)
        values=dict(zip(indices,witness['coefficients']))
        assert len(values)==70 and any(values.values())
        zeros=0
        for z in range(p):
            rows=specialize(1,6,5,5,indices,values,z,p)
            zeros+=not any(c for row in rows for c in row)
            for x in range(3):
                translated=translate(rows,x,(x*x+1+z*(x+2))%p,p)
                assert all(coeff(translated,r,s)==0 for r,s in ((0,0),(1,0),(0,1)))
        assert zeros<=4
        retained.append(dict(prime=p,zero_specializations=zeros))
    # Nonzero Q=Z has one zero specialization; Q=Z^3-Z saturates the bound
    # over F3. Zero-function behavior must not imply a zero sparse polynomial.
    assert sum(evaluate([0,1],z,3)==0 for z in range(3))==1
    assert sum(evaluate([0,2,0,1],z,3)==0 for z in range(3))==3
    assert sum(evaluate([0,1],z,3)==0 for z in [0,0,0])==3>1
    assert sum(evaluate([0,0],z,3)==0 for z in range(3))==3>1
    print(json.dumps(dict(nonzero_vectors=vectors,mixed_coefficient_identities=mixed_checks,
        retained_interpolants=retained,
        boundary_cases=['Q=Z','Q=Z^3-Z over F3','duplicate sample invalidates count','zero vector invalidates count'],
        scope='Formal specialization and total-annihilation bound only. Useful-factor/Hensel and complete MCA exceptions remain open.'),indent=2))


if __name__=='__main__':main()
