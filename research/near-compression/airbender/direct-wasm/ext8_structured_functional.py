"""Algebraic candidate for a closed verifier's derived weight state.
No transcript change: existing protocols still bind expanded weight vectors.
"""
from dataclasses import dataclass
import pq384_ext8_reference as f


@dataclass(frozen=True)
class Functional:
    point: tuple
    tensor_scale: tuple
    powers: tuple=()

    @classmethod
    def equality(cls,point):return cls(tuple(f.canonical(x) for x in point),f.ONE)

    @property
    def size(self):return 1<<len(self.point)

    def inject(self,points,mixers):
        if len(points)!=len(mixers):raise ValueError('injection shape')
        return Functional(self.point,self.tensor_scale,self.powers+tuple((f.canonical(m),f.canonical(z)) for z,m in zip(points,mixers)))

    def fold(self,r):
        if not self.point:raise ValueError('terminal functional')
        r=f.canonical(r);u=self.point[0];one_r=f.sub(f.ONE,r)
        scale=f.mul(self.tensor_scale,f.add(f.mul(one_r,f.sub(f.ONE,u)),f.mul(r,u)))
        terms=tuple((f.mul(m,f.add(one_r,f.mul(r,z))),f.mul(z,z)) for m,z in self.powers)
        return Functional(self.point[1:],scale,terms)

    def at(self,index):
        if type(index)is not int or not 0<=index<self.size:raise ValueError('coefficient index')
        value=self.tensor_scale
        for bit,u in enumerate(self.point):value=f.mul(value,u if index>>bit&1 else f.sub(f.ONE,u))
        for m,z in self.powers:value=f.add(value,f.mul(m,f.power(z,index)))
        return value

    def materialize(self):return [self.at(i) for i in range(self.size)]
