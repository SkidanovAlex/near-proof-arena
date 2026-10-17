"""Weighted PCS prover with packed uint32 input-reduction states.
Same transcript/relations as pq384_ext8_weighted.prove; verifier unchanged.
"""
import ctypes as C
from array import array
import pq384_ext8_weighted as p
from pq384_ext8_native import Kernel
f=p.f


class Packed:
    def __init__(self,words):
        if not isinstance(words,array) or words.typecode!='I' or words.itemsize!=4 or len(words)%8:raise ValueError('packed Ext8 words')
        self.words=words
    def __len__(self):return len(self.words)//8
    def __getitem__(self,i):
        if not isinstance(i,int):raise TypeError('scalar index')
        if i<0:i+=len(self)
        if not 0<=i<len(self):raise IndexError(i)
        return tuple(self.words[8*i:8*i+8])
    @classmethod
    def base(cls,values):
        words=array('I')
        for value in values:
            if type(value)is not int or not 0<=value<f.P:raise ValueError('canonical base coefficient')
            words.extend((value,0,0,0,0,0,0,0))
        return cls(words)


class PackedKernel(Kernel):
    def __init__(self,native):self.__dict__.update(native.__dict__)
    @staticmethod
    def pack(values):
        if isinstance(values,Packed):return (C.c_uint32*len(values.words)).from_buffer(values.words)
        return Kernel.pack(values)
    def affine_fold(self,values,r):
        n=len(values)
        if n<2 or n%2:raise ValueError('fold shape')
        out=Packed(array('I',[0])*(4*n))
        if self.lib.near_ext8_fold(self.pack(values),n,Kernel.pack([r]),self.pack(out)):raise ValueError('native fold rejected')
        return out
    def tensor_weights(self,a,b,r,s):
        if not a or len(a)!=len(b) or len(a)&(len(a)-1):raise ValueError('column tensor shape')
        if not r or len(r)!=len(s) or len(r)&(len(r)-1):raise ValueError('row tensor shape')
        n=len(a)*len(r)
        if n>1<<22 or self.tensor is None:raise ValueError('native tensor required/capacity')
        out=Packed(array('I',[0])*(8*n))
        if self.tensor(Kernel.pack(a),Kernel.pack(b),len(a),Kernel.pack(r),Kernel.pack(s),len(r),self.pack(out),n):raise ValueError('native tensor rejected')
        return out


def prove(caches,native,statement,parent,branches,claim, *, queries):
    p.h.require(all('terms' not in b for b in branches),'packed prover currently requires unpooled descriptors')
    native=PackedKernel(native)
    degrees,D,contexts,t,claim=p.public(statement,parent,branches,claim,queries)
    p.h.require(len(caches)==len(branches),'cache count');states=[]
    for cache,b,d,ctx in zip(caches,branches,degrees,contexts):
        p.h.require(cache.root.hex()==b['root'] and cache.context==ctx and cache.degree==d and cache.lanes==p.lane_count(b),'source binding')
        low=(D//d).bit_length()-1
        for j in range(p.lane_count(b)):
            cs=Packed.base(cache.coefficients(j));ws=p.families.lane_weights(b,j,native)
            q=native.quadratic(cs,ws);dot=f.add(q[0],f.evaluate(q,f.ONE));states.append([cs,ws,low,f.ONE,dot])
    reduction=[];u=[]
    for bit in range(D.bit_length()-1):
        q=[f.ZERO]*3
        for cs,ws,low,scale,dot in states:
            part=[dot,f.sub(f.ZERO,dot),f.ZERO] if bit<low else native.quadratic(cs,ws)
            q=[f.add(a,f.mul(scale,b)) for a,b in zip(q,part)]
        r,_,claim=p.round_start(t,q,claim);u.append(r);reduction.append(q)
        for state in states:
            if bit<state[2]:state[3]=f.mul(state[3],f.sub(f.ONE,r))
            else:state[0]=native.affine_fold(state[0],r);state[1]=native.affine_fold(state[1],r)
    bs=p.betas(branches,degrees,D,u);at=f.ZERO
    for state,beta in zip(states,[x for row in bs for x in row]):at=f.add(at,f.mul(f.mul(state[0][0],state[3]),beta))
    p.h.require(at==claim,'reduction terminal');combined=[f.ZERO]*D
    for cache,powers in zip(caches,bs):
        for j,power in enumerate(powers):
            for i,c in enumerate(cache.coefficients(j)):combined[i*(D//cache.degree)]=f.add(combined[i*(D//cache.degree)],f.scale(power,c))
    weights=p.eqs(u);rounds=[];trees=[];rs=[];d=D
    while d>1:
        q=native.quadratic(combined,weights);r,stage,claim=p.round_start(t,q,claim);rs.append(r)
        combined=native.affine_fold(combined,r);weights=native.affine_fold(weights,r);d//=2
        tree=p.folded_tree(combined,p.context(stage,d),native);trees.append(tree)
        t.commit(b'ext8-weighted-root',tree.root);rounds.append(dict(quadratic=q,root=tree.root.hex()))
    terminal=combined[0];p.terminal_check(t,terminal,trees[-1].root,trees[-1].context,u,rs,claim)
    openings=[dict(sources=[c.opening(s%(2*d)) for c,d in zip(caches,degrees)],folds=[tr.opening(s%tr.half) for tr in trees]) for s in p.sample(t,4*D,queries)]
    return dict(profile=p.profile(branches),reduction=reduction,rounds=rounds,terminal=terminal,queries=openings)
