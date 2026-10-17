"""Lossless codec only: omitted linear coefficients, 31-bit field packing,
zero-tagged leaf words, and reconstructed constant-terminal root/openings.
The complete original proof and exact original transcript are recovered.
"""
import struct
from array import array
import pq384_weighted_joint as joint
import pq384_weighted_joint_codec as original
from pq384_primitives import require,P,field_words
from pq384_cached_prover import FlatTree
MAGIC=b'NPWC\x00\x01'
limits=original.limits


class Writer:
    def __init__(self):self.data=bytearray();self.bits=0;self.count=0
    def bitword(self,value,n):
        require(type(value)is int and 0<=value<1<<n,'bit value');self.bits|=value<<self.count;self.count+=n
        while self.count>=8:self.data.append(self.bits&255);self.bits>>=8;self.count-=8
    def align(self):
        if self.count:self.data.append(self.bits);self.bits=0;self.count=0
    def raw(self,value):self.align();self.data.extend(value)
    def fields(self,values,zero_tags=False):
        for v in values:
            require(type(v)is int and 0<=v<P,'canonical field')
            if zero_tags:
                self.bitword(int(v!=0),1)
                if v:self.bitword(v,31)
            else:self.bitword(v,31)
    def vector(self,values):
        for x in values:self.fields(list(joint.ext(x)))
    def finish(self):self.align();return bytes(self.data)


class Reader:
    def __init__(self,data):self.data=data;self.offset=0;self.bits=0;self.count=0
    def bitword(self,n):
        while self.count<n:
            require(self.offset<len(self.data),'bit truncation');self.bits|=self.data[self.offset]<<self.count;self.offset+=1;self.count+=8
        value=self.bits&((1<<n)-1);self.bits>>=n;self.count-=n;return value
    def align(self):require(self.bits==0,'noncanonical padding bits');self.bits=0;self.count=0
    def raw(self,n):
        self.align();require(n>=0 and self.offset+n<=len(self.data),'raw truncation');v=self.data[self.offset:self.offset+n];self.offset+=n;return v
    def fields(self,n,zero_tags=False):
        values=[]
        for _ in range(n):
            present=self.bitword(1) if zero_tags else 1
            v=self.bitword(31) if present else 0;require(v<P and (not zero_tags or not present or v!=0),'noncanonical packed field');values.append(v)
        return values
    def vector(self,n):return [self.fields(4) for _ in range(n)]
    def finish(self):self.align();require(self.offset==len(self.data),'trailing bytes')


def recover(kept,claim):
    require(len(kept)>=1,'polynomial shape');kept=[joint.ext(x) for x in kept];linear=joint.sub(joint.sub(claim,kept[0]),kept[0])
    for x in kept[1:]:linear=joint.sub(linear,x)
    return [list(kept[0]),list(linear)]+[list(x) for x in kept[1:]]


def terminal_tree(proof,ctx):
    c=joint.ext(proof['terminal']['coefficients'][0][0]);return FlatTree(array('I',c*4),ctx)


def encode(proof,statement,parent,args,claim):
    require(joint.verify(proof,statement,parent,args,claim),'weighted proof');out=Writer();out.raw(MAGIC)
    for rd in proof['reduction']:out.vector([rd[0],rd[2]])
    for i,rd in enumerate(proof['rounds']):
        out.vector([rd['quadratic'][0],rd['quadratic'][2]])
        if i+1<len(proof['rounds']):out.raw(joint.decode_hash(rd['next_root']))
    out.vector([proof['terminal']['coefficients'][0][0]]);out.align()
    metadata=original.stages(proof,statement,parent,args,claim)
    for j,(root,ctx,count,indices,words) in enumerate(metadata):
        section,index=('sources',j) if j<len(args) else ('folds',j-len(args))
        opened=[q[section][index] for q in proof['queries']]
        if j+1==len(metadata):
            tree=terminal_tree(proof,ctx);require(tree.root==root and all(tree.opening(i)==op for i,op in zip(indices,opened)),'exact terminal reconstruction');continue
        shared=original.mp.compress(root,ctx,count,indices,[field_words(v['leaf']) for v in opened],[[joint.decode_hash(h) for h in v['path']] for v in opened])
        for leaf in shared['leaves']:out.fields(list(struct.unpack('<'+'I'*words,leaf)),True)
        out.align()
        for sibling in shared['siblings']:out.raw(sibling)
    return out.finish()


def decode(data,statement,parent,args,initial_claim):
    n,_,maximum=limits(args);require(type(data)is bytes and len(MAGIC)<=len(data)<=maximum,'compact weighted size');rd=Reader(data);require(rd.raw(len(MAGIC))==MAGIC,'weighted magic')
    _,_,_,t,claim=joint.public(statement,parent,args,initial_claim);reduction=[];rounds=[]
    for _ in range(n):
        row=recover(rd.vector(2),claim);_,_,claim=joint.round_start(t,row,claim);reduction.append(row)
    for i in range(n):
        row=recover(rd.vector(2),claim);_,stage,claim=joint.round_start(t,row,claim)
        root=rd.raw(48).hex() if i+1<n else None;rounds.append(dict(quadratic=row,next_root=root))
        if root:t.commit(b'weighted-joint-next-root',bytes.fromhex(root))
    terminal=dict(profile='near-pq384-terminal-v1',coefficients=[[rd.fields(4)]]);rd.align()
    proof=dict(profile=joint.PROFILE,reduction=reduction,rounds=rounds,terminal=terminal,queries=[])
    finaltree=terminal_tree(proof,joint.context(stage,1));proof['rounds'][-1]['next_root']=finaltree.root.hex()
    metadata=original.stages(proof,statement,parent,args,initial_claim);opened=[]
    for j,(root,ctx,count,indices,w) in enumerate(metadata):
        if j+1==len(metadata):
            require(finaltree.root==root and finaltree.context==ctx and count==2,'terminal context');opened.append([finaltree.opening(i) for i in indices]);continue
        leaves=[field_words(rd.fields(w,True)) for _ in original.mp.shape(count,indices)];rd.align();siblings=[rd.raw(48) for _ in original.mp.boundary(count,indices)]
        ls,paths=original.mp.expand(root,ctx,count,indices,dict(leaves=leaves,siblings=siblings))
        opened.append([dict(leaf=list(struct.unpack('<'+'I'*w,leaf)),path=[h.hex() for h in path]) for leaf,path in zip(ls,paths)])
    proof['queries']=[dict(sources=[v[q] for v in opened[:len(args)]],folds=[v[q] for v in opened[len(args):]]) for q in range(8)]
    rd.finish();require(joint.verify(proof,statement,parent,args,initial_claim),'compact weighted verification');return proof
