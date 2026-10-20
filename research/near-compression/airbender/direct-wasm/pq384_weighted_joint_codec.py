"""Canonical shared-path encoding for the new experimental joint PCS."""
import struct
import pq384_weighted_joint as joint
import pq384_multiproof as mp
from pq384_primitives import require,field_words,P
MAGIC=b'NPWJ\x00\x01'

def limits(arguments):
    require(1<=len(arguments)<=128,'branch count')
    dimensions=[]
    for a in arguments:
        n=a['log_rows'];p=a['packing'];w=a['width'];d=(1<<n)*p
        require(type(n)is int and 1<=n<=13 and type(p)is int and p>0 and p&(p-1)==0 and 128<=d<=262144 and 0<w and (w+p-1)//p<=64,'joint codec shape')
        dimensions.append((d,2*((w+p-1)//p)))
    D=max(d for d,_ in dimensions);n=D.bit_length()-1;fixed=len(MAGIC)+144*n+16;maximum=fixed
    for d,words in dimensions:maximum+=8*(4*words+48*((2*d).bit_length()-1))
    for j in range(n):maximum+=8*(32+48*((D>>j).bit_length()-1))
    return n,fixed,maximum

def stages(proof,statement,parent,arguments,claim):
    ds,D,source_contexts,_,roots,contexts,_,samples=joint.replay(proof,statement,parent,arguments,claim)
    result=[]
    for a,d,ctx in zip(arguments,ds,source_contexts):result.append((bytes.fromhex(a['root']),ctx,2*d,[s%(2*d) for s in samples],2*len(a['lanes'])))
    for j,(root,ctx) in enumerate(zip(roots,contexts)):
        count=D>>j;result.append((root,ctx,count,[s%count for s in samples],8))
    return result

def encode(proof,statement,parent,arguments,claim):
    require(joint.verify(proof,statement,parent,arguments,claim),'joint encoding verification');n,fixed,maximum=limits(arguments);out=bytearray(MAGIC)
    for rd in proof['reduction']:
        for value in rd:out.extend(field_words(list(joint.ext(value))))
    for rd in proof['rounds']:
        for value in rd['quadratic']:out.extend(field_words(list(joint.ext(value))))
        out.extend(joint.decode_hash(rd['next_root']))
    out.extend(field_words(list(joint.ext(proof['terminal']['coefficients'][0][0]))))
    for j,(root,ctx,count,indices,words) in enumerate(stages(proof,statement,parent,arguments,claim)):
        section,index=('sources',j) if j<len(arguments) else ('folds',j-len(arguments))
        opened=[q[section][index] for q in proof['queries']]
        shared=mp.compress(root,ctx,count,indices,[field_words(v['leaf']) for v in opened],[[joint.decode_hash(h) for h in v['path']] for v in opened])
        for leaf in shared['leaves']:require(len(leaf)==4*words,'joint leaf shape');out.extend(leaf)
        for sibling in shared['siblings']:out.extend(sibling)
    require(fixed<=len(out)<=maximum,'joint encoded size');return bytes(out)

def decode(data,statement,parent,arguments,claim):
    n,fixed,maximum=limits(arguments);require(type(data)is bytes and fixed<=len(data)<=maximum,'joint codec size')
    require(data[:len(MAGIC)]==MAGIC,'joint codec magic');offset=len(MAGIC)
    def read(count):
        nonlocal offset
        require(offset+count<=len(data),'joint codec truncation');v=data[offset:offset+count];offset+=count;return v
    def words(count):
        values=list(struct.unpack('<'+'I'*count,read(4*count)));require(all(v<P for v in values),'joint codec noncanonical');return values
    reduction=[[words(4) for _ in range(3)] for _ in range(n)]
    rounds=[{'quadratic':[words(4) for _ in range(3)],'next_root':read(48).hex()} for _ in range(n)]
    proof=dict(profile=joint.PROFILE,reduction=reduction,rounds=rounds,terminal={'profile':'near-pq384-terminal-v1','coefficients':[[words(4)]]},queries=[])
    metadata=stages(proof,statement,parent,arguments,claim)
    expected=fixed+sum(len(set(indices))*4*w+len(mp.boundary(count,indices))*48 for _,_,count,indices,w in metadata)
    require(len(data)==expected,'joint exact size');opened=[]
    for root,ctx,count,indices,w in metadata:
        leaves=[field_words(words(w)) for _ in mp.shape(count,indices)];siblings=[read(48) for _ in mp.boundary(count,indices)]
        ls,paths=mp.expand(root,ctx,count,indices,dict(leaves=leaves,siblings=siblings))
        opened.append([{'leaf':list(struct.unpack('<'+'I'*w,leaf)),'path':[h.hex() for h in path]} for leaf,path in zip(ls,paths)])
    proof['queries']=[dict(sources=[v[q] for v in opened[:len(arguments)]],folds=[v[q] for v in opened[len(arguments):]]) for q in range(8)]
    require(offset==len(data),'joint trailing bytes');require(joint.verify(proof,statement,parent,arguments,claim),'joint decoded verification');return proof
