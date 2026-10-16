"""Canonical multiproof transport; external branch roots/weights/claim required.
Counts and indices are derived from transcript, never selected by proof bytes.
"""
import struct
import pq384_ext8_weighted as p
import pq384_multiproof as mp
MAGIC=b'NP8WMP01'
SHARED_MAGIC=b'NP8WMP02'
DERIVED_MAGIC=b'NP8WMP03'
MAX_BYTES=16*1024*1024

def extread(raw):return list(p.f.canonical(struct.unpack('<8I',raw)))
def stages(proof,statement,parent,branches,claim,queries):
    ds,D,ctx,_,roots,fc,_,samples=p.replay(proof,statement,parent,branches,claim,queries=queries)
    result=[]
    for j,(b,d,c) in enumerate(zip(branches,ds,ctx)):
        result.append(dict(kind='sources',index=j,root=p.hashread(b['root']),context=c,half=2*d,width=8*len(b['lanes']),indices=[s%(2*d) for s in samples]))
    d=D
    for j,(root,c) in enumerate(zip(roots[:-1],fc[:-1])):
        result.append(dict(kind='folds',index=j,root=root,context=c,half=d,width=64,indices=[s%d for s in samples]));d//=2
    terminal_leaf=p.vector_bytes([proof['terminal'],proof['terminal']])
    terminal=p.Tree([terminal_leaf,terminal_leaf],fc[-1])
    p.h.require(terminal.root==roots[-1],'terminal root')
    return result,samples,terminal

def source_key(stage):
    """Only identical authenticated source geometry may share transport bytes.
    Weights are deliberately absent: each branch is still verified separately.
    """
    return (stage['root'],stage['context'],stage['half'],stage['width'],tuple(stage['indices']))

def encode(proof,statement,parent,branches,claim, *, queries, shared_sources=False, derived_folds=False):
    if derived_folds:
        from pq384_ext8_derived_codec import encode as derived_encode
        return derived_encode(proof,statement,parent,branches,claim,queries=queries)
    p.verify(proof,statement,parent,branches,claim,queries=queries)
    plan,_,_=stages(proof,statement,parent,branches,claim,queries)
    out=bytearray(SHARED_MAGIC if shared_sources else MAGIC);seen={}
    for q in proof['reduction']:out.extend(p.vector_bytes(q))
    for rd in proof['rounds']:out.extend(p.vector_bytes(rd['quadratic']));out.extend(p.hashread(rd['root']))
    out.extend(p.vector_bytes([proof['terminal']]))
    for stage in plan:
        openings=[q[stage['kind']][stage['index']] for q in proof['queries']]
        shared=mp.compress(stage['root'],stage['context'],stage['half'],stage['indices'],
            [p.h.field_words(o['leaf']) for o in openings],[[p.hashread(x) for x in o['path']] for o in openings])
        if shared_sources and stage['kind']=='sources':
            key=source_key(stage)
            if key in seen:
                p.h.require(shared==seen[key],'conflicting shared source');continue
            seen[key]=shared
        out.extend(b''.join(shared['leaves']));out.extend(b''.join(shared['siblings']))
    p.h.require(len(out)<=MAX_BYTES,'codec cap');return bytes(out)

def decode(data,statement,parent,branches,claim, *, queries):
    p.h.require(type(data)is bytes and len(data)<=MAX_BYTES,'codec cap')
    if data.startswith(DERIVED_MAGIC):
        from pq384_ext8_derived_codec import decode as derived_decode
        return derived_decode(data,statement,parent,branches,claim,queries=queries)
    _,D,_,_,_=p.public(statement,parent,branches,claim,queries);n=D.bit_length()-1;offset=0
    def read(size):
        nonlocal offset
        p.h.require(size>=0 and offset+size<=len(data),'truncated codec')
        value=data[offset:offset+size];offset+=size;return value
    magic=read(len(MAGIC));p.h.require(magic in (MAGIC,SHARED_MAGIC),'codec version')
    shared_sources=magic==SHARED_MAGIC;seen={}
    reduction=[[extread(read(32)) for _ in range(3)] for _ in range(n)]
    rounds=[dict(quadratic=[extread(read(32)) for _ in range(3)],root=read(48).hex()) for _ in range(n)]
    proof=dict(profile=p.PROFILE,reduction=reduction,rounds=rounds,terminal=extread(read(32)),queries=[])
    plan,samples,terminal=stages(proof,statement,parent,branches,claim,queries)
    sources=[None]*len(branches);folds=[None]*n
    for stage in plan:
        key=source_key(stage) if shared_sources and stage['kind']=='sources' else None
        if key is not None and key in seen:
            sources[stage['index']]=seen[key];continue
        unique=mp.shape(stage['half'],stage['indices']);boundary=mp.boundary(stage['half'],stage['indices'])
        size=len(unique)*stage['width']+len(boundary)*48;p.h.require(size<=len(data)-offset,'stage size')
        shared=dict(leaves=[read(stage['width']) for _ in unique],siblings=[read(48) for _ in boundary])
        leaves,paths=mp.expand(stage['root'],stage['context'],stage['half'],stage['indices'],shared)
        openings=[dict(leaf=list(struct.unpack('<'+'I'*(len(leaf)//4),leaf)),path=[x.hex() for x in path]) for leaf,path in zip(leaves,paths)]
        (sources if stage['kind']=='sources' else folds)[stage['index']]=openings
        if key is not None:seen[key]=openings
    p.h.require(offset==len(data),'trailing codec bytes')
    folds[-1]=[terminal.opening(s%2) for s in samples]
    proof['queries']=[dict(sources=[x[i] for x in sources],folds=[x[i] for x in folds]) for i in range(len(samples))]
    return proof

def verify(data,statement,parent,branches,claim, *, queries):
    return p.verify(decode(data,statement,parent,branches,claim,queries=queries),statement,parent,branches,claim,queries=queries)

def breakdown(proof,statement,parent,branches,claim, *, queries, derived_folds=False):
    if derived_folds:
        from pq384_ext8_derived_codec import breakdown as derived_breakdown
        return derived_breakdown(proof,statement,parent,branches,claim,queries=queries)
    plan,_,_=stages(proof,statement,parent,branches,claim,queries);rows=[]
    for s in plan:
        unique=len(mp.shape(s['half'],s['indices']));siblings=len(mp.boundary(s['half'],s['indices']))
        rows.append(dict(kind=s['kind'],index=s['index'],unique_leaves=unique,leaf_bytes=unique*s['width'],sibling_bytes=48*siblings))
    header=len(MAGIC)+240*len(proof['rounds'])+32
    return dict(header_bytes=header,stages=rows,total_bytes=header+sum(s['leaf_bytes']+s['sibling_bytes'] for s in rows))
