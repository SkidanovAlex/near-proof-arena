"""Lossless transport omitting fold scalars determined by preceding queries.
Transcript, roots, sampling and decoded PCS proof are unchanged. Reconstructed
leaves are authenticated by the original multiproof and full PCS verifier.
"""
import struct
import pq384_ext8_weighted_codec as base
p,mp=base.p,base.mp
MAGIC=base.DERIVED_MAGIC


def pair(opening):
    p.h.require(len(opening['leaf'])==16,'fold leaf width')
    return p.f.canonical(opening['leaf'][:8]),p.f.canonical(opening['leaf'][8:])


def initial_pairs(sources,branches,degrees,D,betas,samples):
    result=[]
    for qi,s in enumerate(samples):
        a=b=p.f.ZERO
        for openings,branch,d,powers in zip(sources,branches,degrees,betas):
            leaf=openings[qi]['leaf']
            p.h.require(len(leaf)==2*len(powers) and all(type(x)is int and 0<=x<p.f.P for x in leaf),'source field words')
            left=right=p.f.ZERO
            for j,power in enumerate(powers):
                left=p.f.add(left,p.f.scale(power,leaf[2*j]))
                right=p.f.add(right,p.f.scale(power,leaf[2*j+1]))
            if d<D:left=right=(left,right)[(s%(4*d))//(2*d)]
            a=p.f.add(a,left);b=p.f.add(b,right)
        result.append((a,b))
    return result


def derived_values(half,challenge,samples,previous):
    """One checked child coordinate per query; repeated coordinates must agree."""
    p.h.require(len(previous)==len(samples),'previous query count')
    omega=pow(440564289,(1<<27)//(4*half),p.f.P)
    known={}
    for s,(a,b) in zip(samples,previous):
        x=pow(omega,s%(2*half),p.f.P)
        even=p.f.scale(p.f.add(a,b),pow(2,-1,p.f.P))
        odd=p.f.scale(p.f.sub(a,b),pow(2*x,-1,p.f.P))
        value=p.f.add(even,p.f.mul(challenge,p.f.sub(odd,even)))
        key=(s%half,(s%(2*half))//half)
        p.h.require(key not in known or known[key]==value,'derived scalar disagreement')
        known[key]=value
    return known


def prepare(proof,statement,parent,branches,claim,queries):
    degrees,D,_,betas,_,_,rs,samples=p.replay(proof,statement,parent,branches,claim,queries=queries)
    plan,check_samples,terminal=base.stages(proof,statement,parent,branches,claim,queries)
    p.h.require(samples==check_samples,'sample replay')
    return degrees,D,betas,rs,samples,plan,terminal


def encode(proof,statement,parent,branches,claim,*,queries):
    p.verify(proof,statement,parent,branches,claim,queries=queries)
    degrees,D,betas,rs,samples,plan,_=prepare(proof,statement,parent,branches,claim,queries)
    out=bytearray(MAGIC);seen={};previous=None
    for q in proof['reduction']:out.extend(p.vector_bytes(q))
    for rd in proof['rounds']:out.extend(p.vector_bytes(rd['quadratic']));out.extend(p.hashread(rd['root']))
    out.extend(p.vector_bytes([proof['terminal']]))
    for stage in plan:
        openings=[q[stage['kind']][stage['index']] for q in proof['queries']]
        shared=mp.compress(stage['root'],stage['context'],stage['half'],stage['indices'],
            [p.h.field_words(o['leaf']) for o in openings],[[p.hashread(x) for x in o['path']] for o in openings])
        if stage['kind']=='sources':
            key=base.source_key(stage)
            if key in seen:
                p.h.require(shared==seen[key],'conflicting shared source');continue
            seen[key]=shared
            out.extend(b''.join(shared['leaves']))
        else:
            if previous is None:
                sources=[[q['sources'][i] for q in proof['queries']] for i in range(len(branches))]
                previous=initial_pairs(sources,branches,degrees,D,betas,samples)
            known=derived_values(stage['half'],rs[stage['index']],samples,previous)
            for index,leaf in zip(mp.shape(stage['half'],stage['indices']),shared['leaves']):
                for side in range(2):
                    raw=leaf[32*side:32*(side+1)]
                    if (index,side) in known:
                        p.h.require(base.extread(raw)==list(known[index,side]),'derived leaf mismatch')
                    else:out.extend(raw)
            previous=[pair(o) for o in openings]
        out.extend(b''.join(shared['siblings']))
    p.h.require(len(out)<=base.MAX_BYTES,'codec cap')
    return bytes(out)


def decode(data,statement,parent,branches,claim,*,queries):
    p.h.require(type(data)is bytes and len(data)<=base.MAX_BYTES,'codec cap')
    _,D,_,_,_=p.public(statement,parent,branches,claim,queries);n=D.bit_length()-1;offset=0
    def read(size):
        nonlocal offset
        p.h.require(size>=0 and offset+size<=len(data),'truncated codec')
        value=data[offset:offset+size];offset+=size;return value
    p.h.require(read(8)==MAGIC,'codec version')
    reduction=[[base.extread(read(32)) for _ in range(3)] for _ in range(n)]
    rounds=[dict(quadratic=[base.extread(read(32)) for _ in range(3)],root=read(48).hex()) for _ in range(n)]
    proof=dict(profile=p.PROFILE,reduction=reduction,rounds=rounds,terminal=base.extread(read(32)),queries=[])
    degrees,D,betas,rs,samples,plan,terminal=prepare(proof,statement,parent,branches,claim,queries)
    sources=[None]*len(branches);folds=[None]*n;seen={};previous=None
    for stage in plan:
        unique=mp.shape(stage['half'],stage['indices']);boundary=mp.boundary(stage['half'],stage['indices'])
        if stage['kind']=='sources':
            key=base.source_key(stage)
            if key in seen:sources[stage['index']]=seen[key];continue
            leaves=[read(stage['width']) for _ in unique]
        else:
            if previous is None:previous=initial_pairs(sources,branches,degrees,D,betas,samples)
            known=derived_values(stage['half'],rs[stage['index']],samples,previous)
            leaves=[]
            for index in unique:
                parts=[]
                for side in range(2):
                    value=known.get((index,side))
                    parts.append(p.vector_bytes([value]) if value is not None else read(32))
                leaves.append(b''.join(parts))
        shared=dict(leaves=leaves,siblings=[read(48) for _ in boundary])
        leaves,paths=mp.expand(stage['root'],stage['context'],stage['half'],stage['indices'],shared)
        openings=[dict(leaf=list(struct.unpack('<'+'I'*(len(leaf)//4),leaf)),path=[x.hex() for x in path]) for leaf,path in zip(leaves,paths)]
        if stage['kind']=='sources':sources[stage['index']]=openings;seen[key]=openings
        else:folds[stage['index']]=openings;previous=[pair(o) for o in openings]
    p.h.require(offset==len(data),'trailing codec bytes')
    folds[-1]=[terminal.opening(s%2) for s in samples]
    proof['queries']=[dict(sources=[x[i] for x in sources],folds=[x[i] for x in folds]) for i in range(len(samples))]
    return proof


def breakdown(proof,statement,parent,branches,claim,*,queries):
    _,_,_,_,samples,plan,_=prepare(proof,statement,parent,branches,claim,queries)
    rows=[];seen=set()
    for stage in plan:
        unique=mp.shape(stage['half'],stage['indices']);boundary=mp.boundary(stage['half'],stage['indices'])
        omitted=0;alias=False
        if stage['kind']=='sources':
            key=base.source_key(stage);alias=key in seen;seen.add(key)
        else:
            omitted=len({(s%stage['half'],(s%(2*stage['half']))//stage['half']) for s in samples})
        rows.append(dict(kind=stage['kind'],index=stage['index'],unique_leaves=len(unique),
            leaf_bytes=0 if alias else len(unique)*stage['width']-32*omitted,
            sibling_bytes=0 if alias else 48*len(boundary),derived_scalar_count=omitted,shared_source=alias))
    header=len(MAGIC)+240*len(proof['rounds'])+32
    return dict(header_bytes=header,stages=rows,total_bytes=header+sum(s['leaf_bytes']+s['sibling_bytes'] for s in rows),
                derived_scalar_bytes_saved=32*sum(s['derived_scalar_count'] for s in rows))
