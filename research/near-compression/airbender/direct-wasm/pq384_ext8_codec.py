"""Lossless canonical multiproof transport for frozen Ext8 scalar PCS.
No proof-selected indices/counts. All configured with-replacement queries replay.
Config remains verifier supplied; root is transported and must equal expected.
"""
import pq384_ext8_pcs as p
import pq384_multiproof as mp
MAGIC=b'NP8MP001'
MAX_BYTES=4*1024*1024

def metadata(proof,config,root):
    t=p.start(config,root);d=config['degree'];roots=[root];contexts=[p.source_context(config)]
    claim=p.e.canonical(config['claim']);factor=p.e.ONE
    p.h.require(type(proof['rounds'])is list and len(proof['rounds'])==d.bit_length()-1,'round count')
    for j,rd in enumerate(proof['rounds']):
        p.h.require(type(rd)is dict and set(rd)=={'quadratic','root'},'round shape')
        r,claim=p.round_start(t,rd['quadratic'],claim);u=p.e.canonical(config['point'][j])
        factor=p.e.mul(factor,p.e.add(p.e.mul(p.e.sub(p.e.ONE,r),p.e.sub(p.e.ONE,u)),p.e.mul(r,u)))
        d//=2;contexts.append(p.fold_context(t.seed,d));roots.append(p.hashread(rd['root']));t.commit(b'ext8/next-root',roots[-1])
    terminal=p.e.canonical(proof['terminal']);p.h.require(p.e.mul(factor,terminal)==claim,'terminal residual')
    terminaltree=p.tree([terminal],contexts[-1],False);p.h.require(terminaltree['root']==roots[-1],'terminal root')
    t.commit(b'ext8/terminal',p.extbytes(terminal));samples=p.sample(t,4*config['degree'],config['queries'])
    return roots,contexts,samples,terminaltree

def encode(proof,config,expected_root):
    p.verify(proof,config,expected_root)
    roots,contexts,samples,terminaltree=metadata(proof,config,expected_root)
    out=bytearray(MAGIC+expected_root)
    for rd in proof['rounds']:
        out.extend(b''.join(p.extbytes(x) for x in rd['quadratic']));out.extend(p.hashread(rd['root']))
    out.extend(p.extbytes(proof['terminal']));d=config['degree']
    for stage in range(len(proof['rounds'])):
        indices=[s%(2*d) for s in samples]
        openings=[q[stage][0] for q in proof['queries']]
        shared=mp.compress(roots[stage],contexts[stage],2*d,indices,
            [bytes.fromhex(o['leaf']) for o in openings],[[p.hashread(x) for x in o['path']] for o in openings])
        out.extend(b''.join(shared['leaves']));out.extend(b''.join(shared['siblings']));d//=2
    p.h.require(len(out)<=MAX_BYTES,'codec size cap');return bytes(out)

def decode(data,config,expected_root):
    # Bound before parsing; config shapes validated before deriving any array counts.
    p.h.require(type(data)is bytes and len(data)<=MAX_BYTES,'codec size cap');p.start(config,expected_root)
    offset=0
    def read(n):
        nonlocal offset
        p.h.require(type(n)is int and n>=0 and offset+n<=len(data),'truncated codec')
        out=data[offset:offset+n];offset+=n;return out
    p.h.require(read(len(MAGIC))==MAGIC,'codec version');p.h.require(read(48)==expected_root,'external root binding')
    rounds=[]
    for _ in range(config['degree'].bit_length()-1):
        rounds.append(dict(quadratic=[list(p.extread(read(32))) for _ in range(3)],root=read(48).hex()))
    proof=dict(profile=p.PROFILE,rounds=rounds,terminal=list(p.extread(read(32))),queries=[])
    roots,contexts,samples,terminaltree=metadata(proof,config,expected_root)
    allopen=[];d=config['degree']
    for stage in range(len(rounds)):
        indices=[s%(2*d) for s in samples];unique=mp.shape(2*d,indices);needed=mp.boundary(2*d,indices)
        width=8 if stage==0 else 64
        required=width*len(unique)+48*len(needed);p.h.require(required<=len(data)-offset,'stage size')
        shared=dict(leaves=[read(width) for _ in unique],siblings=[read(48) for _ in needed])
        leaves,paths=mp.expand(roots[stage],contexts[stage],2*d,indices,shared)
        allopen.append([dict(leaf=leaf.hex(),path=[x.hex() for x in path]) for leaf,path in zip(leaves,paths)]);d//=2
    p.h.require(offset==len(data),'trailing codec bytes')
    allopen.append([p.opening(terminaltree,s%2) for s in samples])
    proof['queries']=[[[allopen[j][i],allopen[j+1][i]] for j in range(len(rounds))] for i in range(len(samples))]
    return proof

def verify(data,config,expected_root):return p.verify(decode(data,config,expected_root),config,expected_root)

def breakdown(proof,config,root):
    roots,contexts,samples,_=metadata(proof,config,root);d=config['degree'];stages=[]
    for stage in range(len(proof['rounds'])):
        indices=[s%(2*d) for s in samples];u=len(set(indices));siblings=len(mp.boundary(2*d,indices));width=8 if stage==0 else 64
        stages.append(dict(stage=stage,leaf_count=2*d,sampled_checks=len(indices),unique_leaves=u,leaf_bytes=u*width,sibling_bytes=48*siblings));d//=2
    header=len(MAGIC)+48+len(proof['rounds'])*144+32
    return dict(header_bytes=header,stages=stages,total_bytes=header+sum(x['leaf_bytes']+x['sibling_bytes'] for x in stages),
                external_canonical_config_bytes=len(p.config_bytes(config)),expected_root_included=True)
