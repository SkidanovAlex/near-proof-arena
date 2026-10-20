"""Canonical global-chain codec: external shape, transcript-derived indices.

Shared paths expand to the original verifier object; no query/profile changes.
Decode authenticates every stage and runs the unchanged global-chain verifier.
"""
import struct
import pq384_global_chain as gc
import pq384_multiproof as mp
from pq384_primitives import require,field_words,P
from packed_claim_handoff import canonical_ext
from pq384_one_fold import ONE,weights,decode_hash
from pq384_terminal import verify_terminal
from check_whir_handoff import add,sub,mul

MAGIC=b'NPGC\x00\x01'

def header(args,terminal_degree,rounds,terminal):
    h,t,degree,powers,claim=gc.public(args,terminal_degree);initial=degree
    count=degree.bit_length()-terminal_degree.bit_length()
    require(isinstance(rounds,list) and len(rounds)==count,'codec round count')
    roots=[args['expected_root']];contexts=[bytes.fromhex(h['context_hex'])];factor=ONE
    for j,rd in enumerate(rounds):
        require(type(rd)is dict and set(rd)=={'quadratic','next_root'},'codec round fields')
        r,stage,claim=gc.round_start(t,rd['quadratic'],claim)
        factor=mul(factor,add(ONE,mul(r,sub(tuple(h['packed_point'][j]),ONE))))
        degree//=2;root=decode_hash(rd['next_root']);roots.append(root)
        contexts.append(gc.context(stage,degree,terminal_degree));t.commit(b'next-oracle-root',root)
    gc.disclose(t,terminal,terminal_degree)
    ws=[mul(factor,w) for w in weights(h['packed_point'][count:])]
    verify_terminal(terminal,expected_root=roots[-1],stage_binding=stage,degree_bound=degree,
                    domain_size=4*degree,lanes=1,weights=[[list(v) for v in ws]],claim=claim)
    sample=gc.sample(t,4*initial);stages=[];degree=initial
    for j,(root,ctx) in enumerate(zip(roots,contexts)):
        indices=[s%(2*degree) for s in sample]
        stages.append((root,ctx,2*degree,indices,2*len(powers) if j==0 else 8))
        degree//=2
    return stages

def limits(args,terminal_degree):
    h,_,degree,_,_=gc.public(args,terminal_degree)
    count=degree.bit_length()-terminal_degree.bit_length()
    fixed=len(MAGIC)+96*count+16*terminal_degree
    maximum=fixed;d=degree
    for stage in range(count+1):
        words=2*len(h['lane_claims']) if stage==0 else 8
        maximum+=gc.QUERIES*(4*words+48*((2*d).bit_length()-1));d//=2
    return count,fixed,maximum

def encode(proof,*,terminal_degree=1,**args):
    require(gc.verify(proof,terminal_degree=terminal_degree,**args),'codec source proof')
    stages=header(args,terminal_degree,proof['rounds'],proof['terminal']);out=bytearray(MAGIC)
    for rd in proof['rounds']:
        for value in rd['quadratic']:out.extend(field_words(list(canonical_ext(value))))
        out.extend(decode_hash(rd['next_root']))
    for value in proof['terminal']['coefficients'][0]:out.extend(field_words(list(canonical_ext(value))))
    for j,(root,ctx,count,indices,wordcount) in enumerate(stages):
        openings=[]
        for chain in proof['queries']:
            if j==0:opening=chain[0]['source']
            else:
                opening=chain[j-1]['next']
                if j<len(stages)-1:
                    require(opening==chain[j]['source'],'same-stage opening disagreement')
            openings.append(opening)
        shared=mp.compress(root,ctx,count,indices,[field_words(q['leaf']) for q in openings],
                           [[decode_hash(v) for v in q['path']] for q in openings])
        for leaf in shared['leaves']:
            require(len(leaf)==4*wordcount,'stage leaf size');out.extend(leaf)
        for sibling in shared['siblings']:out.extend(sibling)
    _,fixed,maximum=limits(args,terminal_degree)
    require(fixed<=len(out)<=maximum,'encoded size bound');return bytes(out)

def decode(data,*,terminal_degree=1,**args):
    count,fixed,maximum=limits(args,terminal_degree)
    require(type(data)is bytes and fixed<=len(data)<=maximum,'codec size bound')
    require(data[:len(MAGIC)]==MAGIC,'codec magic');offset=len(MAGIC)
    def read(size):
        nonlocal offset
        require(offset+size<=len(data),'codec truncation');v=data[offset:offset+size];offset+=size;return v
    def words(n):
        values=list(struct.unpack('<'+'I'*n,read(4*n)))
        require(all(v<P for v in values),'noncanonical field word');return values
    rounds=[]
    for _ in range(count):rounds.append({'quadratic':[words(4) for _ in range(3)],'next_root':read(48).hex()})
    terminal={'profile':'near-pq384-terminal-v1','coefficients':[[words(4) for _ in range(terminal_degree)]]}
    stages=header(args,terminal_degree,rounds,terminal)
    expected=fixed+sum(len(set(indices))*4*wordcount+len(mp.boundary(n,indices))*48
                       for _,_,n,indices,wordcount in stages)
    require(len(data)==expected,'canonical total size')
    stage_openings=[]
    for root,ctx,n,indices,wordcount in stages:
        leaves=[field_words(words(wordcount)) for _ in mp.shape(n,indices)]
        siblings=[read(48) for _ in mp.boundary(n,indices)]
        expanded,paths=mp.expand(root,ctx,n,indices,{'leaves':leaves,'siblings':siblings})
        stage_openings.append([{'leaf':list(struct.unpack('<'+'I'*wordcount,leaf)),
                                'path':[v.hex() for v in path]} for leaf,path in zip(expanded,paths)])
    require(offset==len(data),'trailing bytes')
    queries=[[{'source':stage_openings[j][i],'next':stage_openings[j+1][i]}
              for j in range(count)] for i in range(gc.QUERIES)]
    proof={'profile':gc.PROFILE,'rounds':rounds,'terminal':terminal,'queries':queries}
    require(gc.verify(proof,terminal_degree=terminal_degree,**args),'decoded proof rejected')
    return proof

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    args=json.loads(Path(sys.argv[2]).read_text())
    for key in ('statement','parent_binding','expected_root'):args[key]=bytes.fromhex(args[key])
    decode(Path(sys.argv[1]).read_bytes(),terminal_degree=int(sys.argv[3]),**args)
    print('PASS: authenticated globalchain binary; unchanged diagnostic verifier')
