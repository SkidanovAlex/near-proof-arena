"""Explicit routed SHA384/challenge relation for the fixed GKR transcript.

Hash outputs are recomputed here. A recursive circuit must instead constrain
all these hashes and the byte/range/scan operations; this is not that proof.
"""
import hashlib,json,struct
import pq384_primitives as p
import pq384_terminal_gkr as g
from swirl_bundle_codec import layer_rounds


def derive(layout,statement,proof,claim,expected_graph=None):
    inputs={'statement':statement,'claim':g.vector_bytes([g.ext(claim)])}
    layout_digest=g.hash_parts(g.PROFILE,json.dumps(layout,sort_keys=True,separators=(',',':')).encode())
    nodes=[];digests=[];draws=[];challenges={}
    def literal(x):return ['literal',x.hex()]
    def external(name,data):
        if name in inputs:raise ValueError('duplicate transcript input')
        inputs[name]=data;return ['input',name]
    def resolve(ref):
        tag,value=ref
        if tag=='literal':return bytes.fromhex(value)
        if tag=='input':return inputs[value]
        if tag=='hash' and type(value)is int and 0<=value<len(digests):return digests[value]
        raise ValueError('hash reference')
    def hp(tag,refs):
        parts=[resolve(r) for r in refs]
        wire=p.PREFIX+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))+b''.join(p.u64(len(x))+x for x in parts)
        digest=hashlib.sha384(wire).digest()
        node=dict(tag=tag.decode(),parts=refs,digest=digest.hex(),blocks=(len(wire)+144)//128)
        if expected_graph is not None:
            if len(nodes)>=len(expected_graph) or node!=expected_graph[len(nodes)]:raise ValueError('hash route or digest mismatch')
        ref=['hash',len(nodes)];nodes.append(node);digests.append(digest);return ref
    seed=hp(g.PROFILE,[['input','statement'],literal(layout_digest),['input','claim']])
    seed=hp(b'transcript/init',[seed])
    def commit_draw(seed,payload,name,max_blocks=4096):
        seed=hp(b'transcript/commit',[seed,literal(b'gkr-vector'),external(name,payload)])
        state=hp(b'transcript/request',[seed,literal(b'gkr-challenge'),literal(p.u64(1)),literal(p.u64(4))])
        values=[];rejected=0;scans=[]
        for counter in range(max_blocks):
            block=hp(b'transcript/squeeze',[state,literal(b'gkr-challenge'),literal(p.u64(counter))])
            state=hp(b'transcript/ratchet',[state,literal(b'gkr-challenge'),block])
            words=struct.unpack('<12I',resolve(block));needed=4-len(values);accepted=[];bad=0
            for word in words:
                if word>=2*p.P:bad+=1
                else:
                    accepted.append(word%p.P)
                    if len(accepted)==needed:break
            values.extend(accepted);rejected+=bad
            scans.append(dict(hash_node=block[1],needed=needed,words=list(words),accepted=accepted,rejected=bad))
            if len(values)==4:
                seed=hp(b'transcript/draw-result',[state,literal(b'gkr-challenge'),literal(p.u64(1)),literal(p.u64(4)),literal(p.u64(counter+1))])
                draws.append(dict(input=name,scans=scans,values=values,rejected=rejected,blocks=counter+1,next_seed=seed[1]))
                return seed,tuple(values)
        raise ValueError('sampler exhausted')
    counts=list(layer_rounds(layout))
    if proof['profile']!=g.PROFILE.decode() or len(proof['layers'])!=len(counts):raise ValueError('proof shape')
    for k,(part,count) in enumerate(zip(proof['layers'],counts)):
        if len(part['rounds'])!=count or len(part['inputs'])!=2:raise ValueError('layer shape')
        for j,row in enumerate(part['rounds']):
            if len(row)!=3:raise ValueError('round shape')
            seed,r=commit_draw(seed,g.vector_bytes(row),f'proof/{k}/round/{j}')
            challenges[f'challenge/{k}/{j}']=r
        seed,r=commit_draw(seed,g.vector_bytes(part['inputs']),f'proof/{k}/inputs')
        challenges[f'challenge/{k}/gamma']=r
    if expected_graph is not None and len(nodes)!=len(expected_graph):raise ValueError('extra hash nodes')
    return dict(inputs={k:v.hex() for k,v in inputs.items()},nodes=nodes,draws=draws,challenges=challenges)
