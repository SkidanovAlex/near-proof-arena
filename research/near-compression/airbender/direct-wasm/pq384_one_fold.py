"""One-round packed PCS experiment: D128 → D64 exact terminal, one lane.

SHA384/Ext4, eight diagnostic queries. NOT a certified proximity protocol or
128-bit PQ scheme. No complete AIR transcript integration. Source is native
packed-v2 base-field encoding; terminal uses terminal-v1 Ext4 encoding.
"""
from pq384_primitives import P, Transcript, require, field_words, merkle_tree, merkle_path, verify_path
from packed_claim_handoff import derive_handoff, canonical_ext, vector_bytes, packing_context
from packed_disclosure import scalar_eval
from pq384_terminal import terminal_context, reconstructed_root, verify_terminal, horner
from check_whir_handoff import add, sub, mul

ZERO=(0,0,0,0);ONE=(1,0,0,0)
DEGREE=128;HALF=256;QUERIES=8


def base(v):return (v%P,0,0,0)


def public(args):
    require(type(args['log_rows'])is int and 1<=args['log_rows']<=7,'one-fold rows')
    require(args['width']==args['packing'] and
            (1<<args['log_rows'])*args['packing']==DEGREE,'one-fold single lane shape')
    h=derive_handoff(**args)
    t=Transcript(b'NEAR-PQ384-ONE-FOLD-DIAGNOSTIC-V1/D128/Q8')
    t.commit(b'packed-handoff',bytes.fromhex(h['transcript_seed_hex']))
    return h,t


def weights(point):
    result=[ONE]
    for r in point:
        r=canonical_ext(r);result += [mul(v,r) for v in result]
    return result


def polynomial(cs,r):return add(cs[0],mul(r,add(cs[1],mul(r,cs[2]))))


def round_state(h,t,round_coefficients):
    require(isinstance(round_coefficients,list) and len(round_coefficients)==3,'quadratic shape')
    cs=[canonical_ext(v) for v in round_coefficients]
    require(add(cs[0],add(add(cs[0],cs[1]),cs[2]))==tuple(h['lane_claims'][0]),
            'sumcheck endpoints')
    t.commit(b'sumcheck-quadratic',vector_bytes(cs))
    draws,_=t.draw(b'fold-challenge',1,4);r=tuple(draws[0])
    stage=t.seed
    scale=add(ONE,mul(r,sub(tuple(h['packed_point'][0]),ONE)))
    ws=[mul(scale,v) for v in weights(h['packed_point'][1:])]
    return r,stage,ws,polynomial(cs,r)


def query_indices(t,root):
    require(type(root)is bytes and len(root)==48,'next root')
    t.commit(b'next-oracle-root',root)
    indices=[]
    for _ in range(4096):
        draws,_=t.draw(b'fold-query',1,1);v=draws[0][0]
        if v<P//HALF*HALF:indices.append(v%HALF)
        if len(indices)==QUERIES:return indices
    raise ValueError('query sampler exhausted')


def decode_hash(value):
    require(type(value)is str and len(value)==96 and
            all(c in '0123456789abcdef' for c in value),'canonical hash hex')
    return bytes.fromhex(value)


def verify(proof,**args):
    h,t=public(args)
    require(type(proof)is dict and set(proof)=={'profile','round','next_root','queries','terminal'}
            and proof['profile']=='near-pq384-one-fold-v1','fold proof fields')
    r,stage,ws,claim=round_state(h,t,proof['round'])
    root=decode_hash(proof['next_root']);indices=query_indices(t,root)
    verify_terminal(proof['terminal'],expected_root=root,stage_binding=stage,
                    degree_bound=64,domain_size=256,lanes=1,weights=[[list(v) for v in ws]],claim=claim)
    coefficients=[canonical_ext(v) for v in proof['terminal']['coefficients'][0]]
    require(isinstance(proof['queries'],list) and len(proof['queries'])==QUERIES,'query count')
    context=bytes.fromhex(h['context_hex']);omega=pow(440564289,(1<<27)//512,P)
    for index,q in zip(indices,proof['queries']):
        require(type(q)is dict and set(q)=={'leaf','path'} and isinstance(q['leaf'],list)
                and len(q['leaf'])==2 and isinstance(q['path'],list),'query shape')
        leaf=field_words(q['leaf']);path=[decode_hash(v) for v in q['path']]
        verify_path(args['expected_root'],context,HALF,index,leaf,path)
        x=pow(omega,index,P);a,b=q['leaf']
        even=base((a+b)*pow(2,-1,P));odd=base((a-b)*pow(2*x,-1,P))
        folded=add(even,mul(r,sub(odd,even)))
        require(folded==horner(coefficients,base(x*x)),'fold query consistency')
    return True


def prove(rows,**args):
    h,t=public(args);n=1<<args['log_rows'];width=args['width']
    require(isinstance(rows,list) and len(rows)==n and
            all(isinstance(row,list) and len(row)==width and
                all(type(v)is int and 0<=v<P for v in row) for row in rows),'source rows')
    cs=[rows[row][col] for col in range(width) for row in range(n)]
    bit=1
    while bit<DEGREE:
        for i in range(DEGREE):
            if i&bit:cs[i]=(cs[i]-cs[i^bit])%P
        bit*=2
    omega=pow(440564289,(1<<27)//512,P)
    leaves=[field_words([scalar_eval(cs,pow(omega,i,P)),scalar_eval(cs,(-pow(omega,i,P))%P)])
            for i in range(HALF)]
    root,layers=merkle_tree(leaves,bytes.fromhex(h['context_hex']))
    require(root==args['expected_root'],'source commitment mismatch')
    tail_weights=weights(h['packed_point'][1:]);z=tuple(h['packed_point'][0])
    quadratic=[ZERO,ZERO,ZERO]
    for i,w in enumerate(tail_weights):
        a,b=base(cs[2*i]),base(cs[2*i+1]);delta=sub(b,a);dw=mul(sub(z,ONE),w)
        terms=[mul(a,w),add(mul(delta,w),mul(a,dw)),mul(delta,dw)]
        quadratic=[add(v,u) for v,u in zip(quadratic,terms)]
    r,stage,ws,claim=round_state(h,t,[list(v) for v in quadratic])
    folded=[add(base(a),mul(r,sub(base(b),base(a)))) for a,b in zip(cs[::2],cs[1::2])]
    context,next_omega=terminal_context(stage,64,256,1)
    next_root=reconstructed_root([folded],context,256,next_omega)
    indices=query_indices(t,next_root)
    import struct
    proof={'profile':'near-pq384-one-fold-v1','round':[list(v) for v in quadratic],
           'next_root':next_root.hex(),'terminal':{'profile':'near-pq384-terminal-v1',
           'coefficients':[[list(v) for v in folded]]},
           'queries':[{'leaf':list(struct.unpack('<2I',leaves[i])),
                       'path':[v.hex() for v in merkle_path(layers,i)]} for i in indices]}
    require(verify(proof,**args),'generated proof failed')
    return proof
