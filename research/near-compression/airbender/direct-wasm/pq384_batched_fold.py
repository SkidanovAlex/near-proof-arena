"""Multi-round batched-lane SHA384 folding experiment, D128..262144 → D64.

Eight queries per round; Ext4 diagnostic, not a soundness/security claim.
Every query authenticates BOTH adjacent oracles. Responses enter the transcript
before the following round. No AIR integration, recursion or zero knowledge.
"""
import json
import struct
from pq384_primitives import P,Transcript,require,u64,field_words,merkle_tree,merkle_path,verify_path
from packed_claim_handoff import derive_handoff,canonical_ext,vector_bytes
from pq384_terminal import terminal_context,verify_terminal
from pq384_one_fold import ZERO,ONE,base,weights,polynomial,decode_hash
from check_whir_handoff import add,sub,mul

QUERIES=8


def public(args):
    require(type(args['log_rows'])is int and 1<=args['log_rows']<=13,'fold rows')
    h=derive_handoff(**args);degree=(1<<args['log_rows'])*args['packing']
    require(1<=len(h['lane_claims'])<=64 and 128<=degree<=262144,'batched fold shape')
    t=Transcript(b'NEAR-PQ384-BATCHED-FOLD-DIAGNOSTIC-V1/Q8/terminal64')
    t.commit(b'packed-handoff',bytes.fromhex(h['transcript_seed_hex']))
    draws,_=t.draw(b'lane-batching-challenge',1,4)
    alpha=tuple(draws[0]);powers=[];power=ONE;claim=ZERO
    for value in h['lane_claims']:
        powers.append(power);claim=add(claim,mul(power,tuple(value)));power=mul(power,alpha)
    h['batch_powers']=powers;h['batched_claim']=claim
    return h,t,degree


def oracle_context(stage,degree):
    if degree==64:return terminal_context(stage,64,256,1)
    require(64<degree<=262144 and degree&(degree-1)==0,'intermediate degree')
    omega=pow(440564289,(1<<27)//(4*degree),P)
    return (b'NEAR-PQ384-FOLD-ORACLE-V1/Ext4-v4=11/natural-domain/lane-pairs/le-u32'
            +u64(len(stage))+stage+b''.join(u64(v) for v in (P,degree,4*degree,omega))),omega


def scale(a,k):return tuple(v*k%P for v in a)


def fft(coefficients,omega):
    a=list(coefficients);n=len(a);j=0
    for i in range(1,n):
        bit=n>>1
        while j&bit:j^=bit;bit>>=1
        j^=bit
        if i<j:a[i],a[j]=a[j],a[i]
    size=2
    while size<=n:
        step=pow(omega,n//size,P)
        for start in range(0,n,size):
            w=1
            for i in range(start,start+size//2):
                v=scale(a[i+size//2],w);u=a[i]
                a[i]=add(u,v);a[i+size//2]=sub(u,v);w=w*step%P
        size*=2
    return a


def tree(coefficients,context,first=False):
    degree=len(coefficients);domain=4*degree
    omega=pow(440564289,(1<<27)//domain,P)
    codeword=fft(coefficients+[ZERO]*(domain-degree),omega)
    if first:
        require(all(v[1:]==(0,0,0) for v in codeword),'base source oracle')
        leaves=[field_words([codeword[i][0],codeword[i+domain//2][0]]) for i in range(domain//2)]
    else:leaves=[field_words(list(codeword[i])+list(codeword[i+domain//2])) for i in range(domain//2)]
    root,layers=merkle_tree(leaves,context)
    return root,layers,leaves


def source_tree(matrices,context):
    degree=len(matrices[0]);domain=4*degree
    omega=pow(440564289,(1<<27)//domain,P)
    encoded=[fft(cs+[ZERO]*(domain-degree),omega) for cs in matrices]
    require(all(v[1:]==(0,0,0) for lane in encoded for v in lane),'base source matrix')
    leaves=[field_words([v for lane in encoded for v in (lane[i][0],lane[i+domain//2][0])])
            for i in range(domain//2)]
    root,layers=merkle_tree(leaves,context)
    return root,layers,leaves


def fold(values,r):return [add(a,mul(r,sub(b,a))) for a,b in zip(values[::2],values[1::2])]


def round_start(t,cs,claim):
    require(isinstance(cs,list) and len(cs)==3,'round quadratic')
    cs=[canonical_ext(v) for v in cs]
    require(add(cs[0],add(add(cs[0],cs[1]),cs[2]))==claim,'sumcheck endpoints')
    t.commit(b'sumcheck-quadratic',vector_bytes(cs));draw,_=t.draw(b'fold-challenge',1,4)
    r=tuple(draw[0]);return r,t.seed,polynomial(cs,r)


def indices(t,root,half):
    t.commit(b'next-oracle-root',root);result=[]
    for _ in range(4096):
        values,_=t.draw(b'fold-query',1,1);v=values[0][0]
        if v<P//half*half:result.append(v%half)
        if len(result)==QUERIES:return result
    raise ValueError('query sampler exhausted')


def absorb_queries(t,queries):
    # Verifier calls only after shape, canonical fields, paths and folds pass.
    t.commit(b'authenticated-query-responses',json.dumps(queries,sort_keys=True,separators=(',',':')).encode())


def opening(layers,leaves,index):
    return {'leaf':list(struct.unpack('<'+'I'*(len(leaves[index])//4),leaves[index])),
            'path':[v.hex() for v in merkle_path(layers,index)]}


def check_opening(q,root,context,half,index,first,powers):
    require(type(q)is dict and set(q)=={'leaf','path'} and isinstance(q['leaf'],list)
            and len(q['leaf'])==(2*len(powers) if first else 8) and isinstance(q['path'],list),'opening shape')
    verify_path(root,context,half,index,field_words(q['leaf']),[decode_hash(v) for v in q['path']])
    if first:
        even,odd=ZERO,ZERO
        for lane,power in enumerate(powers):
            even=add(even,mul(power,base(q['leaf'][2*lane])))
            odd=add(odd,mul(power,base(q['leaf'][2*lane+1])))
        return even,odd
    return tuple(q['leaf'][:4]),tuple(q['leaf'][4:])


def verify(proof,**args):
    h,t,degree=public(args);initial=degree
    require(type(proof)is dict and set(proof)=={'profile','rounds','terminal'} and
            proof['profile']=='near-pq384-batched-fold-v1','proof fields')
    require(isinstance(proof['rounds'],list) and len(proof['rounds'])==degree.bit_length()-7,'round count')
    root=args['expected_root'];context=bytes.fromhex(h['context_hex'])
    claim=h['batched_claim'];weight_scale=ONE;stage=None
    for round_index,round_proof in enumerate(proof['rounds']):
        require(type(round_proof)is dict and set(round_proof)=={'quadratic','next_root','queries'},'round fields')
        r,stage,claim=round_start(t,round_proof['quadratic'],claim)
        # Adjacent monomial weights are (w, point[i]*w). No division
        # is needed, including when the accumulated factor becomes zero.
        weight_scale=mul(weight_scale,add(ONE,mul(r,sub(h['packed_point'][round_index],ONE))))
        next_root=decode_hash(round_proof['next_root']);next_context,_=oracle_context(stage,degree//2)
        queries=round_proof['queries'];sample=indices(t,next_root,2*degree)
        require(isinstance(queries,list) and len(queries)==QUERIES,'query count')
        omega=pow(440564289,(1<<27)//(4*degree),P)
        for i,q in zip(sample,queries):
            require(type(q)is dict and set(q)=={'source','next'},'query fields')
            a,b=check_opening(q['source'],root,context,2*degree,i,degree==initial,h['batch_powers'])
            pair=check_opening(q['next'],next_root,next_context,degree,i%degree,False,h['batch_powers'])
            x=pow(omega,i,P);even=scale(add(a,b),pow(2,-1,P));odd=scale(sub(a,b),pow(2*x,-1,P))
            require(add(even,mul(r,sub(odd,even)))==pair[i//degree],'fold consistency')
        absorb_queries(t,queries)
        root,context,degree=next_root,next_context,degree//2
    require(degree==64 and stage is not None,'terminal schedule')
    ws=[mul(weight_scale,w) for w in weights(h['packed_point'][len(proof['rounds']):])]
    verify_terminal(proof['terminal'],expected_root=root,stage_binding=stage,
                    degree_bound=64,domain_size=256,lanes=1,weights=[[list(v) for v in ws]],claim=claim)
    return True


def prove(rows,**args):
    h,t,degree=public(args);initial=degree;n=1<<args['log_rows'];width=args['width']
    require(isinstance(rows,list) and len(rows)==n and all(isinstance(row,list) and len(row)==width
        and all(type(v)is int and 0<=v<P for v in row) for row in rows),'source rows')
    matrices=[]
    for lane in range(len(h['batch_powers'])):
        cs=[rows[row][lane*args['packing']+col] if lane*args['packing']+col<width else 0
            for col in range(args['packing']) for row in range(n)]
        bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:cs[i]=(cs[i]-cs[i^bit])%P
            bit*=2
        matrices.append([base(v) for v in cs])
    root,layers,leaves=source_tree(matrices,bytes.fromhex(h['context_hex']))
    cs=[ZERO]*degree
    for power,coefficients in zip(h['batch_powers'],matrices):
        cs=[add(a,mul(power,b)) for a,b in zip(cs,coefficients)]
    ws=weights(h['packed_point']);claim=h['batched_claim']
    require(root==args['expected_root'],'source root mismatch');rounds=[]
    while degree>64:
        quadratic=[ZERO,ZERO,ZERO]
        for a,b,w,v in zip(cs[::2],cs[1::2],ws[::2],ws[1::2]):
            dc,dw=sub(b,a),sub(v,w)
            terms=[mul(a,w),add(mul(dc,w),mul(a,dw)),mul(dc,dw)]
            quadratic=[add(x,y) for x,y in zip(quadratic,terms)]
        wire=[list(v) for v in quadratic];r,stage,claim=round_start(t,wire,claim)
        cs,ws=fold(cs,r),fold(ws,r);next_context,_=oracle_context(stage,degree//2)
        next_root,next_layers,next_leaves=tree(cs,next_context)
        sample=indices(t,next_root,2*degree)
        queries=[{'source':opening(layers,leaves,i),'next':opening(next_layers,next_leaves,i%degree)} for i in sample]
        rounds.append({'quadratic':wire,'next_root':next_root.hex(),'queries':queries})
        absorb_queries(t,queries)
        root,layers,leaves,degree=next_root,next_layers,next_leaves,degree//2
    proof={'profile':'near-pq384-batched-fold-v1','rounds':rounds,
           'terminal':{'profile':'near-pq384-terminal-v1','coefficients':[[list(v) for v in cs]]}}
    require(verify(proof,**args),'generated proof failed');return proof
