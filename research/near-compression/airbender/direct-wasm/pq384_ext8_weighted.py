"""Ext8 weighted multi-branch folding diagnostic. No proximity/QROM claim.
Source commitments use opening-independent packed base-field contexts.
Verifier derives lane weights externally; proof cannot select its opening claim.
"""
import json, struct
import pq384_ext8_reference as f
import pq384_primitives as h
from packed_claim_handoff import packing_context
from pq384_ext8_input_weights import lane_weights,lane_weight_mle
from pq384_ext8_terminal_gkr import vector_bytes,eqs
from pq384_ext8_reusable import hashread,sample
PROFILE='near-pq384-ext8-weighted-joint-diagnostic-v1'

class Tree:
    def __init__(self,leaves,context):
        self.leaves=leaves;self.context=context;self.root,self.layers=h.merkle_tree(leaves,context);self.half=len(leaves)
    def opening(self,i):return dict(leaf=list(struct.unpack('<'+'I'*(len(self.leaves[i])//4),self.leaves[i])),path=[x.hex() for x in h.merkle_path(self.layers,i)])

class Source(Tree):
    def __init__(self,rows,packing,native):
        h.require(len(rows)>=2 and len(rows)&(len(rows)-1)==0,'row count')
        width=len(rows[0]);self.context=packing_context(len(rows).bit_length()-1,width,packing)
        self.degree=len(rows)*packing;h.require(self.degree<=262144,'degree')
        h.require(all(len(row)==width and all(type(x)is int and 0<=x<f.P for x in row) for row in rows),'base rows')
        self.coeff=[];evaluations=[]
        for start in range(0,width,packing):
            cs=[row[c] if c<width else 0 for c in range(start,start+packing) for row in rows];bit=1
            while bit<len(cs):
                for i in range(len(cs)):
                    if i&bit:cs[i]=(cs[i]-cs[i^bit])%f.P
                bit*=2
            self.coeff.append(cs);evaluations.append([x[0] for x in native.fft([f.base(x) for x in cs],lde4=True)])
        self.lanes=len(self.coeff);half=2*self.degree
        leaves=[h.field_words([v for lane in evaluations for v in (lane[i],lane[i+half])]) for i in range(half)]
        super().__init__(leaves,self.context)
    def coefficients(self,j):return self.coeff[j]

def context(stage,d):return h.hash_parts(b'ext8-weighted-fold',stage,h.u64(d))
def folded_tree(cs,ctx,native):
    v=native.fft(cs,lde4=True);half=len(v)//2
    return Tree([vector_bytes([v[i],v[i+half]]) for i in range(half)],ctx)
def public(statement,parent,branches,claim,queries):
    h.require(type(statement)is bytes and type(parent)is bytes,'statement')
    h.require(type(queries)is int and 1<=queries<=4096,'queries')
    h.require(type(branches)is list and 1<=len(branches)<=128,'branches');degrees=[];contexts=[]
    for b in branches:
        h.require(set(b)=={'root','log_rows','width','packing','row_point','lanes'},'branch fields')
        n,w,p=b['log_rows'],b['width'],b['packing'];ctx=packing_context(n,w,p);d=(1<<n)*p
        h.require(2<=d<=262144 and len(b['row_point'])==n,'branch degree/point')
        hashread(b['root']);[f.canonical(v) for v in b['row_point']]
        h.require(len(b['lanes'])==(w+p-1)//p<=64,'lanes')
        for j,pair in enumerate(b['lanes']):
            h.require(len(pair)==2 and all(len(side)==p for side in pair),'lane shape')
            for side in pair:
                for c,x in enumerate(side):
                    v=f.canonical(x)
                    if j*p+c>=w:h.require(v==f.ZERO,'padding weight')
        degrees.append(d);contexts.append(ctx)
    claim=f.canonical(claim)
    digest=h.hash_parts(PROFILE.encode(),statement,parent,h.u64(queries),json.dumps(branches,sort_keys=True,separators=(',',':')).encode(),vector_bytes([claim]))
    return degrees,max(degrees),contexts,h.Transcript(digest),claim

def round_start(t,wire,claim):
    h.require(len(wire)==3,'quadratic');q=[f.canonical(x) for x in wire]
    h.require(f.add(q[0],f.evaluate(q,f.ONE))==claim,'endpoint')
    t.commit(b'ext8-weighted-quadratic',vector_bytes(q));r=tuple(t.draw(b'ext8-weighted-fold',1,8)[0][0])
    return r,t.seed,f.evaluate(q,r)
def betas(branches,degrees,D,u):
    return [[lane_weight_mle(b['row_point'],a,c,u[(D//d).bit_length()-1:]) for a,c in b['lanes']] for b,d in zip(branches,degrees)]
def terminal_check(t,value,root,ctx,u,rs,claim):
    value=f.canonical(value);weight=f.ONE
    for a,b in zip(u,rs):weight=f.mul(weight,f.add(f.mul(a,b),f.mul(f.sub(f.ONE,a),f.sub(f.ONE,b))))
    h.require(f.mul(value,weight)==claim,'terminal claim')
    leaf=vector_bytes([value,value]);expected,_=h.merkle_tree([leaf,leaf],ctx)
    h.require(expected==root,'terminal root');t.commit(b'ext8-weighted-terminal',vector_bytes([value]))

def prove(caches,native,statement,parent,branches,claim, *, queries):
    degrees,D,contexts,t,claim=public(statement,parent,branches,claim,queries)
    h.require(len(caches)==len(branches),'cache count');states=[]
    for cache,b,d,ctx in zip(caches,branches,degrees,contexts):
        h.require(cache.root.hex()==b['root'] and cache.context==ctx and cache.degree==d and cache.lanes==len(b['lanes']),'source binding')
        low=(D//d).bit_length()-1
        for j,(a,c) in enumerate(b['lanes']):
            cs=[f.base(x) for x in cache.coefficients(j)];ws=lane_weights(b['row_point'],a,c)
            q=native.quadratic(cs,ws);dot=f.add(q[0],f.evaluate(q,f.ONE));states.append([cs,ws,low,f.ONE,dot])
    reduction=[];u=[]
    for bit in range(D.bit_length()-1):
        q=[f.ZERO]*3
        for cs,ws,low,scale,dot in states:
            part=[dot,f.sub(f.ZERO,dot),f.ZERO] if bit<low else native.quadratic(cs,ws)
            q=[f.add(a,f.mul(scale,b)) for a,b in zip(q,part)]
        r,_,claim=round_start(t,q,claim);u.append(r);reduction.append(q)
        for state in states:
            if bit<state[2]:state[3]=f.mul(state[3],f.sub(f.ONE,r))
            else:state[0]=native.affine_fold(state[0],r);state[1]=native.affine_fold(state[1],r)
    bs=betas(branches,degrees,D,u);at=f.ZERO
    for state,beta in zip(states,[x for row in bs for x in row]):at=f.add(at,f.mul(f.mul(state[0][0],state[3]),beta))
    h.require(at==claim,'reduction terminal');combined=[f.ZERO]*D
    for cache,powers in zip(caches,bs):
        for j,power in enumerate(powers):
            for i,c in enumerate(cache.coefficients(j)):combined[i*(D//cache.degree)]=f.add(combined[i*(D//cache.degree)],f.scale(power,c))
    weights=eqs(u);rounds=[];trees=[];rs=[];d=D
    while d>1:
        q=native.quadratic(combined,weights);r,stage,claim=round_start(t,q,claim);rs.append(r)
        combined=native.affine_fold(combined,r);weights=native.affine_fold(weights,r);d//=2
        tree=folded_tree(combined,context(stage,d),native);trees.append(tree)
        t.commit(b'ext8-weighted-root',tree.root);rounds.append(dict(quadratic=q,root=tree.root.hex()))
    terminal=combined[0];terminal_check(t,terminal,trees[-1].root,trees[-1].context,u,rs,claim)
    openings=[dict(sources=[c.opening(s%(2*d)) for c,d in zip(caches,degrees)],folds=[tr.opening(s%tr.half) for tr in trees]) for s in sample(t,4*D,queries)]
    return dict(profile=PROFILE,reduction=reduction,rounds=rounds,terminal=terminal,queries=openings)

def read_opening(op,root,ctx,half,index,base,powers):
    h.require(set(op)=={'leaf','path'} and len(op['leaf'])==(2*len(powers) if base else 16),'opening shape')
    h.require(len(op['path'])==half.bit_length()-1,'path length')
    h.verify_path(root,ctx,half,index,h.field_words(op['leaf']),[hashread(x) for x in op['path']])
    if not base:return f.canonical(op['leaf'][:8]),f.canonical(op['leaf'][8:])
    a=b=f.ZERO
    for j,power in enumerate(powers):a=f.add(a,f.scale(power,op['leaf'][2*j]));b=f.add(b,f.scale(power,op['leaf'][2*j+1]))
    return a,b

def verify(proof,statement,parent,branches,claim, *, queries):
    degrees,D,contexts,t,claim=public(statement,parent,branches,claim,queries);n=D.bit_length()-1
    h.require(set(proof)=={'profile','reduction','rounds','terminal','queries'} and proof['profile']==PROFILE,'proof fields')
    h.require(len(proof['reduction'])==len(proof['rounds'])==n and len(proof['queries'])==queries,'proof lengths');u=[]
    for q in proof['reduction']:r,_,claim=round_start(t,q,claim);u.append(r)
    bs=betas(branches,degrees,D,u);roots=[];contexts_fold=[];rs=[];d=D
    for rd in proof['rounds']:
        h.require(set(rd)=={'quadratic','root'},'round fields');r,stage,claim=round_start(t,rd['quadratic'],claim);rs.append(r);d//=2
        root=hashread(rd['root']);roots.append(root);contexts_fold.append(context(stage,d));t.commit(b'ext8-weighted-root',root)
    terminal_check(t,proof['terminal'],roots[-1],contexts_fold[-1],u,rs,claim)
    for s,q in zip(sample(t,4*D,queries),proof['queries']):
        h.require(set(q)=={'sources','folds'} and len(q['sources'])==len(branches) and len(q['folds'])==n,'query shape');a=b=f.ZERO
        for op,branch,d,ctx,powers in zip(q['sources'],branches,degrees,contexts,bs):
            pair=read_opening(op,hashread(branch['root']),ctx,2*d,s%(2*d),True,powers)
            if d<D:pair=(pair[(s%(4*d))//(2*d)],)*2
            a=f.add(a,pair[0]);b=f.add(b,pair[1])
        degree=D
        for op,root,ctx,r in zip(q['folds'],roots,contexts_fold,rs):
            pair=read_opening(op,root,ctx,degree,s%degree,False,[f.ONE])
            omega=pow(440564289,(1<<27)//(4*degree),f.P);x=pow(omega,s%(2*degree),f.P)
            even=f.scale(f.add(a,b),pow(2,-1,f.P));odd=f.scale(f.sub(a,b),pow(2*x,-1,f.P))
            h.require(f.add(even,f.mul(r,f.sub(odd,even)))==pair[(s%(2*degree))//degree],'fold consistency')
            a,b=pair;degree//=2
    return True


if __name__=='__main__':
    import argparse
    from pathlib import Path
    parser=argparse.ArgumentParser();parser.add_argument('capture',type=Path);args=parser.parse_args()
    cfg=json.loads((args.capture/'opening.json').read_text());proof=json.loads((args.capture/'proof.json').read_text())
    verify(proof,bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']),cfg['branches'],cfg['claim'],queries=cfg['queries'])
    print('PASS weighted Ext8 opening')
