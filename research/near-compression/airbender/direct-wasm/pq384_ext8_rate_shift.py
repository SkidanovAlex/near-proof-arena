"""One explicit rate-shift/constraint-accumulation prerequisite, not WHIR soundness.
D32/domain128 -> D8/domain64; final coefficients disclosed for diagnostic
same-candidate binding. Four consistency samples are an algebra test profile.
"""
import pq384_ext8_reusable as p
e=p.e;h=p.h
PROFILE='near-ext8-rate-shift-accumulator-diagnostic-v1'
QUERIES=4

def dot(a,b):
    h.require(len(a)==len(b),'dot shape');v=e.ZERO
    for x,y in zip(a,b):v=e.add(v,e.mul(x,y))
    return v
def mono(x):return [e.power(x,i) for i in range(8)]
def candidate_context(seed):return h.hash_parts(b'rate-shift/candidate',PROFILE.encode(),seed,h.u64(8),h.u64(64))
def candidate_tree(cs,ctx):
    h.require(len(cs)==8,'candidate degree');omega=pow(440564289,(1<<27)//64,e.P)
    vals=e.fft([e.canonical(c) for c in cs]+[e.ZERO]*56,omega)
    leaves=[p.extbytes(v) for v in vals];root,layers=h.merkle_tree(leaves,ctx)
    return dict(root=root,layers=layers,leaves=leaves)
def start(cfg,root):
    h.require(cfg['degree']==32 and cfg['queries']==QUERIES,'fixed diagnostic shape');return h.Transcript(PROFILE.encode()+p.config_bytes(cfg)+root)
def ood(t):
    for _ in range(64):
        draw,_=t.draw(b'rate-shift/ood-outside-base',1,8);z=tuple(draw[0])
        if any(z[1:]):return z
    raise ValueError('OOD rejection limit')
def folded_query(openings,root,ctx,index,rs):
    h.require(type(openings)is list and len(openings)==2,'coset shape')
    a,c=p.read_opening(openings[0],root,ctx,32,index,True)
    b,d=p.read_opening(openings[1],root,ctx,32,index+32,True)
    vals=[a,b,c,d];omega=pow(440564289,(1<<27)//128,e.P);x=pow(omega,index,e.P);iota=pow(omega,32,e.P)
    pieces=[]
    for k in range(4):
        v=e.ZERO
        for j,value in enumerate(vals):v=e.add(v,e.scale(value,pow(iota,(-j*k)%4,e.P)))
        pieces.append(e.scale(v,pow(4*pow(x,k,e.P)%e.P,-1,e.P)))
    return e.affine_fold(e.affine_fold(pieces,rs[0]),rs[1])[0]
def accumulate(w,claim,z,y,points,values,gamma):
    out=list(w);value=claim;power=gamma
    for x,v in [(z,y)]+list(zip(points,values)):
        out=[e.add(a,e.mul(power,b)) for a,b in zip(out,mono(x))]
        value=e.add(value,e.mul(power,v));power=e.mul(power,gamma)
    return out,value

def prove(coeff,cfg,root,alter=None,wrong_ood=False):
    source=p.source_tree(coeff,cfg);h.require(source['root']==root,'source root')
    t=start(cfg,root);cs=[e.base(x) for x in coeff];w=p.eqweights(cfg['point']);claim=e.canonical(cfg['claim']);rounds=[];rs=[]
    for _ in range(2):
        wire=[list(v) for v in e.quadratic(cs,w)];r,claim=p.round_start(t,wire,claim);rs.append(r);rounds.append(wire)
        cs=e.affine_fold(cs,r);w=e.affine_fold(w,r)
    candidate=alter(cs,w) if alter else cs
    ctx=candidate_context(t.seed);tree=candidate_tree(candidate,ctx);t.commit(b'rate-shift/next-root',tree['root'])
    z=ood(t);y=e.evaluate(candidate,z)
    if wrong_ood:y=e.add(y,e.ONE)
    t.commit(b'rate-shift/ood-value',p.extbytes(y));indices=p.sample(t,32,QUERIES)
    draw,_=t.draw(b'rate-shift/mixing',1,8);gamma=tuple(draw[0])
    openings=[[p.opening(source,i),p.opening(source,i+32)] for i in indices]
    return dict(profile=PROFILE,quadratics=rounds,next_root=tree['root'].hex(),ood_value=list(y),source_queries=openings,terminal=[list(v) for v in candidate])

def inspect(proof,cfg,root):
    h.require(type(proof)is dict and set(proof)=={'profile','quadratics','next_root','ood_value','source_queries','terminal'} and proof['profile']==PROFILE,'proof fields')
    h.require(type(root)is bytes and len(root)==48,'root');t=start(cfg,root);w=p.eqweights(cfg['point']);claim=e.canonical(cfg['claim']);rs=[]
    h.require(type(proof['quadratics'])is list and len(proof['quadratics'])==2,'fold count')
    for wire in proof['quadratics']:
        r,claim=p.round_start(t,wire,claim);rs.append(r);w=e.affine_fold(w,r)
    ctx=candidate_context(t.seed);nextroot=p.hashread(proof['next_root']);t.commit(b'rate-shift/next-root',nextroot)
    z=ood(t);y=e.canonical(proof['ood_value']);t.commit(b'rate-shift/ood-value',p.extbytes(y));indices=p.sample(t,32,QUERIES)
    draw,_=t.draw(b'rate-shift/mixing',1,8);gamma=tuple(draw[0])
    h.require(type(proof['source_queries'])is list and len(proof['source_queries'])==QUERIES,'query count')
    values=[folded_query(q,root,p.source_context(cfg),i,rs) for q,i in zip(proof['source_queries'],indices)]
    omega=pow(440564289,(1<<27)//32,e.P);points=[e.base(pow(omega,i,e.P)) for i in indices]
    terminal=proof['terminal'];h.require(type(terminal)is list and len(terminal)==8,'terminal size');cs=[e.canonical(v) for v in terminal]
    h.require(candidate_tree(cs,ctx)['root']==nextroot,'candidate root reconstruction')
    neww,newclaim=accumulate(w,claim,z,y,points,values,gamma)
    errors=[e.sub(dot(cs,w),claim),e.sub(e.evaluate(cs,z),y)]+[e.sub(e.evaluate(cs,x),v) for x,v in zip(points,values)]
    residual=e.sub(dot(cs,neww),newclaim)
    h.require(e.evaluate(errors,gamma)==residual,'accumulator polynomial parity')
    return dict(residual=residual,errors=errors,gamma=gamma,weights=w,claim=claim,z=z,y=y,points=points,values=values,coefficients=cs,indices=indices)
def verify(proof,cfg,root):
    result=inspect(proof,cfg,root);h.require(result['residual']==e.ZERO,'aggregate residual');return True
