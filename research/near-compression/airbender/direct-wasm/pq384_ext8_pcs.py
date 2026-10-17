"""Versioned scalar-source Ext8 folding reference. Not full PCS/QROM soundness.
Verifier supplies complete config and mandatory source root. Initial claim is
coefficient-table equality-weight MLE, not polynomial evaluation at that point.
"""
import struct
import pq384_primitives as h
import pq384_ext8_reference as e
PROFILE='near-pq384-ext8-scalar-equality-fold-v1'

def extbytes(a):return h.field_words(list(e.canonical(a)))
def extread(b):
    h.require(len(b)==32,'Ext8 bytes');return e.canonical(list(struct.unpack('<8I',b)))
def hashread(x):
    h.require(type(x)is str and len(x)==96,'hash shape');v=bytes.fromhex(x);h.require(v.hex()==x,'canonical hash');return v

def config_bytes(config):
    h.require(type(config)is dict and set(config)=={'profile','degree','queries','point','claim','statement'},'config fields')
    h.require(config['profile']==PROFILE,'config profile');d=config['degree'];q=config['queries']
    h.require(type(d)is int and 2<=d<=1024 and d&(d-1)==0,'degree')
    h.require(type(q)is int and 1<=q<=4096,'query budget')
    h.require(type(config['point'])is list and len(config['point'])==d.bit_length()-1,'point dimension')
    h.require(type(config['statement'])is str and len(config['statement'])<=8192,'statement shape')
    statement=bytes.fromhex(config['statement']);h.require(statement.hex()==config['statement'],'canonical statement')
    return (PROFILE.encode()+h.u64(e.P)+h.u64(8)+h.u64(11)+h.u64(d)+h.u64(4*d)+h.u64(q)+
        b''.join(extbytes(a) for a in config['point'])+extbytes(config['claim'])+h.u64(len(statement))+statement)

def source_context(config):
    return h.hash_parts(b'ext8/source-context',config_bytes(config),b'base-pair-u32-le')
def fold_context(seed,d):return h.hash_parts(b'ext8/fold-context',seed,h.u64(d),b'ext8-pair-8xu32-le')
def start(config,expected_root):
    h.require(type(expected_root)is bytes and len(expected_root)==48,'mandatory expected root')
    return h.Transcript(config_bytes(config)+expected_root)
def eqweights(point):
    w=[e.ONE]
    for a in point:
        a=e.canonical(a);w=[e.mul(x,e.sub(e.ONE,a)) for x in w]+[e.mul(x,a) for x in w]
    return w

def tree(coeff,context,base_source):
    d=len(coeff);omega=pow(440564289,(1<<27)//(4*d),e.P)
    values=e.fft(coeff+[e.ZERO]*(3*d),omega)
    leaves=[]
    for i in range(2*d):
        a,b=values[i],values[i+2*d]
        if base_source:
            h.require(a[1:]==e.ZERO[1:] and b[1:]==e.ZERO[1:],'base source')
            leaves.append(h.field_words([a[0],b[0]]))
        else:leaves.append(extbytes(a)+extbytes(b))
    root,layers=h.merkle_tree(leaves,context)
    return dict(root=root,layers=layers,leaves=leaves)
def source_tree(coeff,config):
    h.require(type(coeff)is list and len(coeff)==config['degree'],'source shape')
    return tree([e.base(a) for a in coeff],source_context(config),True)
def opening(t,i):return dict(leaf=t['leaves'][i].hex(),path=[v.hex() for v in h.merkle_path(t['layers'],i)])
def read_opening(o,root,context,d,i,base_source):
    h.require(type(o)is dict and set(o)=={'leaf','path'},'opening fields')
    size=8 if base_source else 64
    h.require(type(o['leaf'])is str and len(o['leaf'])==2*size,'leaf size')
    leaf=bytes.fromhex(o['leaf']);h.require(leaf.hex()==o['leaf'],'canonical leaf')
    h.require(type(o['path'])is list and len(o['path'])==(2*d).bit_length()-1,'path length')
    path=[hashread(x) for x in o['path']]
    h.verify_path(root,context,2*d,i,leaf,path)
    if base_source:return tuple(e.base(x) for x in struct.unpack('<2I',leaf))
    return extread(leaf[:32]),extread(leaf[32:])
def round_start(t,wire,claim):
    h.require(type(wire)is list and len(wire)==3,'quadratic shape');q=[e.canonical(a) for a in wire]
    h.require(e.add(q[0],e.add(e.add(q[0],q[1]),q[2]))==claim,'quadratic endpoints')
    t.commit(b'ext8/quadratic',b''.join(extbytes(a) for a in q));draw,_=t.draw(b'ext8/fold',1,8)
    r=tuple(draw[0]);return r,e.evaluate(q,r)
def sample(t,domain,q):
    out=[]
    for _ in range(q*32):
        draw,_=t.draw(b'ext8/query',1,1);v=draw[0][0]
        if v<e.P//domain*domain:out.append(v%domain)
        if len(out)==q:return out
    raise ValueError('query rejection budget')
def prove(coeff,config,expected_root):
    t=start(config,expected_root);src=source_tree(coeff,config)
    h.require(src['root']==expected_root,'source root');cs=[e.base(a) for a in coeff];ws=eqweights(config['point'])
    claim=e.canonical(config['claim']);trees=[src];rounds=[];d=len(cs)
    while d>1:
        wire=[list(a) for a in e.quadratic(cs,ws)];r,claim=round_start(t,wire,claim)
        cs=e.affine_fold(cs,r);ws=e.affine_fold(ws,r);d//=2
        nxt=tree(cs,fold_context(t.seed,d),False);trees.append(nxt)
        t.commit(b'ext8/next-root',nxt['root']);rounds.append(dict(quadratic=wire,root=nxt['root'].hex()))
    h.require(e.mul(cs[0],ws[0])==claim,'terminal claim');terminal=list(cs[0]);t.commit(b'ext8/terminal',extbytes(terminal))
    queries=[]
    for s in sample(t,4*config['degree'],config['queries']):
        d=config['degree'];chain=[]
        for i in range(len(rounds)):
            chain.append([opening(trees[i],s%(2*d)),opening(trees[i+1],s%d)]);d//=2
        queries.append(chain)
    return dict(profile=PROFILE,rounds=rounds,terminal=terminal,queries=queries)
def verify(proof,config,expected_root):
    t=start(config,expected_root);d=config['degree'];initial=d
    h.require(type(proof)is dict and set(proof)=={'profile','rounds','terminal','queries'} and proof['profile']==PROFILE,'proof fields')
    h.require(type(proof['rounds'])is list and len(proof['rounds'])==d.bit_length()-1,'round count')
    roots=[expected_root];contexts=[source_context(config)];rs=[];claim=e.canonical(config['claim']);factor=e.ONE
    for j,rd in enumerate(proof['rounds']):
        h.require(type(rd)is dict and set(rd)=={'quadratic','root'},'round fields')
        r,claim=round_start(t,rd['quadratic'],claim);rs.append(r);u=e.canonical(config['point'][j])
        factor=e.mul(factor,e.add(e.mul(e.sub(e.ONE,r),e.sub(e.ONE,u)),e.mul(r,u)))
        d//=2;contexts.append(fold_context(t.seed,d));root=hashread(rd['root']);roots.append(root);t.commit(b'ext8/next-root',root)
    terminal=e.canonical(proof['terminal']);h.require(e.mul(factor,terminal)==claim,'terminal residual')
    # Complete constant oracle reconstruction, before sampling; no proximity premise.
    h.require(tree([terminal],contexts[-1],False)['root']==roots[-1],'terminal root')
    t.commit(b'ext8/terminal',extbytes(terminal))
    h.require(type(proof['queries'])is list and len(proof['queries'])==config['queries'],'query count')
    for s,chain in zip(sample(t,4*initial,config['queries']),proof['queries']):
        h.require(type(chain)is list and len(chain)==len(rs),'chain shape');d=initial
        for j,(r,q) in enumerate(zip(rs,chain)):
            h.require(type(q)is list and len(q)==2,'pair query shape');i=s%(2*d)
            a,b=read_opening(q[0],roots[j],contexts[j],d,i,j==0)
            nxt=read_opening(q[1],roots[j+1],contexts[j+1],d//2,s%d,False)
            omega=pow(440564289,(1<<27)//(4*d),e.P);x=pow(omega,i,e.P)
            even=e.scale(e.add(a,b),pow(2,-1,e.P));odd=e.scale(e.sub(a,b),pow(2*x,-1,e.P))
            h.require(e.add(even,e.mul(r,e.sub(odd,even)))==nxt[i//d],'fold consistency');d//=2
    return True
