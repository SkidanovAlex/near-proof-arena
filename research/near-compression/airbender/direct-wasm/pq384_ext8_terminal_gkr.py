"""Ext8 transcript-driven GKR diagnostic with optional native round kernels.

The verifier returns a REQUIRED input linear-functional opening obligation.
The public circuit is caller supplied and hashed, never selected by the proof.
The verifier uses Python field arithmetic, independently of the native kernel.
No cryptographic soundness or source-AIR compiler theorem is claimed here.
"""
import json
from pq384_ext8_reference import add,sub,mul,ZERO,ONE,base,canonical as ext,evaluate as poly
import pq384_ext8_reference as field
from pq384_terminal_gkr import layer_circuit as generic_layer_circuit

def vector_bytes(values):
    return b''.join(x.to_bytes(4,'little') for value in values for x in ext(value))
from pq384_primitives import Transcript,hash_parts,require

PROFILE=b'near-pq384-ext8-terminal-gkr-diagnostic-v1'


def eqs(point):
    out=[ONE]
    for r in point:
        out=[mul(x,sub(ONE,r)) for x in out]+[mul(x,r) for x in out]
    return out


def fold(v,r):return [add(a,mul(r,sub(b,a))) for a,b in zip(v[::2],v[1::2])]
def mle(v,point):
    for r in point:v=fold(v,r)
    return v[0]

def gate(op,a,b):return {'add':add,'sub':sub,'mul':mul}[op](a,b)
def size(n):return 1<<max(0,(n-1).bit_length())


def layer_circuit(circuit):return generic_layer_circuit(circuit,field=field)

def validate_layout(layout):
    require(set(layout)=={'input_size','private_capacity','constants','layers','root'},'layout fields')
    n=layout['input_size'];cap=layout['private_capacity']
    require(type(n)is int and n>=2 and n&(n-1)==0,'input size')
    require(type(cap)is int and 0<cap<=n,'private capacity')
    for i,c in layout['constants'].items():
        require(type(i)is int and cap<=i<n,'constant slot');ext(c)
    require(len(layout['layers'])>0,'empty circuit')
    for gates in layout['layers']:
        require(len(gates)>=2 and len(gates)&(len(gates)-1)==0,'layer size')
        for op,a,b in gates:
            require(op in ('add','sub','mul') and all(type(x)is int and 0<=x<n for x in (a,b)),'gate')
        n=len(gates)
    require(type(layout['root'])is int and 0<=layout['root']<n,'root')


def values(layout,private):
    require(len(private)==layout['private_capacity'],'private shape')
    v=[ext(x) for x in private]+[ZERO]*(layout['input_size']-len(private))
    for i,x in layout['constants'].items():v[i]=x
    allv=[v]
    for gates in layout['layers']:
        v=[gate(op,v[a],v[b]) for op,a,b in gates];allv.append(v)
    return allv


def begin(layout,statement,claim):
    digest=hash_parts(PROFILE,json.dumps(layout,sort_keys=True,separators=(',',':')).encode())
    t=Transcript(hash_parts(PROFILE,statement,digest,vector_bytes([ext(claim)])))
    return t


def draw(t):return tuple(t.draw(b'gkr-challenge',1,8)[0][0])
def commit(t,v):t.commit(b'gkr-vector',vector_bytes(v))

def interpolation(v):
    # Quadratic values at 0,1,2.
    c2=mul(sub(add(v[2],v[0]),add(v[1],v[1])),base((2013265921+1)//2))
    return [v[0],sub(sub(v[1],v[0]),c2),c2]


def wiring(gates,weights,ru,rv,a,b):
    eu,ev=eqs(ru),eqs(rv);ans=ZERO
    for (op,i,j),w in zip(gates,weights):
        ans=add(ans,mul(mul(w,mul(eu[i],ev[j])),gate(op,a,b)))
    return ans


def output_weights(length,queries):
    out=[ZERO]*length
    for q,scale in queries:
        e=eqs(q)
        require(len(e)==length,'output query dimension')
        out=[add(v,mul(scale,x)) for v,x in zip(out,e)]
    return out


def obligation(layout,queries,claim):
    w=output_weights(layout['input_size'],queries)
    for i,c in layout['constants'].items():claim=sub(claim,mul(w[i],c))
    return dict(private_claim=claim,queries=queries,private_weights=w[:layout['private_capacity']])


def prove(layout,statement,private,claim=ZERO, *, kernel=None):
    validate_layout(layout);claim=ext(claim)
    vs=values(layout,private);require(vs[-1][layout['root']]==claim,'false circuit output')
    t=begin(layout,statement,claim);n=(len(vs[-1])-1).bit_length()
    queries=[([base((layout['root']>>i)&1) for i in range(n)],ONE)];parts=[]
    for layer in range(len(layout['layers'])-1,-1,-1):
        gates=layout['layers'][layer];w=output_weights(len(gates),queries);v=vs[layer];m=(len(v)-1).bit_length()
        folded=list(v);gw=list(w);rounds=[];ru=[];rv=[];a=None
        for axis in (0,1):
            if axis:folded=list(v)
            for bit in range(m):
                if kernel is not None:
                    coeff=kernel.gkr_round(gates,gw,v,folded,axis,bit,ZERO if a is None else a)
                else:
                    vals=[]
                    for node in (0,1,2):
                        r=base(node);ans=ZERO
                        for k,(op,i,j) in enumerate(gates):
                            index=(i if axis==0 else j)>>bit
                            fv=add(folded[index&~1],mul(r,sub(folded[index|1],folded[index&~1])))
                            ev=r if index&1 else sub(ONE,r)
                            x,y=(fv,v[j]) if axis==0 else (a,fv)
                            ans=add(ans,mul(mul(gw[k],ev),gate(op,x,y)))
                        vals.append(ans)
                    coeff=interpolation(vals)
                require(add(poly(coeff,ZERO),poly(coeff,ONE))==claim,'honest endpoint')
                commit(t,coeff);r=draw(t);claim=poly(coeff,r);rounds.append(coeff)
                for k,(_,i,j) in enumerate(gates):gw[k]=mul(gw[k],r if ((i if axis==0 else j)>>bit)&1 else sub(ONE,r))
                folded=(fold(folded,r) if kernel is None else kernel.affine_fold(folded,r));(ru if axis==0 else rv).append(r)
            if axis==0:a=folded[0]
        b=folded[0];require(wiring(gates,w,ru,rv,a,b)==claim,'honest wiring')
        commit(t,[a,b]);gamma=draw(t);claim=add(a,mul(gamma,b));queries=[(ru,ONE),(rv,gamma)]
        parts.append(dict(rounds=rounds,inputs=[a,b]))
    return dict(profile=PROFILE.decode(),layers=parts),obligation(layout,queries,claim)


def verify(layout,statement,proof,claim=ZERO):
    validate_layout(layout);claim=ext(claim)
    require(set(proof)=={'profile','layers'} and proof['profile']==PROFILE.decode(),'profile')
    require(len(proof['layers'])==len(layout['layers']),'layer count');t=begin(layout,statement,claim)
    n=(len(layout['layers'][-1])-1).bit_length();queries=[([base((layout['root']>>i)&1) for i in range(n)],ONE)]
    for layer,part in zip(range(len(layout['layers'])-1,-1,-1),proof['layers']):
        gates=layout['layers'][layer];w=output_weights(len(gates),queries)
        prev=layout['input_size'] if layer==0 else len(layout['layers'][layer-1]);m=(prev-1).bit_length()
        require(set(part)=={'rounds','inputs'} and len(part['rounds'])==2*m and len(part['inputs'])==2,'layer shape');point=[]
        for row in part['rounds']:
            require(len(row)==3,'quadratic shape');c=[ext(x) for x in row]
            require(add(poly(c,ZERO),poly(c,ONE))==claim,'endpoint');commit(t,c);r=draw(t);point.append(r);claim=poly(c,r)
        a,b=map(ext,part['inputs']);ru,rv=point[:m],point[m:]
        require(wiring(gates,w,ru,rv,a,b)==claim,'wiring evaluation')
        commit(t,[a,b]);gamma=draw(t);claim=add(a,mul(gamma,b));queries=[(ru,ONE),(rv,gamma)]
    return obligation(layout,queries,claim)
