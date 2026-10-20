"""NEW configured outer GKR engine; copied algebra from seed-GKR engine.
Compiler CONFIG is specific to complete fold/source residual conjunction.
Caller derives all layout/weights from native fixed operands and one RS root.
Not the inner AIR seed profile; never relabel its proofs or old outer proofs.
"""
from pq384_terminal_gkr import *
PROFILE=b'near-recursive-single-root-gkr-v1'
CONFIG=b'recursive-single-rs-source-fold-fixedslots-v1/derived-native-operands/all-residuals-mle/rs-root-before-point/relay-v1/Ext4-v4=11/row-low4096/column-group-high/basis4'


def begin(statement,claim):
    return Transcript(hash_parts(PROFILE,CONFIG,statement,vector_bytes([ext(claim)])))


def prove(layout,statement,private,claim=ZERO):
    vs=values(layout,private);require(vs[-1][layout['root']]==claim,'false circuit output')
    t=begin(statement,claim);n=(len(vs[-1])-1).bit_length()
    queries=[([base((layout['root']>>i)&1) for i in range(n)],ONE)];parts=[]
    for layer in range(len(layout['layers'])-1,-1,-1):
        gates=layout['layers'][layer];w=output_weights(len(gates),queries);v=vs[layer];m=(len(v)-1).bit_length()
        folded=list(v);gw=list(w);rounds=[];ru=[];rv=[];a=None
        for axis in (0,1):
            if axis:folded=list(v)
            for bit in range(m):
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
                coeff=interpolation(vals);require(add(poly(coeff,ZERO),poly(coeff,ONE))==claim,'honest endpoint')
                commit(t,coeff);r=draw(t);claim=poly(coeff,r);rounds.append(coeff)
                for k,(_,i,j) in enumerate(gates):gw[k]=mul(gw[k],r if ((i if axis==0 else j)>>bit)&1 else sub(ONE,r))
                folded=fold(folded,r);(ru if axis==0 else rv).append(r)
            if axis==0:a=folded[0]
        b=folded[0];require(wiring(gates,w,ru,rv,a,b)==claim,'honest wiring')
        commit(t,[a,b]);gamma=draw(t);claim=add(a,mul(gamma,b));queries=[(ru,ONE),(rv,gamma)]
        parts.append(dict(rounds=rounds,inputs=[a,b]))
    ob=obligation(layout,queries,claim);ob['transcript_seed']=t.seed
    return dict(profile=PROFILE.decode(),layers=parts),ob


def verify(layout,statement,proof,claim=ZERO):
    require(set(proof)=={'profile','layers'} and proof['profile']==PROFILE.decode(),'profile')
    require(len(proof['layers'])==len(layout['layers']),'layer count');t=begin(statement,claim)
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
    ob=obligation(layout,queries,claim);ob['transcript_seed']=t.seed
    return ob
