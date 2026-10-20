"""SHA384 multi-table AIR, group-1 bus products, global-chain PCS diagnostic.

All source roots precede bus challenges. All fresh auxiliary roots/finals
precede table mixing. Bus acceptance is randomized fingerprint product equality;
it implies natural multiplicity balance only outside explicit bad events whose
security bounds are NOT certified here. V2 hashes canonical AIR/public/shapes
once into a SHA384 statement digest; binding additionally assumes no digest collision. Q8/Ext4, no ZK/proximity/RBR/QROM claim.
"""
import json,sys,time
import scheduled_bus_whir as algebra
import pq384_global_chain as pcs
from pq384_table_air import AirTranscript
from pq384_primitives import require,hash_parts,u64
from packed_claim_handoff import packing_context,vector_bytes,canonical_ext as ext
from verify_whir_toy import P,ZERO,ONE,base,add,sub,mul,poly
import pq384_shift as shift
import pq384_native_shift as native_shift
from native_folded_v2 import compile_weighted,NativeTable,library
from pq384_native_fft import NativeFFT
from reference import schema,public_messages

PROFILE='near-pq384-global-bus-v2'
aux=algebra.aux;BASIS=algebra.BASIS;constraints=algebra.constraints
weighted=algebra.weighted

def validate(spec):
    require(type(spec)is dict and set(spec)=={'air','public','log_rows','source_packings','aux_packings','terminal_degree'},'bus spec fields')
    air=spec['air'];schema(air);count=len(air['tables']);require(count>0,'nonempty AIR')
    require(type(spec['terminal_degree'])is int and spec['terminal_degree'] in (1,64),'terminal profile')
    for key in ('log_rows','source_packings','aux_packings'):
        require(isinstance(spec[key],list) and len(spec[key])==count,'per-table shape')
    require(isinstance(spec['public'],list) and all(type(v)is int and 0<=v<P for v in spec['public']),'public field')
    degrees=[]
    for ti,table in enumerate(air['tables']):
        n=spec['log_rows'][ti];require(type(n)is int and 1<=n<=13 and n<=table['maxLog'] and table['width']>0,'table shape')
        widths=(table['width'],4*aux.layout(table)['aux_columns'])
        for branch,(w,key) in enumerate(zip(widths,('source_packings','aux_packings'))):
            packing=spec[key][ti]
            if w==0:require(type(packing)is int and packing==0,'empty auxiliary packing');continue
            packing_context(n,w,packing);D=(1<<n)*packing
            require(128<=D<=262144 and (w+packing-1)//packing<=64,'PCS shape')
        degrees.append(algebra.table_degree(table,air['numPub']))
    public_messages(air,spec['public']);return degrees

def statement(spec):
    canonical=json.dumps({'profile':PROFILE,'spec':spec},sort_keys=True,separators=(',',':')).encode()
    return hash_parts(b'global-bus-canonical-statement-digest-v2',canonical)

def check_roots(roots,count):
    require(isinstance(roots,list) and len(roots)==count and all(type(v)is bytes and len(v)==48 for v in roots),'root vector')

def begin(spec,roots):
    validate(spec);check_roots(roots,len(spec['air']['tables']));st=statement(spec);t=AirTranscript(st);t.statement_digest=st
    t.t.commit(b'all-source-commitments',u64(len(roots))+b''.join(roots))
    alpha=t.draw(1,True)[0];gamma=t.draw(1,True)[0];return st,t,alpha,gamma

def empty_aux_root(spec,ti,st=None):return hash_parts(b'global-bus-empty-auxiliary',statement(spec) if st is None else st,u64(ti))

def initialize_aux(t,spec,roots,finals):
    tables=spec['air']['tables'];check_roots(roots,len(tables))
    require(isinstance(finals,list) and len(finals)==len(tables),'final table count')
    t.t.commit(b'all-auxiliary-commitments',u64(len(roots))+b''.join(roots))
    for ti,(table,root,fs) in enumerate(zip(tables,roots,finals)):
        layout=aux.layout(table)
        require(isinstance(fs,list) and len(fs)==layout['finals'],'interaction final count')
        values=[ext(v) for v in fs]
        if layout['aux_columns']==0:require(root==empty_aux_root(spec,ti,t.statement_digest) and fs==[],'canonical empty auxiliary')
        t.t.commit(b'auxiliary-final-vector',u64(ti)+u64(len(fs))+vector_bytes(values))

def table_start(t,ti,n):
    t.t.commit(b'table-constraint-start',u64(ti)+u64(n));return t.draw(1,True)[0],t.draw(n,True)

def handoff(spec,st,t,ti,branch,root,point,claims):
    table=spec['air']['tables'][ti];width=table['width'] if branch==0 else 4*aux.layout(table)['aux_columns']
    packing=spec['source_packings' if branch==0 else 'aux_packings'][ti]
    parent=hash_parts(b'global-bus-packed-opening-branch',t.seed,u64(ti),u64(branch))
    return dict(statement=st,parent_binding=parent,expected_root=root,log_rows=spec['log_rows'][ti],
                width=width,packing=packing,row_point=point,column_claims=claims)

def prove_table(spec,st,t,alpha,gamma,ti,rows,coordinates,finals,roots,caches,*,folded_library,fft_library):
    table=spec['air']['tables'][ti];n=spec['log_rows'][ti];degree=algebra.table_degree(table,spec['air']['numPub'])
    width=table['width'];cw=4*aux.layout(table)['aux_columns']
    require(len(rows)==len(coordinates)==1<<n and all(len(r)==width and len(c)==cw for r,c in zip(rows,coordinates)),'combined trace shape')
    combined=[r+c for r,c in zip(rows,coordinates)];mixing,tau=table_start(t,ti,n)
    lib=library(folded_library);program=compile_weighted(table,spec['public'],alpha,gamma,[ext(v) for v in finals],mixing,sys.modules[__name__])
    point=[];rounds=[];start=time.perf_counter()
    with NativeTable(combined,program,tau,lib) as state:
        for _ in range(n):
            cs=[list(v) for v in shift.interpolate(state.values(degree+2))]
            rounds.append(cs);t.commit_ext(cs);r=t.draw(1,True)[0];point.append(r);state.fold(r)
        current,nxt=native_shift.terminal(state)
    zerocheck=time.perf_counter()-start;start=time.perf_counter()
    reduction,at,claims=native_shift.prove(combined,point,t,current,nxt,lib)
    shift_seconds=time.perf_counter()-start;start=time.perf_counter();openings=[]
    slices=[claims[:width]]+([claims[width:]] if cw else [])
    for branch,values in enumerate(slices):
        args=handoff(spec,st,t,ti,branch,roots[branch],at,values)
        openings.append(pcs.prove_cached(caches[branch],NativeFFT(fft_library),terminal_degree=spec['terminal_degree'],**args))
    return dict(constraint_rounds=rounds,shift_reduction=reduction,column_claims=[list(v) for v in claims],openings=openings),dict(zerocheck=zerocheck,shift=shift_seconds,openings=time.perf_counter()-start)

def verify_table_reduction(part,spec,st,t,alpha,gamma,ti,finals,roots):
    table=spec['air']['tables'][ti];n=spec['log_rows'][ti];degree=algebra.table_degree(table,spec['air']['numPub'])
    require(type(part)is dict and set(part)=={'constraint_rounds','shift_reduction','column_claims','openings'},'table proof fields')
    mixing,tau=table_start(t,ti,n);claim=ZERO;point=[]
    require(isinstance(part['constraint_rounds'],list) and len(part['constraint_rounds'])==n,'constraint round count')
    for cs in part['constraint_rounds']:
        require(isinstance(cs,list) and len(cs)==degree+2,'constraint round degree');values=[ext(v) for v in cs]
        require(add(poly(values,ZERO),poly(values,ONE))==claim,'table zerocheck')
        t.commit_ext(cs);r=t.draw(1,True)[0];point.append(r);claim=poly(values,r)
    sw=table['width'];cw=4*aux.layout(table)['aux_columns'];width=sw+cw;red=part['shift_reduction']
    require(type(red)is dict and set(red)=={'current_evals','next_evals','rounds'},'shift fields')
    require(len(red['current_evals'])==len(red['next_evals'])==width,'terminal width')
    current=[ext(v) for v in red['current_evals']];nxt=[ext(v) for v in red['next_evals']]
    require(claim==weighted(spec,ti,alpha,gamma,[ext(v) for v in finals],mixing,tau,point,current,nxt),'table terminal constraints')
    claims=part['column_claims'];require(isinstance(claims,list) and len(claims)==width,'claim width')
    for v in claims:ext(v)
    at=shift.verify(red,point,width,t,claims)
    slices=[claims[:sw]]+([claims[sw:]] if cw else [])
    require(isinstance(part['openings'],list) and len(part['openings'])==len(slices),'opening branch count')
    return [handoff(spec,st,t,ti,branch,roots[branch],at,values) for branch,values in enumerate(slices)]

def verify_local(proof,spec,roots):
    require(type(proof)is dict and set(proof)=={'profile','aux_roots','finals','tables'} and proof['profile']==PROFILE,'bus proof fields')
    st,t,alpha,gamma=begin(spec,roots)
    require(isinstance(proof['aux_roots'],list),'aux root list');ars=[pcs.decode_hash(v) for v in proof['aux_roots']]
    initialize_aux(t,spec,ars,proof['finals'])
    require(isinstance(proof['tables'],list) and len(proof['tables'])==len(roots),'table count')
    for ti,part in enumerate(proof['tables']):
        argslist=verify_table_reduction(part,spec,st,t,alpha,gamma,ti,proof['finals'][ti],[roots[ti],ars[ti]])
        for opening,args in zip(part['openings'],argslist):pcs.verify(opening,terminal_degree=spec['terminal_degree'],**args)
    return alpha,gamma

def global_fingerprint_balance(spec,finals,alpha,gamma):
    sends=ONE;receives=ONE
    for table,fs in zip(spec['air']['tables'],finals):
        for index,value in zip(aux.layout(table)['order'],fs):
            if table['interactions'][index]['send']:sends=mul(sends,ext(value))
            else:receives=mul(receives,ext(value))
    for bus,send,message in public_messages(spec['air'],spec['public']):
        fp=ZERO;power=ONE
        for value in message:fp=add(fp,mul(base(value),power));power=mul(power,alpha)
        factor=sub(gamma,add(fp,mul(base(bus+1),power)))
        if send:sends=mul(sends,factor)
        else:receives=mul(receives,factor)
    return sends==receives

def verify(proof,spec,roots):
    alpha,gamma=verify_local(proof,spec,roots)
    require(global_fingerprint_balance(spec,proof['finals'],alpha,gamma),'global fingerprint product equality')
    return True

if __name__=='__main__':
    import sys
    from pathlib import Path
    proof=json.loads(Path(sys.argv[1]).read_text());trusted=json.loads(Path(sys.argv[2]).read_text())
    assert verify(proof,trusted['spec'],[bytes.fromhex(v) for v in trusted['roots']])
    print('PASS: all-table local AIR and randomized bus-fingerprint diagnostic')
