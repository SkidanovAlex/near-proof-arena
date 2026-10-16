"""New all-zerocheck -> random terminal batch -> GKR -> weighted PCS profile.

Canonical AIR/config digest and fixed-width public/shape encoding bind the
statement. All roots and fresh auxiliaries precede constraints. No disclosed
current/next/final-column vectors and no abandoned opening obligation.
Diagnostic only: weighted joint proximity/RBR/QROM and GKR composition pending.
"""
import json,sys
import pq384_global_bus as old
import pq384_terminal_gkr as gkr
import pq384_weighted_joint as pcs
from pq384_terminal_compile import compile_terminal
from pq384_terminal_input_weights import branch_lanes
from pq384_table_air import AirTranscript
from pq384_primitives import require,hash_parts,u64,field_words
from packed_claim_handoff import canonical_ext as ext
from native_folded_v2 import compile_weighted,NativeTable,library
from verify_whir_toy import ZERO,ONE,add,poly
from pq384_native_fft import NativeFFT
from pq384_source_cache import SourceCache
import pq384_native_shift as ns
import pq384_shift as shift
PROFILE='near-pq384-gkr-bus-v1'
FIXED_PROFILE='near-pq384-gkr-fixed-input-bus-v1'

def profile(input_log=None):
    if input_log is None:return PROFILE
    require(type(input_log)is int and 1<=input_log<=25,'trusted input log')
    return FIXED_PROFILE
aux=old.aux;validate=old.validate;initialize_aux=old.initialize_aux;empty_aux_root=old.empty_aux_root


def statement(spec, *, input_log=None):
    old.validate(spec);require(spec['terminal_degree']==1,'constant terminal only')
    static=hash_parts(b'gkr-static-air-config-v1',json.dumps(spec['air'],sort_keys=True,separators=(',',':')).encode())
    shape=b''.join(u64(v) for key in ('log_rows','source_packings','aux_packings') for v in spec[key])
    parts=(static,u64(len(spec['public'])),field_words(spec['public']),u64(len(spec['log_rows'])),shape,u64(1))
    selected=profile(input_log)
    return hash_parts(selected.encode(),*parts,*(() if input_log is None else (u64(input_log),)))


def begin(spec,roots, *, input_log=None):
    old.check_roots(roots,len(spec['air']['tables']));st=statement(spec,input_log=input_log);t=AirTranscript(st);t.statement_digest=st
    t.t.commit(b'all-source-commitments',u64(len(roots))+b''.join(roots))
    return st,t,t.draw(1,True)[0],t.draw(1,True)[0]


def constraint_prove(spec,t,alpha,gamma,ti,rows,coords,finals,lib):
    table=spec['air']['tables'][ti];n=spec['log_rows'][ti];degree=old.algebra.table_degree(table,spec['air']['numPub'])
    sw=table['width'];aw=4*aux.layout(table)['aux_columns']
    require(len(rows)==len(coords)==1<<n and all(len(r)==sw and len(c)==aw for r,c in zip(rows,coords)),'trace shape')
    mixing,tau=old.table_start(t,ti,n);program=compile_weighted(table,spec['public'],alpha,gamma,[ext(x) for x in finals],mixing,old)
    rounds=[];point=[];claim=ZERO
    with NativeTable([r+c for r,c in zip(rows,coords)],program,tau,lib) as state:
        for _ in range(n):
            cs=shift.interpolate(state.values(degree+2));require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'invalid trace constraints')
            rounds.append(cs);t.commit_ext(cs);r=t.draw(1,True)[0];point.append(r);claim=poly(cs,r);state.fold(r)
        current,nxt=ns.terminal(state)
    return rounds,dict(point=point,mixing=mixing,tau=tau,claim=claim),(current,nxt)


def constraint_verify(spec,t,ti,rounds):
    table=spec['air']['tables'][ti];n=spec['log_rows'][ti];degree=old.algebra.table_degree(table,spec['air']['numPub']);mixing,tau=old.table_start(t,ti,n)
    require(isinstance(rounds,list) and len(rounds)==n,'constraint rounds');point=[];claim=ZERO
    for cs in rounds:
        require(len(cs)==degree+2,'constraint degree');cs=[ext(x) for x in cs]
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'constraint endpoint');t.commit_ext(cs);r=t.draw(1,True)[0];point.append(r);claim=poly(cs,r)
    return dict(point=point,mixing=mixing,tau=tau,claim=claim)


def terminal_layout(spec,t,alpha,gamma,finals,terminals, *, input_log=None):
    t.t.commit(b'all-constraint-proofs-complete',u64(len(terminals)));rho=t.draw(1,True)[0]
    circuit=compile_terminal(spec,alpha,gamma,finals,terminals,rho)
    binding=hash_parts(b'gkr-after-all-constraints',t.seed)
    if input_log is None:layout=gkr.layer_circuit(circuit)
    else:
        profile(input_log)
        from pq384_fixed_gkr_layout import fixed_layer_circuit
        layout=fixed_layer_circuit(circuit,input_log=input_log)
    return circuit,layout,binding


def opening_arguments(spec,roots,ars,terminals,circuit,obligation):
    blocks={x['table']:x for x in circuit['input_blocks']};branches=[]
    for ti,table in enumerate(spec['air']['tables']):
        sw=table['width'];aw=4*aux.layout(table)['aux_columns']
        for branch,width,offset,key,root in ((0,sw,0,'source_packings',roots[ti]),(1,aw,sw,'aux_packings',ars[ti])):
            if not width:continue
            packing=spec[key][ti]
            branches.append(dict(root=root.hex(),log_rows=spec['log_rows'][ti],width=width,packing=packing,row_point=terminals[ti]['point'],
                lanes=branch_lanes(blocks[ti],offset,width,packing,obligation['private_weights'])))
    return branches


def opening_parent(binding,gproof):
    return hash_parts(b'weighted-pcs-after-gkr',binding,json.dumps(gproof,sort_keys=True,separators=(',',':')).encode())


def finish_prove(spec,roots,ars,finals,st,t,alpha,gamma,rounds,terminals,private_rows,caches,native, *, input_log=None, gkr_kernel=None):
    circuit,layout,binding=terminal_layout(spec,t,alpha,gamma,finals,terminals,input_log=input_log)
    private=[ZERO]*circuit['private_input_capacity']
    for block in circuit['input_blocks']:
        current,nxt=private_rows[block['table']];offset=block['offset'];W=block['column_capacity']
        private[offset:offset+len(current)]=current;private[offset+W:offset+W+len(nxt)]=nxt
    gp,ob=gkr.prove(layout,binding,private,kernel=gkr_kernel)
    branches=opening_arguments(spec,roots,ars,terminals,circuit,ob)
    opening=pcs.prove(caches,native,st,opening_parent(binding,gp),branches,ob['private_claim'])
    return dict(profile=profile(input_log),aux_roots=[r.hex() for r in ars],finals=finals,tables=rounds,gkr=gp,opening=opening)


def verify_local(proof,spec,roots, *, input_log=None):
    require(set(proof)=={'profile','aux_roots','finals','tables','gkr','opening'} and proof['profile']==profile(input_log),'proof fields')
    st,t,alpha,gamma=begin(spec,roots,input_log=input_log);ars=[pcs.decode_hash(x) for x in proof['aux_roots']];initialize_aux(t,spec,ars,proof['finals'])
    require(len(proof['tables'])==len(roots),'table count')
    terminals=[constraint_verify(spec,t,ti,rounds) for ti,rounds in enumerate(proof['tables'])]
    circuit,layout,binding=terminal_layout(spec,t,alpha,gamma,proof['finals'],terminals,input_log=input_log)
    ob=gkr.verify(layout,binding,proof['gkr']);branches=opening_arguments(spec,roots,ars,terminals,circuit,ob)
    pcs.verify(proof['opening'],st,opening_parent(binding,proof['gkr']),branches,ob['private_claim'])
    return alpha,gamma


def verify(proof,spec,roots, *, input_log=None):
    alpha,gamma=verify_local(proof,spec,roots,input_log=input_log)
    require(old.global_fingerprint_balance(spec,proof['finals'],alpha,gamma),'randomized bus fingerprint product')
    return True

if __name__=='__main__':
    from pathlib import Path
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('proof');ap.add_argument('statement');ap.add_argument('--input-log',type=int)
    args=ap.parse_args()
    p=json.loads(Path(args.proof).read_text());s=json.loads(Path(args.statement).read_text())
    assert verify(p,s['spec'],[bytes.fromhex(x) for x in s['roots']],input_log=args.input_log)
    print('PASS: GKR and mandatory weighted opening diagnostic; security not certified')
