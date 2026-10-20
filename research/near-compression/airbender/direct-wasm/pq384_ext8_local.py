"""Ext8 local sumcheck transcript reduction. Returns terminal obligations.
No polynomial commitment opening or state-transition security claim.
"""
import pq384_ext8_reference as f
from pq384_primitives import require,u64
from pq384_ext8_terminal_gkr import vector_bytes
from pq384_ext8_terminal_compile import compile_weighted
from pq384_ext8_local_native import NativeTable
import pq384_global_bus as protocol

def draw(t,n=1):return [tuple(v) for v in t.draw(b'ext8-local-challenge',n,8)[0]]
def start(t,ti,n):
    t.commit(b'ext8-local-table',u64(ti)+u64(n))
    return draw(t)[0],draw(t,n)
def interpolate(values):
    # Independent scalar Lagrange basis over the small public evaluation nodes.
    out=[f.ZERO]*len(values)
    for i,value in enumerate(values):
        basis=[1];den=1
        for j in range(len(values)):
            if i==j:continue
            nxt=[0]*(len(basis)+1)
            for k,c in enumerate(basis):nxt[k]=(nxt[k]-j*c)%f.P;nxt[k+1]=(nxt[k+1]+c)%f.P
            basis=nxt;den=den*(i-j)%f.P
        inverse=pow(den,-1,f.P)
        out=[f.add(x,f.scale(value,c*inverse%f.P)) for x,c in zip(out,basis)]
    return out

def prove(spec,t,alpha,gamma,ti,rows,coordinates,finals,lib):
    table=spec['air']['tables'][ti];n=spec['log_rows'][ti]
    width=table['width'];auxwidth=8*protocol.aux.layout(table)['aux_columns']
    require(len(rows)==len(coordinates)==1<<n and all(len(r)==width and len(c)==auxwidth for r,c in zip(rows,coordinates)),'trace shape')
    degree=protocol.algebra.table_degree(table,spec['air']['numPub'])
    mixing,tau=start(t,ti,n);program=compile_weighted(table,spec['public'],alpha,gamma,finals,mixing,protocol)
    claim=f.ZERO;rounds=[];point=[]
    with NativeTable([r+c for r,c in zip(rows,coordinates)],program,tau,lib) as state:
        for _ in range(n):
            coeff=interpolate(state.values(degree+2))
            require(f.add(coeff[0],f.evaluate(coeff,f.ONE))==claim,'invalid trace constraints')
            t.commit(b'ext8-local-round',vector_bytes(coeff));r=draw(t)[0]
            rounds.append(coeff);point.append(r);claim=f.evaluate(coeff,r);state.fold(r)
        terminal=state.terminal()
    return rounds,dict(point=point,mixing=mixing,tau=tau,claim=claim),terminal

def verify(spec,t,ti,rounds):
    table=spec['air']['tables'][ti];n=spec['log_rows'][ti]
    degree=protocol.algebra.table_degree(table,spec['air']['numPub'])
    require(len(rounds)==n,'local round count');mixing,tau=start(t,ti,n);claim=f.ZERO;point=[]
    for coeff in rounds:
        require(len(coeff)==degree+2,'local degree');coeff=[f.canonical(c) for c in coeff]
        require(f.add(coeff[0],f.evaluate(coeff,f.ONE))==claim,'local endpoint')
        t.commit(b'ext8-local-round',vector_bytes(coeff));r=draw(t)[0];point.append(r);claim=f.evaluate(coeff,r)
    return dict(point=point,mixing=mixing,tau=tau,claim=claim)
