"""Native prover-only acceleration; unchanged pq384_table_air verifier/wire."""
import time
import pq384_table_air as air
import pq384_native_shift as native_shift
from native_folded_v2 import Program,NativeTable,library
from pq384_cached_prover import prove_cached
from pq384_native_fft import NativeFFT
from pq384_primitives import require
from verify_whir_toy import ZERO,ONE,base,mul


def compile_table(table,public,mixing):
    p=Program();zero=p.constant(ZERO)
    selectors={k:p.emit(i) for k,i in [('first',3),('last',4),('trans',5)]}
    def expr(e):
        op=e[0]
        if op=='c':return p.constant(base(e[1]))
        if op=='p':return p.constant(base(public[e[1]] if e[1]<len(public) else 0))
        if op=='v':return p.emit(2 if e[2] else 1,e[1])
        if op in selectors:return selectors[op]
        if op=='-':return p.minus(zero,expr(e[1]))
        if op=='+':return p.plus(expr(e[1]),expr(e[2]))
        if op=='*':return p.times(expr(e[1]),expr(e[2]))
        raise ValueError('canonical Expr opcode')
    total=zero;weight=ONE
    for e in air.constraints(table):
        total=p.plus(total,p.times(p.constant(weight),expr(e)));weight=mul(weight,mixing)
    return p.finish(total)


def prove_native(spec,root,rows,*,folded_library,fft_library=None,cache=None):
    table,degree=air.validate(spec);n=spec['log_rows']
    statement,t,mixing,tau=air.begin(spec,root);point=[];rounds=[]
    program=compile_table(table,spec['public'],mixing);lib=library(folded_library)
    timing={};start=time.perf_counter()
    with NativeTable(rows,program,tau,lib) as state:
        for _ in range(n):
            encoded=[list(v) for v in air.shift.interpolate(state.values(degree+2))]
            rounds.append(encoded);t.commit_ext(encoded)
            r=t.draw(1,True)[0];point.append(r);state.fold(r)
        current,nxt=native_shift.terminal(state)
    timing['zerocheck_seconds']=time.perf_counter()-start;start=time.perf_counter()
    reduction,at,claims=native_shift.prove(rows,point,t,current,nxt,lib)
    timing['shift_seconds']=time.perf_counter()-start;start=time.perf_counter()
    args=air.handoff(spec,root,statement,t,at,claims)
    if cache is not None:
        require(fft_library is not None,'FFT library required')
        opening=prove_cached(cache,NativeFFT(fft_library),**args)
    else:
        opening=air.pcs.prove(rows,**args)
    timing['opening_seconds']=time.perf_counter()-start
    proof=dict(profile=air.PROFILE,constraint_rounds=rounds,shift_reduction=reduction,
               column_claims=[list(v) for v in claims],opening=opening)
    return proof,timing
