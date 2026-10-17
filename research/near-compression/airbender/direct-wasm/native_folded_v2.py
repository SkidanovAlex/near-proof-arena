"""Prover-only native round kernel. Transcript/interpolation remain in Python.

No native verifier, PCS, or cryptographic-security claim. The instruction DAG
covers actual exported Expr semantics and all group-1 auxiliary residuals.
"""
import ctypes as C
import os
from pathlib import Path
from verify_whir_toy import P, ZERO, ONE, add, mul, base

U32=C.c_uint32
PTR=C.POINTER(U32)

class Program:
    def __init__(self): self.instructions=[]; self.cache={}
    def emit(self,op,a=0,b=0,constant=ZERO):
        key=(op,a,b,*constant)
        if key not in self.cache:
            self.cache[key]=len(self.instructions); self.instructions.append(key)
        return self.cache[key]
    def constant(self,x): return self.emit(0,constant=x)
    def plus(self,a,b): return self.emit(6,a,b)
    def minus(self,a,b): return self.emit(7,a,b)
    def times(self,a,b): return self.emit(8,a,b)
    def finish(self,output):
        # The ABI returns the final register, including when CSE reuses output.
        zero=self.constant(ZERO)
        self.instructions.append((6,output,zero,0,0,0,0))
        return (U32*(7*len(self.instructions)))(*(x for ins in self.instructions for x in ins))


def compile_weighted(table,public,alpha,gamma,finals,mixing,protocol):
    p=Program(); zero=p.constant(ZERO); one=p.constant(ONE)
    selectors={k:p.emit(i) for k,i in [('first',3),('last',4),('trans',5)]}
    def expr(e):
        op=e[0]
        if op=='c': return p.constant(base(e[1]))
        if op=='p': return p.constant(base(public[e[1]] if e[1]<len(public) else 0))
        if op=='v':
            assert 0<=e[1]<table['width'] and e[2] in (0,1)
            return p.emit(2 if e[2] else 1,e[1])
        if op in selectors: return selectors[op]
        if op=='-': return p.minus(zero,expr(e[1]))
        if op=='+': return p.plus(expr(e[1]),expr(e[2]))
        if op=='*': return p.times(expr(e[1]),expr(e[2]))
        raise ValueError('unknown canonical Expr opcode')
    layout=protocol.aux.layout(table)
    def reconstruct(next):
        result=[]
        for i in range(layout['aux_columns']):
            value=zero
            for j,basis in enumerate(protocol.BASIS):
                value=p.plus(value,p.times(p.emit(2 if next else 1,table['width']+4*i+j),p.constant(basis)))
            result.append(value)
        return result
    current,nxt=reconstruct(False),reconstruct(True)
    assert len(finals)==layout['finals']
    residuals=[expr(e) for e in protocol.constraints(table)]
    factors=[];offset=0
    for interaction in table['interactions']:
        fp=zero;weight=ONE
        for e in interaction['msg']:
            fp=p.plus(fp,p.times(expr(e),p.constant(weight)));weight=mul(weight,alpha)
        fp=p.plus(fp,p.constant(mul(base(interaction['bus']+1),weight)))
        p0=p.minus(p.constant(gamma),fp); bits=[expr(e) for e in interaction['mult']]
        if not bits:factors.append(one);continue
        first=p.plus(one,p.times(bits[0],p.minus(p0,one)))
        if len(bits)==1:factors.append(first);continue
        k=len(bits)-1;ps=current[offset:offset+k];pis=current[offset+k:offset+2*k]
        residuals += [p.minus(pj,p.times(prev,prev)) for pj,prev in zip(ps,[p0]+ps)]
        residuals += [p.minus(pi,p.times(prev,p.plus(one,p.times(bit,p.minus(pj,one)))))
                      for pi,prev,bit,pj in zip(pis,[first]+pis,bits[1:],ps)]
        factors.append(pis[-1]);offset+=2*k
    for j,index in enumerate(layout['order']):
        a,an=current[offset+j],nxt[offset+j];factor=p.times(a,factors[index])
        residuals += [p.times(selectors['first'],p.minus(a,one)),
                      p.times(selectors['trans'],p.minus(an,factor)),
                      p.times(selectors['last'],p.minus(factor,p.constant(finals[j])))]
    total=zero;weight=ONE
    for residual in residuals:
        total=p.plus(total,p.times(p.constant(weight),residual));weight=mul(weight,mixing)
    return p.finish(total)


def library(path=None):
    lib=C.CDLL(str(path or os.environ.get('NEAR_NATIVE_FOLDED_V2_LIB') or Path(__file__).with_name('native-folded')/'libnear_folded_v2.so'))
    lib.np_new.argtypes=[PTR,C.c_size_t,C.c_size_t];lib.np_new.restype=C.c_void_p
    lib.np_free.argtypes=[C.c_void_p];lib.np_free.restype=None
    lib.np_fold.argtypes=[C.c_void_p,PTR];lib.np_fold.restype=C.c_int
    lib.np_round.argtypes=[C.c_void_p,PTR,C.c_size_t,PTR,C.c_size_t,PTR,C.c_size_t,C.c_size_t,PTR]
    lib.np_round.restype=C.c_int
    return lib

class NativeTable:
    def __init__(self,rows,program,tau,lib=None):
        self.lib=lib or library();self.handle=None
        self.width=len(rows[0]);self.n=len(tau);self.prefix=[];self.program=program
        assert len(rows)==2**self.n and self.n>0 and self.width>0
        assert all(len(row)==self.width and all(type(v)is int and 0<=v<P for v in row) for row in rows)
        assert all(len(v)==4 and all(type(c)is int and 0<=c<P for c in v) for v in tau)
        data=(U32*(len(rows)*self.width))(*(v for row in rows for v in row))
        self.handle=self.lib.np_new(data,len(rows),self.width)
        if not self.handle:raise ValueError('native witness rejected')
        self.tau=(U32*(4*self.n))(*(v for x in tau for v in x))
    def close(self):
        if self.handle:self.lib.np_free(self.handle);self.handle=None
    def __enter__(self):return self
    def __exit__(self,*args):self.close()
    def values(self,nodes):
        assert self.handle and len(self.prefix)<self.n and 0<nodes<=1000
        prefix=(U32*(4*len(self.prefix)))(*(v for x in self.prefix for v in x));out=(U32*(4*nodes))()
        status=self.lib.np_round(self.handle,self.program,len(self.program)//7,self.tau,self.n,prefix,len(self.prefix),nodes,out)
        if status:raise ValueError(f'native round rejected: {status}')
        return [tuple(out[4*i:4*i+4]) for i in range(nodes)]
    def fold(self,r):
        assert len(r)==4 and all(type(c)is int and 0<=c<P for c in r)
        status=self.lib.np_fold(self.handle,(U32*4)(*r))
        if status:raise ValueError(f'native fold rejected: {status}')
        self.prefix.append(r)


def prove(spec,roots,rows_by_table,aux_roots,aux_rows_by_table,finals_by_table,*,protocol_impl=None,checkpoint=None):
    """Drop-in prover: native zerocheck, existing Python transcript and shift."""
    import copy
    import struct
    import heterogeneous_bus_whir
    import folded_prover
    import shift_opening as shift
    from constraint_sumcheck import encode
    protocol=protocol_impl or heterogeneous_bus_whir
    words,transcript,alpha,gamma=protocol.begin(spec,roots)
    tables=spec['air']['tables'];degrees=protocol.validate(spec)
    assert len(rows_by_table)==len(aux_rows_by_table)==len(finals_by_table)==len(tables)
    finals=[[encode(v) for v in fs] for fs in finals_by_table]
    protocol.initialize_aux(transcript,tables,aux_roots,finals)
    proof={'aux_roots':copy.deepcopy(aux_roots),'finals':finals,'tables':[]};handoffs=[]
    lib=library()
    for ti,(table,degree,source,auxiliary,fs) in enumerate(zip(tables,degrees,rows_by_table,aux_rows_by_table,finals_by_table)):
        n=spec['log_rows'][ti]
        assert len(source)==2**n and all(len(row)==table['width'] for row in source)
        coordinates=protocol.flatten_aux_rows(table,auxiliary,n)
        rows=[a+b for a,b in zip(source,coordinates)]
        mixing,tau=protocol.table_start(transcript,ti,n);point=[];rounds=[]
        program=compile_weighted(table,spec['public'],alpha,gamma,fs,mixing,protocol)
        with NativeTable(rows,program,tau,lib) as state:
            for _ in range(n):
                encoded=[encode(v) for v in shift.interpolate(state.values(degree+2))]
                rounds.append(encoded);transcript.commit_ext(encoded)
                r=transcript.draw(1,True)[0];point.append(r);state.fold(r)
            import native_shift
            current,nxt=native_shift.terminal(state)
        reduction,at,_=native_shift.prove(rows,point,transcript,current,nxt,lib)
        proof['tables'].append({'constraint_rounds':rounds,'shift_reduction':reduction})
        branches=[]
        for branch,root in enumerate((roots[ti],aux_roots[ti])):
            fork=protocol.opening_transcript(transcript,ti,branch)
            branches.append({'root':root,'statement_words':words,'log_rows':n,
                             'pre_opening_seed':list(struct.unpack('<8I',fork.seed)),
                             'evaluation_point':[encode(r) for r in at]})
        handoffs.append(branches)
        if checkpoint is not None: checkpoint(ti,proof,handoffs)
    return proof,handoffs
