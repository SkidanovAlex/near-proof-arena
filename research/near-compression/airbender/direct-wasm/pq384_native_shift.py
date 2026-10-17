"""Prover acceleration only: native matrix work, unchanged shift transcript."""
import ctypes as C
from native_folded import U32, PTR
from verify_whir_toy import ZERO, ONE, base, add, mul, poly, require
from pq384_shift import encode
import folded_prover as folded
import pq384_shift as shift


def setup(lib):
    lib.np_terminal.argtypes=[C.c_void_p,PTR];lib.np_terminal.restype=C.c_int
    lib.np_batch.argtypes=[PTR,C.c_size_t,C.c_size_t,PTR,PTR];lib.np_batch.restype=C.c_int
    lib.np_evaluate.argtypes=[PTR,C.c_size_t,C.c_size_t,PTR,C.c_size_t,PTR];lib.np_evaluate.restype=C.c_int
    return lib


def terminal(state):
    setup(state.lib);out=(U32*(8*state.width))()
    require(state.lib.np_terminal(state.handle,out)==0,'native terminal vectors')
    vectors=[tuple(out[4*i:4*i+4]) for i in range(2*state.width)]
    return vectors[:state.width],vectors[state.width:]


def prove(rows,point,transcript,current,nxt,lib):
    n=len(point);width=len(rows[0]);count=len(rows)
    require(count==2**n and len(current)==len(nxt)==width,'native shift dimensions')
    proof={'current_evals':[encode(v) for v in current],
           'next_evals':[encode(v) for v in nxt],'rounds':[]}
    alpha,claim=shift.start_claim(proof,point,width,transcript)
    setup(lib);data=(U32*(count*width))(*(v for row in rows for v in row));out=(U32*(4*count))()
    require(lib.np_batch(data,count,width,(U32*4)(*alpha),out)==0,'native batch')
    batched=[tuple(out[4*i:4*i+4]) for i in range(count)]
    # Hoist this point-independent power out of the O(N) scalar loop.
    alpha_width=shift.power(alpha,width)
    def kernel(x):return add(shift.eq_point(point,x),mul(alpha_width,shift.shift_kernel(point,x)))
    at=[]
    for i in range(n):
        values=[]
        for node in range(3):
            r=base(node);total=ZERO
            for index in range(len(batched)//2):
                x=at+[r]+folded.boolean_point(index,n-i-1)
                value=folded.affine(batched[2*index],batched[2*index+1],r)
                total=add(total,mul(kernel(x),value))
            values.append(total)
        cs=shift.interpolate(values)
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'native shift identity')
        encoded=[encode(v) for v in cs];proof['rounds'].append(encoded);transcript.commit_ext(encoded)
        r=transcript.draw(1,True)[0];at.append(r);claim=poly(cs,r)
        batched=[folded.affine(a,b,r) for a,b in zip(batched[::2],batched[1::2])]
    final_out=(U32*(4*width))();p=(U32*(4*n))(*(v for r in at for v in r))
    require(lib.np_evaluate(data,count,width,p,n,final_out)==0,'native final MLE')
    final=[tuple(final_out[4*i:4*i+4]) for i in range(width)]
    require(claim==mul(kernel(at),shift.batch(final,alpha)),'native shift terminal')
    return proof,at,final
