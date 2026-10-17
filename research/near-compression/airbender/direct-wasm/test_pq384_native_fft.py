"""Independent parity and C ABI rejection tests; no protocol security claim."""
import argparse
import ctypes
import json
import random
import sys
import time
from array import array
from pq384_native_fft import NativeFFT, P


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--library',required=True)
    ap.add_argument('--reference-dir',required=True)
    ap.add_argument('--full',action='store_true')
    args=ap.parse_args()
    sys.path.insert(0,args.reference_dir)
    from pq384_multi_fold import fft, fold
    from check_whir_handoff import add,sub,mul
    native=NativeFFT(args.library)
    rng=random.Random(384)
    parity=0; naive=0; negatives=0
    for n in [1,2,4,8,16,32,64,128,256,512]:
        cs=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(n)]
        for lde in [False,True]:
            domain=n*(4 if lde else 1)
            omega=pow(440564289,(1<<27)//domain,P)
            got=native.fft(cs,lde4=lde)
            assert got==fft(cs+[(0,0,0,0)]*(domain-n),omega)
            parity+=1
            for index in sorted(set([0,1%domain,domain//2,domain-1])):
                x=pow(omega,index,P)
                expected=[0]*4
                for c in reversed(cs):
                    expected=[(expected[k]*x+c[k])%P for k in range(4)]
                assert got[index]==tuple(expected)
                naive+=1
    kernels=0
    for n in [2,4,16,128,512]:
        cs=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(n)]
        ws=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(n)]
        r=tuple(rng.randrange(P) for _ in range(4))
        flat=lambda xs:array('I',(v for x in xs for v in x))
        assert native.fold_words(flat(cs),r)==flat(fold(cs,r));kernels+=1
        got=native.quadratic_words(flat(cs),flat(ws))
        for t in [(0,0,0,0),(1,0,0,0),r]:
            cf=fold(cs,t);wf=fold(ws,t);expected=(0,0,0,0)
            for a,b in zip(cf,wf):expected=add(expected,mul(a,b))
            actual=add(got[0],mul(t,add(got[1],mul(t,got[2]))))
            assert actual==expected;kernels+=1
    for call in [lambda:native.fold_words(array('I',[P]*8),(0,0,0,0)),
                 lambda:native.quadratic_words(array('I',[0]*8),array('I',[P]*8)),
                 lambda:native.fold_words(array('I',[0]*8),(P,0,0,0))]:
        try:call()
        except ValueError:negatives+=1
        else:raise AssertionError('accepted noncanonical kernel input')
    U=ctypes.c_uint32
    src=(U*16)(*range(16));dst=(U*64)()
    f=native.lib.pq384_fft
    cases=[(None,16,dst,64,16,1),(src,0,dst,64,16,2),
           (src,15,dst,64,16,2),(src,16,dst,63,16,3),
           (src,16,src,64,16,5),(src,16,dst,64,15,2),
           (src,16,dst,64,1<<23,2),(src,16,dst,64,32,2),
           (src,16,None,64,16,1)]
    for a,b,c,d,e,want in cases:
        assert f(a,b,c,d,e)==want
        negatives+=1
    src[15]=P;assert f(src,16,dst,64,16)==4;negatives+=1
    assert list(dst)==[0]*64
    full=None
    if args.full:
        n=262144
        words=array('I',((i*7919+17)%P for i in range(n*4)))
        started=time.perf_counter();out=native.lde4_words(words);elapsed=time.perf_counter()-started
        omega=pow(440564289,(1<<27)//(4*n),P)
        for index in [0,1,17,2*n,4*n-1]:
            x=pow(omega,index,P);expected=[0]*4
            for i in range(n-1,-1,-1):
                expected=[(expected[k]*x+words[4*i+k])%P for k in range(4)]
            assert tuple(out[4*index:4*index+4])==tuple(expected)
            naive+=1
        full={'degree':n,'domain':4*n,'input_bytes':len(words)*4,
              'output_bytes':len(out)*4,'fft_seconds':elapsed,'direct_checks':5}
    print(json.dumps({'python_fft_parity_cases':parity,'naive_evaluations':naive,
                      'kernel_identity_checks':kernels,'rejected_inputs':negatives,'full':full},indent=2))

if __name__=='__main__':main()
