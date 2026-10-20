"""Bounded-memory acceleration of the unchanged Q8 diagnostic batched prover.

No verification shortcuts. SourceCache is untrusted; verifier needs no cache.
Native FFT/fold/quadratic kernels are prover-only. SHA384 uses Python reference.
"""
from array import array
import struct
from pq384_native_fft import NativeFFT
from pq384_primitives import P,require,hash_parts,u64
from pq384_batched_fold import public,round_start,oracle_context,indices,absorb_queries
from pq384_one_fold import weights


def flat(values):return array('I',(v for x in values for v in x))
def tuples(words):return [tuple(words[i:i+4]) for i in range(0,len(words),4)]

class FlatTree:
    def __init__(self, words, context):
        require(len(words)%8==0,'tree shape')
        self.words=words;self.half=len(words)//8;self.context=context
        # Store digests as contiguous bytearrays, avoiding Python objects per node.
        layer=bytearray()
        for i in range(self.half):
            layer.extend(hash_parts(b'merkle/leaf',context,u64(i),self.leaf(i)))
        self.layers=[layer]
        while len(layer)>48:
            level=len(self.layers);nxt=bytearray()
            for start in range(0,len(layer),96):
                nxt.extend(hash_parts(b'merkle/node',context,u64(level),
                                      bytes(layer[start:start+48]),bytes(layer[start+48:start+96])))
            self.layers.append(nxt);layer=nxt
        self.root=hash_parts(b'merkle/root',context,u64(self.half),bytes(layer))

    def leaf(self,i):
        a=self.words[4*i:4*i+4];j=i+self.half
        return struct.pack('<8I',*a,*self.words[4*j:4*j+4])

    def opening(self,i):
        leaf=list(struct.unpack('<8I',self.leaf(i)));path=[]
        for layer in self.layers[:-1]:
            start=(i^1)*48;path.append(layer[start:start+48].hex());i//=2
        return {'leaf':leaf,'path':path}


def prove_cached(cache,native,**args):
    h,t,degree=public(args)
    require(cache.degree==degree and cache.root==args['expected_root'] and
            cache.context.hex()==h['context_hex'] and cache.lanes==len(h['batch_powers']),
            'source cache identity')
    cs=array('I',[0])*(4*degree)
    for lane,power in enumerate(h['batch_powers']):
        coefficients=cache.coefficients(lane)
        for i,c in enumerate(coefficients):
            for k in range(4):cs[4*i+k]=(cs[4*i+k]+power[k]*c)%P
    ws=flat(weights(h['packed_point']));claim=h['batched_claim'];rounds=[];source=cache
    while degree>64:
        wire=[list(v) for v in native.quadratic_words(cs,ws)]
        r,stage,claim=round_start(t,wire,claim)
        cs=native.fold_words(cs,r);ws=native.fold_words(ws,r)
        context,_=oracle_context(stage,degree//2)
        nxt=FlatTree(native.lde4_words(cs),context)
        sample=indices(t,nxt.root,2*degree)
        queries=[{'source':source.opening(i),'next':nxt.opening(i%degree)} for i in sample]
        rounds.append({'quadratic':wire,'next_root':nxt.root.hex(),'queries':queries})
        absorb_queries(t,queries);source=nxt;degree//=2
    return {'profile':'near-pq384-batched-fold-v1','rounds':rounds,
            'terminal':{'profile':'near-pq384-terminal-v1','coefficients':[[list(v) for v in tuples(cs)]]}}
