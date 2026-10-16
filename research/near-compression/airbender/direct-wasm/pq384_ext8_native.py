"""Explicit native Ext8 fold/quadratic adapter; not a complete prover.

Build kernel_ext8.rs as a cdylib and supply its path. Python validates shape
and scalar canonicality before allocation; Rust independently checks scalars.
"""
import ctypes
from array import array
import pq384_ext8_reference as f

class Kernel:
    def __init__(self, library):
        self.lib=ctypes.CDLL(str(library))
        ptr=ctypes.POINTER(ctypes.c_uint32)
        self.lib.near_ext8_fft.argtypes=[ptr,ctypes.c_size_t,ptr,ctypes.c_size_t,ctypes.c_size_t]
        self.lib.near_ext8_fft.restype=ctypes.c_int
        self.lib.near_ext8_fold.argtypes=[ptr,ctypes.c_size_t,ptr,ptr]
        self.lib.near_ext8_quadratic.argtypes=[ptr,ptr,ctypes.c_size_t,ptr]
        self.lib.near_ext8_gkr_round.argtypes=[ptr,ctypes.c_size_t,ptr,ptr,ctypes.c_size_t,ptr,ctypes.c_size_t,ctypes.c_uint32,ctypes.c_uint32,ptr,ptr]
        self.lib.near_ext8_gkr_round.restype=ctypes.c_int
        self.lib.near_ext8_fold.restype=self.lib.near_ext8_quadratic.restype=ctypes.c_int
        self.tensor=getattr(self.lib,'near_ext8_tensor_weights',None)
        if self.tensor is not None:
            self.tensor.argtypes=[ptr,ptr,ctypes.c_size_t,ptr,ptr,ctypes.c_size_t,ptr,ctypes.c_size_t]
            self.tensor.restype=ctypes.c_int
    @staticmethod
    def pack(values):
        words=[x for value in values for x in f.canonical(value)]
        # Non-null buffer even for the empty-table identity.
        return (ctypes.c_uint32*max(1,len(words)))(*words)
    @staticmethod
    def unpack(buffer,n):return [tuple(buffer[8*i:8*i+8]) for i in range(n)]
    def affine_fold(self,values,r):
        if len(values)%2:raise ValueError('fold shape')
        a=self.pack(values);challenge=self.pack([r]);out=(ctypes.c_uint32*max(1,len(values)*4))()
        if self.lib.near_ext8_fold(a,len(values),challenge,out):raise ValueError('native fold rejected')
        return self.unpack(out,len(values)//2)
    def quadratic(self,values,weights):
        if len(values)!=len(weights) or len(values)%2:raise ValueError('quadratic shape')
        a=self.pack(values);b=self.pack(weights);out=(ctypes.c_uint32*24)()
        if self.lib.near_ext8_quadratic(a,b,len(values),out):raise ValueError('native quadratic rejected')
        return self.unpack(out,3)

    def lane_weights(self,point,current,next_columns):
        from pq384_ext8_input_weights import upper_zeta,row_weights,lane_weights
        if not current or len(current)!=len(next_columns) or len(current)&(len(current)-1):raise ValueError('column shape')
        point=[f.canonical(x) for x in point]
        current=[f.canonical(x) for x in current];next_columns=[f.canonical(x) for x in next_columns]
        a,b=upper_zeta(current),upper_zeta(next_columns);r,s=row_weights(point)
        return self.tensor_weights(a,b,r,s)

    def tensor_weights(self,a,b,r,s):
        if not a or len(a)!=len(b) or len(a)&(len(a)-1):raise ValueError('column tensor shape')
        if not r or len(r)!=len(s) or len(r)&(len(r)-1):raise ValueError('row tensor shape')
        n=len(a)*len(r)
        if n>1<<22:raise ValueError('tensor capacity')
        a,b,r,s=([f.canonical(x) for x in values] for values in (a,b,r,s))
        if self.tensor is None:return [f.add(f.mul(x,y),f.mul(z,t)) for x,z in zip(a,b) for y,t in zip(r,s)]
        out=(ctypes.c_uint32*(8*n))()
        if self.tensor(self.pack(a),self.pack(b),len(a),self.pack(r),self.pack(s),len(r),out,n):raise ValueError('native tensor rejected')
        return self.unpack(out,n)

    def gkr_round(self,gates,weights,original,folded,axis,bit,fixed_left=f.ZERO):
        if type(axis)is not int or axis not in (0,1) or type(bit)is not int or not 0<=bit<32:
            raise ValueError('GKR axis/bit')
        if len(gates)!=len(weights) or len(folded)<2 or len(folded)%2:raise ValueError('GKR shape')
        words=[]
        for op,i,j in gates:
            if op not in ('add','sub','mul') or any(type(x)is not int or not 0<=x<len(original) or x>=2**32 for x in (i,j)):
                raise ValueError('GKR gate')
            if (((i if axis==0 else j)>>bit)|1)>=len(folded):raise ValueError('GKR folded index')
            words.extend(({'add':0,'sub':1,'mul':2}[op],i,j))
        gs=(ctypes.c_uint32*max(1,len(words)))(*words)
        w=self.pack(weights);v=self.pack(original);fv=self.pack(folded);left=self.pack([fixed_left]);out=(ctypes.c_uint32*24)()
        if self.lib.near_ext8_gkr_round(gs,len(gates),w,v,len(original),fv,len(folded),axis,bit,left,out):
            raise ValueError('native GKR round rejected')
        return self.unpack(out,3)

    def fft_words(self,words, *, lde4=False):
        if not isinstance(words,array) or words.typecode!='I' or words.itemsize!=4 or not words or len(words)%8:
            raise ValueError('Ext8 uint32 words')
        n=len(words)//8;domain=n*(4 if lde4 else 1)
        if domain>1<<22 or domain&(domain-1):raise ValueError('FFT domain')
        out=array('I',[0])*(8*domain)
        src=(ctypes.c_uint32*len(words)).from_buffer(words);dst=(ctypes.c_uint32*len(out)).from_buffer(out)
        if self.lib.near_ext8_fft(src,len(words),dst,len(out),domain):raise ValueError('native FFT rejected')
        return out
    def lde4_words(self,words):return self.fft_words(words,lde4=True)
    def fft(self,coefficients, *, lde4=False):
        words=array('I',[x for c in coefficients for x in f.canonical(c)])
        out=self.fft_words(words,lde4=lde4)
        return [tuple(out[i:i+8]) for i in range(0,len(out),8)]
