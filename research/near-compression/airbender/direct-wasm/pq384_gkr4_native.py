"""Explicit native Ext4 GKR round/fold adapter; not a complete prover.

Build kernel_gkr4.rs as a cdylib and supply its path. Python validates shape
and scalar canonicality before allocation; Rust independently checks scalars.
"""
import ctypes
from types import SimpleNamespace
from packed_claim_handoff import canonical_ext
from verify_whir_toy import ZERO
f=SimpleNamespace(canonical=canonical_ext,ZERO=ZERO)

class Kernel:
    def __init__(self, library):
        self.lib=ctypes.CDLL(str(library))
        ptr=ctypes.POINTER(ctypes.c_uint32)
        self.lib.near_ext4_fold.restype=ctypes.c_int
        self.lib.near_ext4_fold.argtypes=[ptr,ctypes.c_size_t,ptr,ptr]
        self.lib.near_ext4_gkr_round.argtypes=[ptr,ctypes.c_size_t,ptr,ptr,ctypes.c_size_t,ptr,ctypes.c_size_t,ctypes.c_uint32,ctypes.c_uint32,ptr,ptr]
        self.lib.near_ext4_gkr_round.restype=ctypes.c_int
    @staticmethod
    def pack(values):
        words=[x for value in values for x in f.canonical(value)]
        # Non-null buffer even for the empty-table identity.
        return (ctypes.c_uint32*max(1,len(words)))(*words)
    @staticmethod
    def unpack(buffer,n):return [tuple(buffer[4*i:4*i+4]) for i in range(n)]
    def affine_fold(self,values,r):
        if len(values)%2:raise ValueError('fold shape')
        a=self.pack(values);challenge=self.pack([r]);out=(ctypes.c_uint32*max(1,len(values)*2))()
        if self.lib.near_ext4_fold(a,len(values),challenge,out):raise ValueError('native fold rejected')
        return self.unpack(out,len(values)//2)
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
        w=self.pack(weights);v=self.pack(original);fv=self.pack(folded);left=self.pack([fixed_left]);out=(ctypes.c_uint32*12)()
        if self.lib.near_ext4_gkr_round(gs,len(gates),w,v,len(original),fv,len(folded),axis,bit,left,out):
            raise ValueError('native GKR round rejected')
        return self.unpack(out,3)

