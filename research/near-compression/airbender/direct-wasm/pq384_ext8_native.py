"""Explicit native Ext8 fold/quadratic adapter; not a complete prover.

Build kernel_ext8.rs as a cdylib and supply its path. Python validates shape
and scalar canonicality before allocation; Rust independently checks scalars.
"""
import ctypes
import pq384_ext8_reference as f

class Kernel:
    def __init__(self, library):
        self.lib=ctypes.CDLL(str(library))
        ptr=ctypes.POINTER(ctypes.c_uint32)
        self.lib.near_ext8_fold.argtypes=[ptr,ctypes.c_size_t,ptr,ptr]
        self.lib.near_ext8_quadratic.argtypes=[ptr,ptr,ctypes.c_size_t,ptr]
        self.lib.near_ext8_fold.restype=self.lib.near_ext8_quadratic.restype=ctypes.c_int
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
