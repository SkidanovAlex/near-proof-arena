"""Owned Ext8 local-sumcheck table state; transcript and PCS remain external."""
import ctypes as C
import pq384_ext8_reference as f
from pq384_ext8_native import Kernel

def library(path):
    lib=C.CDLL(str(path));ptr=C.POINTER(C.c_uint32);sz=C.c_size_t;handle=C.c_void_p
    signatures={'new':([ptr,sz,sz],handle),'free':([handle],None),
        'fold':([handle,ptr],C.c_int),'round':([handle,ptr,sz,ptr,sz,ptr,sz,sz,ptr],C.c_int),
        'terminal':([handle,ptr],C.c_int)}
    for name,(args,result) in signatures.items():
        fn=getattr(lib,'np8_'+name);fn.argtypes=args;fn.restype=result
    return lib

class NativeTable:
    def __init__(self,rows,program,tau,lib):
        self.lib=lib;self.handle=None;self.prefix=[];self.n=len(tau)
        if not rows or not rows[0] or not 0<self.n<32 or len(rows)!=1<<self.n:raise ValueError('table shape')
        self.width=len(rows[0])
        if any(len(row)!=self.width or any(type(x)is not int or not 0<=x<f.P for x in row) for row in rows):raise ValueError('base rows')
        if not program or len(program)%11 or any(type(x)is not int or not 0<=x<2**32 for x in program):raise ValueError('program words')
        self.program=(C.c_uint32*len(program))(*program);self.tau=Kernel.pack(tau)
        data=(C.c_uint32*(len(rows)*self.width))(*(x for row in rows for x in row))
        self.handle=lib.np8_new(data,len(rows),self.width)
        if not self.handle:raise ValueError('native table rejected')
    def close(self):
        if self.handle:self.lib.np8_free(self.handle);self.handle=None
    def __enter__(self):return self
    def __exit__(self,*args):self.close()
    def values(self,nodes):
        if not self.handle or len(self.prefix)>=self.n or type(nodes)is not int or not 0<nodes<=1000:raise ValueError('round state')
        out=(C.c_uint32*(8*nodes))();prefix=Kernel.pack(self.prefix)
        status=self.lib.np8_round(self.handle,self.program,len(self.program)//11,self.tau,self.n,prefix,len(self.prefix),nodes,out)
        if status:raise ValueError('native round rejected: '+str(status))
        return Kernel.unpack(out,nodes)
    def fold(self,r):
        if not self.handle or len(self.prefix)>=self.n:raise ValueError('fold state')
        r=f.canonical(r)
        if self.lib.np8_fold(self.handle,Kernel.pack([r])):raise ValueError('native fold rejected')
        self.prefix.append(r)
    def terminal(self):
        if not self.handle or len(self.prefix)!=self.n:raise ValueError('terminal state')
        out=(C.c_uint32*(16*self.width))()
        if self.lib.np8_terminal(self.handle,out):raise ValueError('native terminal rejected')
        values=Kernel.unpack(out,2*self.width)
        return values[:self.width],values[self.width:]
