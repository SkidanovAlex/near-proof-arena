"""Memory-mapped untrusted prover cache; commitments are checked externally.

Exact shape/root/context are supplied by the caller. Source openings are
authenticated when read. Coefficient correctness is NOT assumed by a verifier.
"""
from array import array
from contextlib import ExitStack
import json,mmap,struct,sys
from pathlib import Path
from pq384_primitives import P,require,verify_path
from packed_claim_handoff import packing_context


class SourceCache:
    def __init__(self,path,*,expected_root,log_rows,width,packing):
        self._resources=ExitStack()
        try:
            path=Path(path);m=json.loads((path/'manifest.json').read_text())
            self.context=packing_context(log_rows,width,packing)
            self.degree=(1<<log_rows)*packing;self.lanes=(width+packing-1)//packing
            self.half=2*self.degree;self.root=expected_root
            require(type(expected_root)is bytes and len(expected_root)==48,'cache root')
            require(m['format']=='near-pq384-source-cache-v1' and
                    m['root_hex']==expected_root.hex() and m['context_hex']==self.context.hex(),
                    'cache identity')
            expected={'rows':1<<log_rows,'width':width,'packing':packing,'lanes':self.lanes,
                      'degree':self.degree,'leaf_count':self.half}
            require(all(type(m[k])is int and m[k]==v for k,v in expected.items()),'cache shape')
            def mapped(name,size):
                file=self._resources.enter_context((path/name).open('rb'))
                require(file.seek(0,2)==size,'cache file length');file.seek(0)
                return self._resources.enter_context(mmap.mmap(file.fileno(),0,access=mmap.ACCESS_READ))
            self.coeff=mapped('coefficients.u32',self.degree*self.lanes*4)
            self.leaves=mapped('leaves.u32',self.half*self.lanes*8)
            self.tree=mapped('tree.sha384',(2*self.half-1)*48)
        except BaseException:
            self._resources.close();raise

    def __enter__(self):return self
    def __exit__(self,*args):self._resources.close()

    def coefficients(self,lane):
        require(type(lane)is int and 0<=lane<self.lanes,'cache lane')
        offset=lane*self.degree*4;values=array('I')
        require(values.itemsize==4,'u32 array width')
        values.frombytes(self.coeff[offset:offset+self.degree*4])
        if sys.byteorder!='little':values.byteswap()
        require(all(v<P for v in values),'cache canonical coefficients')
        return values

    def opening(self,index):
        require(type(index)is int and 0<=index<self.half,'cache index')
        size=self.lanes*8;leaf=self.leaves[index*size:(index+1)*size]
        values=list(struct.unpack('<'+'I'*(2*self.lanes),leaf))
        require(all(v<P for v in values),'cache canonical leaf')
        path=[];i=index;n=self.half;offset=0
        while n>1:
            start=offset+(i^1)*48;path.append(self.tree[start:start+48])
            offset+=n*48;n//=2;i//=2
        verify_path(self.root,self.context,self.half,index,leaf,path)
        return {'leaf':values,'path':[v.hex() for v in path]}
