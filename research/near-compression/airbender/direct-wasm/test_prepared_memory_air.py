"""Independent scalar semantics oracle and coherent request mutation tests."""
import json
from prepared_memory_air import *
def main():
  honest=mutants=coherent=0
  for op,width,signed,i64,write in OPS:
    for address,offset,pages in [(0,0,1),(4095,0,2),(65535,0,2),(2**32-width,0,65536),(65534,2,2)]:
      for raw in [0,1,2**(8*width-1),256**width-1]:
        value=0xfedcba9876543210%(2**(64 if i64 else 32)) if write else 0
        row=witness(op,address,offset,pages,value,raw,clock=2**64-1,instance=17)
        assert not any(residuals(row));honest+=1
        msg=messages(row)
        actual_raw=value%(256**width) if write else raw
        expected=0 if write else int.from_bytes(actual_raw.to_bytes(width,'little'),'little',signed=bool(signed))%2**(64 if i64 else 32)
        decode=lambda base,n:sum(row[base+i]<<i for i in range(n))
        assert decode(RESULT,64)==expected and decode(EA,33)==address+offset
        assert msg[1][-4:]==[(actual_raw>>(16*i))&65535 for i in range(4)]
        for col in [EA,EA+32,SLACK,ACARRY,BCARRY,RESULT,RAW,OP+OPS.index((op,width,signed,i64,write))]:
          bad=row.copy();bad[col]^=1
          assert any(residuals(bad)),(op,col);mutants+=1
        # Re-encode raw/result coherently on a store: must still bind actual operand.
        if write:
          bad=row.copy();putbits(bad,RAW,(actual_raw+1)%(256**width),64)
          assert any(residuals(bad));coherent+=1
  # Natural overflow cannot wrap into a low address and pass successful bounds.
  rejected=0
  for op,addr,off,pages in [(0x29,2**32-1,1,65536),(0x28,65535,0,1),(0x28,0,0,0),(0x28,0,0,65537)]:
    try:witness(op,addr,off,pages)
    except AssertionError:rejected+=1
    else:raise AssertionError('accepted invalid bounds')
  row=witness(0x29,0,0,1,raw=0)
  # Coherent 33-bit overflow with internally correct address carries, but a
  # wrapped low bounds witness: limb bounds must reject it.
  putbits(row,ADDRESS,2**32-1,32);putbits(row,OFFSET,1,32);putbits(row,EA,2**32,33)
  row[ACARRY]=row[ACARRY+1]=1
  assert any(residuals(row));coherent+=1
  print(json.dumps(dict(profile='scalar-memory-access-v1',columns=WIDTH,constraints=len(table()['constraints']),
    honest=honest,bit_mutations=mutants,coherent_mutations=coherent,bounds_rejections=rejected,
    scope='request adapter; EXEC/CODE/stack/gas and MEM service buses not yet composed')))
if __name__=='__main__':main()
