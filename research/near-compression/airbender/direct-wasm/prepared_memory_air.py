"""scalar-memory-access-v1: successful integer memory-access request adapter.

Separate ABI, no change to prepared-typed-v1. EXEC receive and MEM send are
open interfaces: this table alone does not authenticate CODE/stack/gas, initial
roots or chronology. Traps, grow, bulk memory and host accesses are not covered.
All message integers use bounded 16-bit limbs, never reduced 64-bit scalars.
"""
from prepared_function_air import c,v,plus,sub,mul,sm,putbits,eval_expr,P
# (opcode, bytes, signed load, i64 value/result, write)
OPS=[(0x28,4,0,0,0),(0x29,8,0,1,0),
     (0x2c,1,1,0,0),(0x2d,1,0,0,0),(0x2e,2,1,0,0),(0x2f,2,0,0,0),
     (0x30,1,1,1,0),(0x31,1,0,1,0),(0x32,2,1,1,0),(0x33,2,0,1,0),
     (0x34,4,1,1,0),(0x35,4,0,1,0),
     (0x36,4,0,0,1),(0x37,8,0,1,1),(0x3a,1,0,0,1),(0x3b,2,0,0,1),
     (0x3c,1,0,1,1),(0x3d,2,0,1,1),(0x3e,4,0,1,1)]
OP=0;INSTANCE=19;CLOCK=51;ADDRESS=115;OFFSET=147;EA=179;PAGES=212
VALUE=229;RAW=293;RESULT=357;SLACK=421;ACARRY=454;BCARRY=456;WIDTH=460

def bits(base,n=16):return sm(mul(c(2**i),v(base+i)) for i in range(n))
def limbs(base,n):return [bits(base+i,min(16,n-i)) for i in range(0,n,16)]
def sel(index):return sm(mul(v(OP+i),c(op[index])) for i,op in enumerate(OPS))
def table(exec_bus=0,mem_bus=1):
    cs=[]
    def eq(a,b):cs.append(sub(a,b))
    for i in range(WIDTH):eq(mul(v(i),sub(v(i),c(1))),c(0))
    eq(sm(v(OP+i) for i in range(len(OPS))),c(1))
    # At most 65536 Wasm pages. Page count is a request-bound external state field.
    for i in range(16):eq(mul(v(PAGES+16),v(PAGES+i)),c(0))
    # Natural 33-bit address = uint32 operand + uint32 static offset.
    eq(plus(bits(ADDRESS),bits(OFFSET)),plus(bits(EA),mul(c(65536),v(ACARRY))))
    eq(plus(plus(bits(ADDRESS+16),bits(OFFSET+16)),v(ACARRY)),
       plus(bits(EA+16),mul(c(65536),v(ACARRY+1))))
    eq(v(EA+32),v(ACARRY+1))
    for i in (0,2):eq(mul(v(BCARRY+i),v(BCARRY+i+1)),c(0))
    # Successful access: EA + width + slack = pages*65536, with no field alias.
    eq(plus(plus(bits(EA),sel(1)),bits(SLACK)),mul(c(65536),bits(BCARRY,2)))
    eq(plus(plus(bits(EA+16),bits(SLACK+16)),bits(BCARRY,2)),
       plus(bits(PAGES),mul(c(65536),bits(BCARRY+2,2))))
    eq(plus(plus(v(EA+32),v(SLACK+32)),bits(BCARRY+2,2)),v(PAGES+16))
    for b in range(64):
        # Raw is the unsigned transferred little-endian value, zero above width.
        valid=sm(v(OP+i) for i,(_,w,_,_,_) in enumerate(OPS) if b<8*w)
        eq(mul(sub(c(1),valid),v(RAW+b)),c(0))
        store=sel(4)
        eq(mul(store,v(RAW+b)),sm(mul(v(OP+i),v(VALUE+b))
          for i,(_,w,_,_,wr) in enumerate(OPS) if wr and b<8*w))
        # Load has no value operand; i32 store has no high half.
        value_live=sm(v(OP+i) for i,(_,_,_,i64,wr) in enumerate(OPS) if wr and b<(64 if i64 else 32))
        eq(mul(sub(c(1),value_live),v(VALUE+b)),c(0))
        out=[]
        for i,(_,w,signed,i64,wr) in enumerate(OPS):
            if wr or b>=(64 if i64 else 32):continue
            if b<8*w:out.append(mul(v(OP+i),v(RAW+b)))
            elif signed:out.append(mul(v(OP+i),v(RAW+8*w-1)))
        eq(v(RESULT+b),sm(out))
    ident=limbs(INSTANCE,32)+limbs(CLOCK,64)
    # EXEC must bind these to actual selected operands, code and memory size.
    execute=ident+[sel(0),sel(3),sel(4)]+limbs(ADDRESS,32)+limbs(OFFSET,32)+limbs(PAGES,17)+limbs(VALUE,64)+limbs(RESULT,64)
    memory=ident+limbs(EA,33)+[sel(1),sel(4)]+limbs(RAW,64)
    return dict(width=WIDTH,maxLog=22,constraints=cs,interactions=[
      dict(bus=exec_bus,msg=execute,mult=[c(1)],send=False),
      dict(bus=mem_bus,msg=memory,mult=[c(1)],send=True)])

def witness(op,address,offset,pages,value=0,raw=0,clock=0,instance=0):
    spec=next(x for x in OPS if x[0]==op);_,width,signed,i64,write=spec
    assert 0<=address<2**32 and 0<=offset<2**32 and 0<=pages<=65536
    assert 0<=clock<2**64 and 0<=instance<2**32
    assert 0<=value<2**(64 if i64 else 32)
    ea=address+offset;slack=pages*65536-ea-width
    assert slack>=0
    if write:raw=value%(256**width);result=0
    else:
      assert value==0 and 0<=raw<256**width
      result=raw
      if signed and raw>=2**(8*width-1):result=(raw-256**width)%2**(64 if i64 else 32)
    row=[0]*WIDTH;row[OPS.index(spec)]=1
    for base,x,n in [(INSTANCE,instance,32),(CLOCK,clock,64),(ADDRESS,address,32),(OFFSET,offset,32),
      (EA,ea,33),(PAGES,pages,17),(VALUE,value,64),(RAW,raw,64),(RESULT,result,64),(SLACK,slack,33)]:putbits(row,base,x,n)
    row[ACARRY]=((address&65535)+(offset&65535))>>16
    row[ACARRY+1]=ea>>32
    bc=((ea&65535)+width+(slack&65535))>>16
    putbits(row,BCARRY,bc,2)
    putbits(row,BCARRY+2,(((ea>>16)&65535)+((slack>>16)&65535)+bc)>>16,2)
    return row

def residuals(row):return [eval_expr(e,row,row,[],False,False) for e in table()['constraints']]
def messages(row):return [[eval_expr(e,row,row,[],False,False) for e in x['msg']] for x in table()['interactions']]
