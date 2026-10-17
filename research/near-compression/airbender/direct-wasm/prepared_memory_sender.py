"""memory-exec-sender-v1: bounded mixed-stack source for scalar-memory-access-v1.

Memory-only contiguous instruction segments, stack8. CODE bus emits7fields;
its authenticated receiver, gas provenance and public segment boundaries are
not supplied here. This is not an extension of frozen prepared-typed-v1.
"""
from prepared_memory_air import OPS
from prepared_function_air import c,v,plus,sub,mul,sm,putbits,eval_expr
STACK=0;TYPE=512;SP=520;OP=529;OFFSET=548;CLOCK=580;PAGES=644;INSTANCE=661;RESULT=693;PC=757;PCCARRY=789;TCARRY=791;WIDTH=795

def bits(base,n=16,nx=0):return sm(mul(c(2**i),v(base+i,nx)) for i in range(n))
def limbs(base,n):return [bits(base+i,min(16,n-i)) for i in range(0,n,16)]
def sel(k):return sm(mul(v(OP+i),c(op[k])) for i,op in enumerate(OPS))
def selected(base,stride,depth):return sm(mul(v(SP+j),v(base+stride*(j-depth))) for j in range(depth,9))
def selected_word(limb,depth):return sm(mul(v(SP+j),bits(STACK+64*(j-depth)+16*limb)) for j in range(depth,9))
def table():
  cs=[]
  def eq(a,b,gate=None):cs.append(sub(a,b) if gate is None else mul(gate,sub(a,b)))
  for i in range(WIDTH):eq(mul(v(i),sub(v(i),c(1))),c(0))
  eq(sm(v(SP+j) for j in range(9)),c(1));eq(sm(v(OP+j) for j in range(19)),c(1))
  write=sel(4);load=sub(c(1),write)
  eq(v(SP),c(0));eq(mul(write,v(SP+1)),c(0))
  # Type of the consumed address is always i32; stored value matches opcode.
  eq(plus(mul(load,selected(TYPE,1,1)),mul(write,selected(TYPE,1,2))),c(0))
  eq(mul(write,sub(selected(TYPE,1,1),sel(3))),c(0))
  for j in range(8):
    live=sm(v(SP+k) for k in range(j+1,9))
    eq(mul(sub(c(1),live),v(TYPE+j)),c(0))
    for b in range(64):
      eq(mul(sub(c(1),live),v(STACK+64*j+b)),c(0))
      if b>=32:eq(mul(sub(c(1),v(TYPE+j)),v(STACK+64*j+b)),c(0))
  for b in range(64):eq(mul(write,v(RESULT+b)),c(0))
  for b in range(16):eq(mul(v(PAGES+16),v(PAGES+b)),c(0))
  trans=['trans']
  for j in range(9):
    eq(v(SP+j,1),plus(mul(load,v(SP+j)),mul(write,v(SP+j+2)) if j+2<=8 else c(0)),trans)
  for j in range(8):
    retain=plus(mul(load,sm(v(SP+k) for k in range(j+2,9))),mul(write,sm(v(SP+k) for k in range(j+3,9))))
    push=mul(load,v(SP+j+1))
    for b in range(64):eq(v(STACK+64*j+b,1),plus(mul(retain,v(STACK+64*j+b)),mul(push,v(RESULT+b))),trans)
    eq(v(TYPE+j,1),plus(mul(retain,v(TYPE+j)),mul(push,sel(3))),trans)
  for i in range(2):
    eq(plus(bits(PC+16*i),c(1) if i==0 else v(PCCARRY+i-1)),plus(bits(PC+16*i,16,1),mul(c(65536),v(PCCARRY+i))),trans)
  eq(v(PCCARRY+1),c(0),trans)
  for i in range(4):
    eq(plus(bits(CLOCK+16*i),c(1) if i==0 else v(TCARRY+i-1)),plus(bits(CLOCK+16*i,16,1),mul(c(65536),v(TCARRY+i))),trans)
  eq(v(TCARRY+3),c(0),trans)
  for base,n in [(PAGES,17),(INSTANCE,32)]:
    for b in range(n):eq(v(base+b,1),v(base+b),trans)
  identity=limbs(INSTANCE,32)+limbs(CLOCK,64)
  address=[plus(mul(load,selected_word(i,1)),mul(write,selected_word(i,2))) for i in range(2)]
  operand=[mul(write,selected_word(i,1)) for i in range(4)]
  execute=identity+[sel(0),sel(3),write]+address+limbs(OFFSET,32)+limbs(PAGES,17)+operand+limbs(RESULT,64)
  code=limbs(INSTANCE,32)+limbs(PC,32)+[sel(0)]+limbs(OFFSET,32)
  return dict(width=WIDTH,maxLog=22,constraints=cs,interactions=[
    dict(bus=0,msg=execute,mult=[c(1)],send=True),dict(bus=2,msg=code,mult=[c(1)],send=True)])

def witness(event,instance=0):
  row=[0]*WIDTH;stack=event['stack'];assert 1<=len(stack)<=8
  spec=next(x for x in OPS if x[0]==event['opcode']);row[OP+OPS.index(spec)]=1;row[SP+len(stack)]=1
  for j,(tag,value) in enumerate(stack):
    assert tag in (0,1) and 0<=value<2**(64 if tag else 32)
    putbits(row,64*j,value,64);row[TYPE+j]=tag
  for base,x,n in [(OFFSET,event['offset'],32),(CLOCK,event['clock'],64),(PAGES,event['pages'],17),
      (INSTANCE,instance,32),(RESULT,event['result'],64),(PC,event['pc'],32)]:
    assert 0<=x<2**n;putbits(row,base,x,n)
  for base,cbase,n in [(PC,PCCARRY,2),(CLOCK,TCARRY,4)]:
    x=event['pc'] if base==PC else event['clock'];carry=1
    for i in range(n):carry=int(((x>>(16*i))&65535)+carry>=65536);row[cbase+i]=carry
  return row

def residuals(rows):
  cs=table()['constraints']
  return [[eval_expr(e,row,rows[(i+1)%len(rows)],[],i==0,i==len(rows)-1) for e in cs] for i,row in enumerate(rows)]
def message(row):return [eval_expr(e,row,row,[],False,False) for e in table()['interactions'][0]['msg']]
