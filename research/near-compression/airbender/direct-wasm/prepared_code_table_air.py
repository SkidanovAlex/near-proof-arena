"""Executable staged direct-Wasm AIR: numeric PC and authenticated CODE table.

No CODE16 limit. Stack8 and one defined function remain explicit. Independent
actual prepare/step fixtures supply witness provenance; new Lean refinement is
not yet proved. Public CODE is linear-size, outside the cryptographic proof.
"""
from collections import Counter
from prepared_function_air import c,v,plus,neg,sub,mul,sm,putbits,val,eval_expr,P
CAP=8
PC=0;SP=32;DONE=41;FAIL=42;STACK=43;GAS=299;DIFF=363;BORROW=427;RESULT=431;CARRY=463
PCCARRY=465;OP=466;IMM=470;FEE=502;HAS=566;KIND=567;FN=573;WIDTH=605
CACTIVE=0;CPC=1;CFN=33;COP=65;CIMM=69;CFEE=101;CHAS=165;CKIND=166;COUNT=172;CCARRY=197;CWIDTH=198
MSG=27;CODEPUB=66;RECORD=25

def bits(base,n=16,next=0):return sm(mul(c(2**i),v(base+i,next)) for i in range(n))
def sp(next=0):return sm(mul(c(i),v(SP+i,next)) for i in range(CAP+1))
def word(slot,limb,next=0):return bits(STACK+32*slot+16*limb,16,next)
def fetch(field):
    if field<4:return v(OP+field)
    if field<6:return bits(IMM+16*(field-4))
    return bits(FEE+16*(field-6))
def boundary():return [bits(FN),bits(FN+16),bits(PC),bits(PC+16),sp(),v(DONE),v(FAIL)]+[bits(GAS+16*i) for i in range(4)]+[word(j,i) for j in range(CAP) for i in range(2)]
def descriptor(pc,fn,op,imm,fee,has,kind):
    return [bits(fn),bits(fn+16),bits(pc),bits(pc+16)]+[v(op+i) for i in range(4)]+[bits(imm),bits(imm+16)]+[bits(fee+16*i) for i in range(4)]+[v(has)]+[v(kind+i) for i in range(6)]+[c(0)]*4

def exec_table():
    cs=[]
    def eq(a,b,gate=None):
        residual=sub(a,b);cs.append(residual if gate is None else mul(gate,residual))
    for i in range(WIDTH):eq(mul(v(i),sub(v(i),c(1))),c(0))
    eq(sm(v(SP+i) for i in range(CAP+1)),c(1))
    # done/fail flags are monotone; failed implies done.
    eq(mul(v(FAIL),sub(c(1),v(DONE))),c(0))
    active=sub(c(1),v(DONE));failed=mul(active,v(BORROW+3));success=mul(active,sub(c(1),v(BORROW+3)))
    ops=[fetch(i) for i in range(4)];const,add,drop,end=ops
    eq(sm(ops),c(1))
    
    for i in range(32):eq(v(PC+i),c(0),['first'])
    eq(v(SP),c(1),['first']);eq(v(DONE),c(0),['first'])
    eq(v(DONE),c(1),['last'])
    # Four limb bounded subtraction; terminal borrow is exact fee>gas test.
    for i in range(4):
        borrow=c(0) if i==0 else v(BORROW+i-1)
        eq(sub(sub(bits(GAS+16*i),fetch(6+i)),borrow),sub(bits(DIFF+16*i),mul(c(65536),v(BORROW+i))))
    stop=plus(failed,mul(success,end));advance=mul(success,sub(c(1),end))
    trans=['trans']
    eq(v(DONE,1),plus(v(DONE),stop),trans);eq(v(FAIL,1),plus(v(FAIL),failed),trans)
    eq(plus(bits(PC),advance),plus(bits(PC,16,1),mul(c(65536),v(PCCARRY))),trans)
    eq(bits(PC+16,16,1),plus(bits(PC+16),v(PCCARRY)),trans)
    for i in range(32):eq(v(FN+i),c(0))
    delta=mul(success,sub(const,plus(add,drop)))
    eq(sp(1),plus(sp(),delta),trans)
    eq(mul(success,mul(const,v(SP+CAP))),c(0))
    eq(mul(success,mul(add,plus(v(SP),v(SP+1)))),c(0))
    eq(mul(success,mul(drop,v(SP))),c(0))
    eq(mul(success,mul(end,sub(c(1),v(SP)))),c(0))
    for i in range(4):eq(bits(GAS+16*i,16,1),plus(mul(success,bits(DIFF+16*i)),mul(sub(c(1),success),bits(GAS+16*i))),trans)
    # Addition operands selected from the entire authenticated stack snapshot.
    for limb in range(2):
        left=sm(mul(v(SP+j),word(j-2,limb)) for j in range(2,CAP+1))
        right=sm(mul(v(SP+j),word(j-1,limb)) for j in range(2,CAP+1))
        eq(plus(plus(left,right),c(0) if limb==0 else v(CARRY)),plus(bits(RESULT+16*limb),mul(c(65536),v(CARRY+limb))),mul(success,add))
    for slot in range(CAP):
        live=sm(v(SP+j) for j in range(slot+1,CAP+1))
        for limb in range(2):
            old=word(slot,limb)
            eq(mul(sub(c(1),live),old),c(0))
            push=mul(success,mul(const,v(SP+slot)))
            write=mul(success,mul(add,v(SP+slot+2) if slot+2<=CAP else c(0)))
            clear=mul(success,mul(plus(add,drop),v(SP+slot+1)))
            new=plus(mul(sub(c(1),plus(plus(push,write),clear)),old),plus(mul(push,fetch(4+limb)),mul(write,bits(RESULT+16*limb))))
            eq(word(slot,limb,1),new,trans)
    return dict(width=WIDTH,maxLog=22,constraints=cs,interactions=[
      dict(bus=i,msg=boundary(),mult=[[flag]],send=True) for i,flag in enumerate(('first','last'))]+[
      dict(bus=2,msg=descriptor(PC,FN,OP,IMM,FEE,HAS,KIND),mult=[c(1)],send=True)])

def code_table():
    cs=[]
    def eq(a,b,gate=None):cs.append(sub(a,b) if gate is None else mul(gate,sub(a,b)))
    for i in range(CWIDTH):eq(mul(v(i),sub(v(i),c(1))),c(0))
    eq(v(CACTIVE),c(1),['first'])
    for i in range(32):
      eq(v(CPC+i),c(0),['first']);eq(v(CFN+i),c(0))
    eq(mul(sub(c(1),v(CACTIVE)),v(CACTIVE,1)),c(0),['trans'])
    link=mul(['trans'],v(CACTIVE,1))
    eq(plus(bits(CPC),c(1)),plus(bits(CPC,16,1),mul(c(65536),v(CCARRY))),link)
    eq(bits(CPC+16,16,1),plus(bits(CPC+16),v(CCARRY)),link)
    # Inactive rows cannot receive fetches or send public records.
    for i in range(1,CWIDTH):eq(v(i),c(0),sub(c(1),v(CACTIVE)))
    eq(sm(v(COP+i) for i in range(4)),v(CACTIVE))
    eq(sm(v(CKIND+i) for i in range(6)),v(CHAS))
    eq(v(CKIND+5),c(0)) # linear charging is outside this slice
    eq(mul(v(CHAS),sub(c(1),v(CACTIVE))),c(0))
    for i in range(4):eq(bits(CFEE+16*i),c(0),sub(c(1),v(CHAS)))
    for i in range(2):eq(bits(CIMM+16*i),c(0),sub(c(1),v(COP)))
    msg=descriptor(CPC,CFN,COP,CIMM,CFEE,CHAS,CKIND)
    return dict(width=CWIDTH,maxLog=22,constraints=cs,interactions=[
      dict(bus=2,msg=msg,mult=[v(COUNT+i) for i in range(25)],send=False),
      dict(bus=3,msg=msg,mult=[v(CACTIVE)],send=True)])

def air(code_length):
    numpub=CODEPUB+RECORD*code_length
    return dict(format='np-air-v2',numPub=numpub,maxPub=numpub,numBuses=4,
      pubSegs=[dict(bus=i,countAt=4*i,indexBase=None,prefix=[],send=False,start=12+i*MSG,startAt=None,width=MSG) for i in range(2)]+[
        dict(bus=3,countAt=8,indexBase=None,prefix=[],send=False,start=CODEPUB,startAt=None,width=RECORD)],
      tables=[exec_table(),code_table()])

def put_descriptor(row,entry,pc,fn,op,imm,fee,has,kind):
    assert entry['function']==0 and 0<=entry['pc']<2**32
    opcode=entry['instruction']['opcode'];assert opcode in (65,106,26,11)
    immediate=entry['instruction']['immediate'];assert 0<=immediate<2**32
    assert opcode==65 or immediate==0
    putbits(row,pc,entry['pc'],32);putbits(row,fn,entry['function'],32)
    row[op+(65,106,26,11).index(opcode)]=1;putbits(row,imm,immediate,32)
    charge=entry['charge']
    if charge is not None:
      assert charge['linear']==0 and not charge['linear_kind'] and 0<=charge['kind']<5
      row[has]=1;row[kind+charge['kind']]=1;putbits(row,fee,charge['constant'],64)

def row_at(code,pc,stack,g,done,failed):
    assert 0<=pc<len(code)<2**32 and len(stack)<=CAP
    row=[0]*WIDTH;put_descriptor(row,code[pc],PC,FN,OP,IMM,FEE,HAS,KIND)
    row[SP+len(stack)]=1;row[DONE]=int(done);row[FAIL]=int(failed)
    for i,value in enumerate(stack):putbits(row,STACK+32*i,value,32)
    putbits(row,GAS,g,64)
    fee=0 if code[pc]['charge'] is None else code[pc]['charge']['constant']
    putbits(row,DIFF,(g-fee)%2**64,64)
    borrow=0
    for i in range(4):
      borrow=int(((g>>(16*i))&65535)-((fee>>(16*i))&65535)-borrow<0);row[BORROW+i]=borrow
    advance=not done and g>=fee and code[pc]['instruction']['opcode']!=11
    row[PCCARRY]=int(advance and pc%65536==65535)
    if code[pc]['instruction']['opcode']==106 and len(stack)>=2:
      a,b=stack[-2:];putbits(row,RESULT,(a+b)%2**32,32)
      row[CARRY]=int((a&65535)+(b&65535)>=65536);row[CARRY+1]=int(a+b>=2**32)
    return row

def pad(rows):
    n=max(1,(len(rows)-1).bit_length());return n,rows+[rows[-1][:] for _ in range(2**n-len(rows))]
def nat4(n):
    assert 0<=n<2**32
    return [(n>>(8*i))&255 for i in range(4)]
def make(case):
    code=case['code'];assert code and len(code)<2**32
    assert case['prepaid']<=10**15 and case['entry_after']['gas']['promises']==0
    assert all(e['pc']==i and e['function']==0 for i,e in enumerate(code))
    rows=[]
    for event in case['exec_rows']:
      before=event['before'];assert len(before['frames'])==1 and before['frames'][0]['fn']==0
      rows.append(row_at(code,event['pc'],[val(v) for v in before['stack']],before['gas']['g'],False,False))
    last=case['exec_rows'][-1];after=last['after'];failed=last['status']=='abort'
    assert last['status'] in ('finish','abort')
    rows.append(row_at(code,last['pc'],[val(v) for v in after['stack']],after['gas']['g'],True,failed))
    en,rows=pad(rows)
    counts=Counter(sum(row[PC+i]<<i for i in range(32)) for row in rows)
    code_rows=[]
    for i,entry in enumerate(code):
      row=[0]*CWIDTH;row[CACTIVE]=1;put_descriptor(row,entry,CPC,CFN,COP,CIMM,CFEE,CHAS,CKIND)
      putbits(row,COUNT,counts[i],25);row[CCARRY]=int(i%65536==65535 and i+1<len(code));code_rows.append(row)
    cn=max(1,(len(code_rows)-1).bit_length());code_rows += [[0]*CWIDTH for _ in range(2**cn-len(code_rows))]
    def evs(exprs,row):return [eval_expr(e,row,row,[],False,False) for e in exprs]
    public=nat4(1)+nat4(1)+nat4(len(code))+evs(boundary(),rows[0])+evs(boundary(),rows[-1])
    public += [x for row in code_rows[:len(code)] for x in evs(descriptor(CPC,CFN,COP,CIMM,CFEE,CHAS,CKIND),row)]
    return dict(air=air(len(code)),public=public,log_rows=[en,cn]),[rows,code_rows]
