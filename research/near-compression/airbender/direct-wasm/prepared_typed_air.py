"""Versioned mixed i32/i64 prepared execution diagnostic.

Full EXEC/CODE polynomial source and natural buses, stack8/locals4/oneblock.
Actual PREP/type provenance and whole-call formal refinement are not yet proved.
The frozen prepared-locals-v1 source is not modified.
"""
from collections import Counter
from prepared_function_air import c,v,plus,neg,sub,mul,sm,putbits,val,eval_expr,P
CAP=8
PC=0;SP=32;DONE=41;FAIL=42;STACK=43;GAS=299;DIFF=363;BORROW=427;RESULT=431;CARRY=463
PCCARRY=465;OP=466;IMM=470;FEE=502;HAS=566;KIND=567;FN=573;WIDTH=1285
CACTIVE=0;CPC=1;CFN=33;COP=65;CIMM=69;CFEE=101;CHAS=165;CKIND=166;COUNT=172;CCARRY=197;CWIDTH=270
MSG=51;TYPEPUB=114;CODEPUB=118;RECORD=37

BLOCK=605;BRIF=606;TARGET=607;LABEL=639;HEIGHT=640;LTARGET=649;NONZERO=681;INVERSE=682
CBLOCK=198;CBRIF=199;CTARGET=200
LGET=683;LSET=684;LTEE=685;LOCALS=686;LSEL=814
CLGET=232;CLSET=233;CLTEE=234
HSTACK=818;STYPE=1074;HLOCALS=1082;LTYPE=1210;HIMM=1214;HRESULT=1246;HCARRY=1278
CONST64=1280;ADD64=1281;EQZ64=1282;EQZINV=1283;EQZRESULT=1284
CHIMM=235;CCONST64=267;CADD64=268;CEQZ64=269
OPCODES=(65,106,26,11,2,13,32,33,34,66,124,80)
def tags(op):return [v(op+i) for i in range(4)]+[v(BLOCK if op==OP else CBLOCK),v(BRIF if op==OP else CBRIF)]+[v((LGET if op==OP else CLGET)+i) for i in range(3)]+[v((CONST64 if op==OP else CCONST64)+i) for i in range(3)]

def bits(base,n=16,next=0):return sm(mul(c(2**i),v(base+i,next)) for i in range(n))
def sp(next=0):return sm(mul(c(i),v(SP+i,next)) for i in range(CAP+1))
def word(slot,limb,next=0):return bits((STACK if limb<2 else HSTACK)+32*slot+16*(limb%2),16,next)
def localword(slot,limb,next=0):return bits((LOCALS if limb<2 else HLOCALS)+32*slot+16*(limb%2),16,next)
def immediate(limb):return bits((IMM if limb<2 else HIMM)+16*(limb%2))
def result(limb):return bits((RESULT if limb<2 else HRESULT)+16*(limb%2))
def carry(limb):return v((CARRY if limb<2 else HCARRY)+(limb%2))
def selected_type(depth=1):return sm(mul(v(SP+j),v(STYPE+j-depth)) for j in range(depth,CAP+1))
def fetch(field):
    if field<4:return v(OP+field)
    if field<6:return bits(IMM+16*(field-4))
    return bits(FEE+16*(field-6))
def boundary():return [bits(FN),bits(FN+16),bits(PC),bits(PC+16),sp(),v(DONE),v(FAIL)]+[bits(GAS+16*i) for i in range(4)]+[x for j in range(CAP) for x in [v(STYPE+j)]+[word(j,i) for i in range(4)]]
def descriptor(pc,fn,op,imm,fee,has,kind):
    return [bits(fn),bits(fn+16),bits(pc),bits(pc+16)]+[v(op+i) for i in range(4)]+[bits(imm),bits(imm+16)]+[bits(fee+16*i) for i in range(4)]+[v(has)]+[v(kind+i) for i in range(6)]+[c(0)]*4+[v(BLOCK if op==OP else CBLOCK),v(BRIF if op==OP else CBRIF)]+[bits((TARGET if op==OP else CTARGET)+16*i) for i in range(2)]+[v((LGET if op==OP else CLGET)+i) for i in range(3)]+[bits((HIMM if op==OP else CHIMM)+16*i) for i in range(2)]+[v((CONST64 if op==OP else CCONST64)+i) for i in range(3)]


def exec_table(local_count):
    cs=[]
    def eq(a,b,gate=None):
        residual=sub(a,b);cs.append(residual if gate is None else mul(gate,residual))
    assert type(local_count) is int and 0<=local_count<=4
    for i in list(range(INVERSE))+list(range(LGET,EQZINV))+[EQZRESULT]:eq(mul(v(i),sub(v(i),c(1))),c(0))
    eq(sm(v(SP+i) for i in range(CAP+1)),c(1))
    eq(sm(v(HEIGHT+i) for i in range(CAP+1)),v(LABEL))
    eq(mul(v(FAIL),sub(c(1),v(DONE))),c(0))
    active=sub(c(1),v(DONE));failed=mul(active,v(BORROW+3));success=mul(active,sub(c(1),v(BORROW+3)))
    const32,add32,drop,end,block,brif,get,set_,tee,const64,add64,eqz64=tags(OP)
    const=plus(const32,const64);add=plus(add32,add64)
    eq(sm(tags(OP)),c(1))
    localop=plus(get,plus(set_,tee))
    eq(sm(v(LSEL+i) for i in range(4)),localop)
    eq(mul(localop,bits(IMM)),sm(mul(c(i),v(LSEL+i)) for i in range(4)))
    eq(mul(localop,bits(IMM+16)),c(0))
    for i in range(local_count,4):eq(v(LSEL+i),c(0))
    for i in range(4):
      eq(v(LTYPE+i),['p',TYPEPUB+i])
      if i>=local_count:eq(v(LTYPE+i),c(0))
    for base in (LOCALS,HLOCALS):
      for i in range(128):eq(v(base+i),c(0),['first'])
      for i in range(local_count*32,128):eq(v(base+i),c(0))
    for slot in range(4):
      for limb in (2,3):eq(mul(sub(c(1),v(LTYPE+slot)),localword(slot,limb)),c(0))
    # Type checks are execution-gated; padding/exhaustion does not pop operands.
    topType=selected_type();secondType=selected_type(2)
    selectedLocalType=sm(mul(v(LSEL+i),v(LTYPE+i)) for i in range(4))
    eq(topType,selectedLocalType,mul(success,plus(set_,tee)))
    eq(topType,c(0),mul(success,plus(add32,brif)))
    eq(secondType,c(0),mul(success,add32))
    eq(topType,c(1),mul(success,plus(add64,eqz64)))
    eq(secondType,c(1),mul(success,add64))
    eqzSum=sm(sm(mul(v(SP+j),word(j-1,i)) for j in range(1,CAP+1)) for i in range(4))
    eq(mul(eqzSum,v(EQZINV)),sub(c(1),v(EQZRESULT)))
    eq(mul(eqzSum,v(EQZRESULT)),c(0))
    for slot in range(4):
      writeLocal=mul(success,mul(plus(set_,tee),v(LSEL+slot)))
      for limb in range(4):
        oldLocal=localword(slot,limb)
        top=sm(mul(v(SP+j),word(j-1,limb)) for j in range(1,CAP+1))
        eq(localword(slot,limb,1),
           plus(mul(sub(c(1),writeLocal),oldLocal),mul(writeLocal,top)),['trans'])
    height=sm(mul(c(i),v(HEIGHT+i)) for i in range(CAP+1))
    # Exact nonzero of the selected i32 condition: bit sum is in [0,32].
    q=sm(mul(v(SP+j),sm(v(STACK+32*(j-1)+bit) for bit in range(32))) for j in range(1,CAP+1))
    eq(mul(q,v(INVERSE)),v(NONZERO));eq(mul(q,sub(c(1),v(NONZERO))),c(0))
    taken=mul(success,mul(brif,v(NONZERO)))
    stop=plus(failed,mul(success,mul(end,sub(c(1),v(LABEL)))))
    sequential=mul(success,sub(c(1),plus(mul(end,sub(c(1),v(LABEL))),mul(brif,v(NONZERO)))))
    for i in range(32):eq(v(PC+i),c(0),['first'])
    eq(v(SP),c(1),['first']);eq(v(DONE),c(0),['first']);eq(v(LABEL),c(0),['first'])
    eq(v(DONE),c(1),['last'])
    for i in range(4):
        borrow=c(0) if i==0 else v(BORROW+i-1)
        eq(sub(sub(bits(GAS+16*i),fetch(6+i)),borrow),sub(bits(DIFF+16*i),mul(c(65536),v(BORROW+i))))
    trans=['trans']
    eq(v(DONE,1),plus(v(DONE),stop),trans);eq(v(FAIL,1),plus(v(FAIL),failed),trans)
    # Jump uses the saved authenticated target; otherwise bounded PC increment.
    normal=mul(trans,sub(c(1),taken))
    eq(plus(bits(PC),sequential),plus(bits(PC,16,1),mul(c(65536),v(PCCARRY))),normal)
    eq(bits(PC+16,16,1),plus(bits(PC+16),v(PCCARRY)),normal)
    for limb in range(2):eq(bits(PC+16*limb,16,1),bits(LTARGET+16*limb),mul(trans,taken))
    for i in range(32):eq(v(FN+i),c(0))
    delta=mul(success,sub(plus(const,get),plus(plus(plus(add,drop),brif),set_)))
    eq(sp(1),plus(mul(taken,height),mul(sub(c(1),taken),plus(sp(),delta))),trans)
    eq(mul(success,mul(plus(const,get),v(SP+CAP))),c(0))
    eq(mul(success,mul(add,plus(v(SP),v(SP+1)))),c(0))
    eq(mul(success,mul(plus(plus(plus(drop,brif),plus(set_,tee)),eqz64),v(SP))),c(0))
    eq(mul(success,mul(end,sub(sp(),height))),c(0))
    eq(mul(success,mul(block,v(LABEL))),c(0))
    eq(mul(success,mul(brif,sub(c(1),v(LABEL)))),c(0))
    # Label pop on taken branch or nested end; retain through failure/padding.
    opened=mul(success,block);closed=plus(taken,mul(success,mul(end,v(LABEL))))
    keep=sub(c(1),plus(opened,closed))
    eq(v(LABEL,1),plus(opened,mul(keep,v(LABEL))),trans)
    for i in range(CAP+1):eq(v(HEIGHT+i,1),plus(mul(opened,v(SP+i)),mul(keep,v(HEIGHT+i))),trans)
    for limb in range(2):
        eq(bits(LTARGET+16*limb,16,1),plus(mul(opened,bits(TARGET+16*limb)),mul(keep,bits(LTARGET+16*limb))),trans)
        eq(bits(LTARGET+16*limb),c(0),sub(c(1),v(LABEL)))
    # Saved block height cannot exceed current SP, or SP after popping condition.
    for h in range(CAP+1):
      for j in range(h):eq(mul(v(HEIGHT+h),v(SP+j)),c(0))
      eq(mul(success,mul(brif,mul(v(HEIGHT+h),v(SP+h)))),c(0))
    for i in range(4):eq(bits(GAS+16*i,16,1),plus(mul(success,bits(DIFF+16*i)),mul(sub(c(1),success),bits(GAS+16*i))),trans)
    for limb in range(4):
        left=sm(mul(v(SP+j),word(j-2,limb)) for j in range(2,CAP+1))
        right=sm(mul(v(SP+j),word(j-1,limb)) for j in range(2,CAP+1))
        eq(plus(plus(left,right),c(0) if limb==0 else carry(limb-1)),plus(result(limb),mul(c(65536),carry(limb))),mul(success,add if limb<2 else add64))
        if limb>=2:eq(result(limb),c(0),mul(success,add32))
    for slot in range(CAP):
        live=sm(v(SP+j) for j in range(slot+1,CAP+1))
        below=sm(v(HEIGHT+h) for h in range(slot+1,CAP+1))
        push=mul(success,mul(plus(const,get),v(SP+slot)))
        write=mul(success,mul(add,v(SP+slot+2) if slot+2<=CAP else c(0)))
        clear=mul(success,mul(plus(plus(plus(add,drop),brif),set_),v(SP+slot+1)))
        zero=mul(success,mul(eqz64,v(SP+slot+1)))
        retain=sub(c(1),plus(plus(plus(push,write),clear),zero))
        for limb in range(4):
            old=word(slot,limb)
            eq(mul(sub(c(1),live),old),c(0))
            if limb>=2:eq(mul(sub(c(1),v(STYPE+slot)),old),c(0))
            pushed=plus(mul(const,immediate(limb)),mul(get,sm(mul(v(LSEL+j),localword(j,limb)) for j in range(4))))
            linear=plus(mul(retain,old),plus(plus(mul(push,pushed),mul(write,result(limb))),mul(zero,v(EQZRESULT) if limb==0 else c(0))))
            eq(word(slot,limb,1),plus(mul(taken,mul(below,old)),mul(sub(c(1),taken),linear)),trans)
        eq(mul(sub(c(1),live),v(STYPE+slot)),c(0))
        pushedType=plus(const64,mul(get,selectedLocalType))
        nextType=plus(mul(retain,v(STYPE+slot)),plus(mul(push,pushedType),mul(write,add64)))
        eq(v(STYPE+slot,1),plus(mul(taken,mul(below,v(STYPE+slot))),mul(sub(c(1),taken),nextType)),trans)
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
    eq(sm(tags(COP)),v(CACTIVE))
    eq(sm(v(CKIND+i) for i in range(6)),v(CHAS))
    eq(v(CKIND+5),c(0)) # linear charging is outside this slice
    eq(mul(v(CHAS),sub(c(1),v(CACTIVE))),c(0))
    for i in range(4):eq(bits(CFEE+16*i),c(0),sub(c(1),v(CHAS)))
    for i in range(2):eq(bits(CIMM+16*i),c(0),sub(c(1),plus(plus(v(COP),v(CCONST64)),sm(v(CLGET+j) for j in range(3)))) )
    for i in range(2):eq(bits(CHIMM+16*i),c(0),sub(c(1),v(CCONST64)))
    for i in range(2):eq(bits(CTARGET+16*i),c(0),sub(c(1),v(CBLOCK)))
    msg=descriptor(CPC,CFN,COP,CIMM,CFEE,CHAS,CKIND)
    return dict(width=CWIDTH,maxLog=22,constraints=cs,interactions=[
      dict(bus=2,msg=msg,mult=[v(COUNT+i) for i in range(25)],send=False),
      dict(bus=3,msg=msg,mult=[v(CACTIVE)],send=True)])

def air(code_length,local_count):
    numpub=CODEPUB+RECORD*code_length
    return dict(format='np-air-v2',numPub=numpub,maxPub=numpub,numBuses=4,
      pubSegs=[dict(bus=i,countAt=4*i,indexBase=None,prefix=[],send=False,start=12+i*MSG,startAt=None,width=MSG) for i in range(2)]+[
        dict(bus=3,countAt=8,indexBase=None,prefix=[],send=False,start=CODEPUB,startAt=None,width=RECORD)],
      tables=[exec_table(local_count),code_table()])

def put_descriptor(row,entry,pc,fn,op,imm,fee,has,kind):
    assert entry['function']==0 and 0<=entry['pc']<2**32
    opcode=entry['instruction']['opcode'];assert opcode in OPCODES
    immediate=entry['instruction']['immediate'];assert 0<=immediate<(2**64 if opcode==66 else 2**32)
    assert opcode in (65,66,32,33,34) or immediate==0
    putbits(row,pc,entry['pc'],32);putbits(row,fn,entry['function'],32)
    tag=OPCODES.index(opcode)
    row[op+tag if tag<4 else ((BLOCK if op==OP else CBLOCK)+(tag-4)) if tag<6 else ((LGET if op==OP else CLGET)+(tag-6)) if tag<9 else ((CONST64 if op==OP else CCONST64)+(tag-9))]=1
    putbits(row,TARGET if op==OP else CTARGET,entry.get('end_target',0),32);putbits(row,imm,immediate%(2**32),32);putbits(row,HIMM if op==OP else CHIMM,immediate>>32,32)
    charge=entry['charge']
    if charge is not None:
      assert charge['linear']==0 and not charge['linear_kind'] and 0<=charge['kind']<5
      row[has]=1;row[kind+charge['kind']]=1;putbits(row,fee,charge['constant'],64)

def row_at(code,pc,stack,g,done,failed,labels=None,locals_=None):
    assert 0<=pc<len(code)<2**32 and len(stack)<=CAP
    row=[0]*WIDTH;put_descriptor(row,code[pc],PC,FN,OP,IMM,FEE,HAS,KIND)
    locals_=[] if locals_ is None else locals_
    assert len(locals_)<=4
    for i,(tag,value) in enumerate(locals_):
      row[LTYPE+i]=tag;putbits(row,LOCALS+32*i,value%(2**32),32);putbits(row,HLOCALS+32*i,value>>32,32)
    if code[pc]['instruction']['opcode'] in (32,33,34):
      index=code[pc]['instruction']['immediate'];assert index<len(locals_)
      row[LSEL+index]=1
    row[SP+len(stack)]=1;row[DONE]=int(done);row[FAIL]=int(failed)
    for i,(tag,value) in enumerate(stack):
      row[STYPE+i]=tag;putbits(row,STACK+32*i,value%(2**32),32);putbits(row,HSTACK+32*i,value>>32,32)
    putbits(row,GAS,g,64)
    fee=0 if code[pc]['charge'] is None else code[pc]['charge']['constant']
    putbits(row,DIFF,(g-fee)%2**64,64)
    borrow=0
    for i in range(4):
      borrow=int(((g>>(16*i))&65535)-((fee>>(16*i))&65535)-borrow<0);row[BORROW+i]=borrow
    labels=[] if labels is None else labels
    assert len(labels)<=2
    if len(labels)==2:
      target,arity,height,isloop=labels[0]
      assert arity==0 and isloop==0 and height<=len(stack)<=CAP
      row[LABEL]=1;row[HEIGHT+height]=1;putbits(row,LTARGET,target,32)
    q=0 if not stack else (stack[-1][1]%(2**32)).bit_count()
    row[NONZERO]=int(q!=0);row[INVERSE]=pow(q,P-2,P) if q else 0
    opcode=code[pc]['instruction']['opcode']
    advance=not done and g>=fee and not (opcode==11 and not row[LABEL]) and not (opcode==13 and row[NONZERO])
    row[PCCARRY]=int(advance and pc%65536==65535)
    q64=0 if not stack else sum((stack[-1][1]>>(16*i))&65535 for i in range(4))
    row[EQZRESULT]=int(q64==0);row[EQZINV]=pow(q64,P-2,P) if q64 else 0
    if opcode in (106,124) and len(stack)>=2:
      a,b=[x[1] for x in stack[-2:]];out=(a+b)%(2**(64 if opcode==124 else 32))
      putbits(row,RESULT,out%(2**32),32);putbits(row,HRESULT,out>>32,32)
      carry=0
      for i in range(4 if opcode==124 else 2):
        carry=int(((a>>(16*i))&65535)+((b>>(16*i))&65535)+carry>=65536)
        row[(CARRY if i<2 else HCARRY)+(i%2)]=carry
    return row

def pad(rows):
    n=max(1,(len(rows)-1).bit_length());return n,rows+[rows[-1][:] for _ in range(2**n-len(rows))]
def nat4(n):
    assert 0<=n<2**32
    return [(n>>(8*i))&255 for i in range(4)]
def typed_value(x):
    tag=x['tag'];assert tag in (0,1)
    limbs=x['limbs'];assert len(limbs) in (2,4) and (tag==0 or len(limbs)==4)
    assert all(type(i) is int and 0<=i<65536 for i in limbs)
    value=sum(i<<(16*j) for j,i in enumerate(limbs));assert value<2**(64 if tag else 32)
    return tag,value

def make(case):
    local_count=case.get('local_count',len(case['entry_after']['frames'][0]['locals']))
    assert 0<=local_count<=4 and len(case['entry_after']['frames'][0]['locals'])==local_count
    assert all(typed_value(v)[1]==0 for v in case['entry_after']['frames'][0]['locals'])
    local_types=case.get('local_types',[0]*local_count)
    assert [typed_value(v)[0] for v in case['entry_after']['frames'][0]['locals']]==local_types
    code=case['code'];assert code and len(code)<2**32
    assert case['prepaid']<=10**15 and case['entry_after']['gas']['promises']==0
    assert all(e['pc']==i and e['function']==0 for i,e in enumerate(code))
    rows=[]
    for event in case['exec_rows']:
      before=event['before'];assert len(before['frames'])==1 and before['frames'][0]['fn']==0
      rows.append(row_at(code,event['pc'],[typed_value(v) for v in before['stack']],before['gas']['g'],False,False,before['frames'][0]['labels'],[typed_value(v) for v in before['frames'][0]['locals']]))
    last=case['exec_rows'][-1];after=last['after'];failed=last['status']=='abort'
    assert last['status'] in ('finish','abort')
    rows.append(row_at(code,last['pc'],[typed_value(v) for v in after['stack']],after['gas']['g'],True,failed,last['before']['frames'][0]['labels'],[typed_value(v) for v in last['before']['frames'][0]['locals']]))
    en,rows=pad(rows)
    counts=Counter(sum(row[PC+i]<<i for i in range(32)) for row in rows)
    code_rows=[]
    for i,entry in enumerate(code):
      row=[0]*CWIDTH;row[CACTIVE]=1;put_descriptor(row,entry,CPC,CFN,COP,CIMM,CFEE,CHAS,CKIND)
      putbits(row,COUNT,counts[i],25);row[CCARRY]=int(i%65536==65535 and i+1<len(code));code_rows.append(row)
    cn=max(1,(len(code_rows)-1).bit_length());code_rows += [[0]*CWIDTH for _ in range(2**cn-len(code_rows))]
    def evs(exprs,row):return [eval_expr(e,row,row,[],False,False) for e in exprs]
    public=nat4(1)+nat4(1)+nat4(len(code))+evs(boundary(),rows[0])+evs(boundary(),rows[-1])
    public += local_types+[0]*(4-local_count)
    public += [x for row in code_rows[:len(code)] for x in evs(descriptor(CPC,CFN,COP,CIMM,CFEE,CHAS,CKIND),row)]
    return dict(air=air(len(code),local_count),public=public,log_rows=[en,cn]),[rows,code_rows]
