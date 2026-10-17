"""Bounded prepared-function diagnostic AIR, not a proved Wasm/PREP refinement.

Fixed 16-instruction/8-i32-stack machine, constant prepared range fees, no hosts.
CODE is public input checked against the Lean fixture outside AIR. Canonical
np-air-v2 expressions and two actual public execution boundary buses.
"""
import copy,json,argparse
P=2013265921
CAP=8;CODE=16
# columns: PC onehot16, SP onehot9, done/fail, stack8*32 bits,
# gas64bits, subtraction result64bits, borrow4, add result32bits, carry2.
PC=0;SP=16;DONE=25;FAIL=26;STACK=27;GAS=283;DIFF=347;BORROW=411;RESULT=415;CARRY=447;WIDTH=449
MSG=24;CODEPUB=8+2*MSG

def c(n):return ['c',n%P]
def v(i,n=0):return ['v',i,n]
def p(i):return ['p',i]
def plus(a,b):return ['+',a,b]
def neg(a):return ['-',a]
def sub(a,b):return plus(a,neg(b))
def mul(a,b):return ['*',a,b]
def sm(xs):
    xs=list(xs)
    if not xs:return c(0)
    while len(xs)>1:xs=[plus(xs[i],xs[i+1]) if i+1<len(xs) else xs[i] for i in range(0,len(xs),2)]
    return xs[0]
def bits(base,n=16,next=0):return sm(mul(c(2**i),v(base+i,next)) for i in range(n))
def pc(next=0):return sm(mul(c(i),v(PC+i,next)) for i in range(CODE))
def sp(next=0):return sm(mul(c(i),v(SP+i,next)) for i in range(CAP+1))
def word(slot,limb,next=0):return bits(STACK+32*slot+16*limb,16,next)
def fetch(field):return sm(mul(v(PC+i),p(CODEPUB+10*i+field)) for i in range(CODE))
def boundary():return [pc(),sp(),v(DONE),v(FAIL)]+[bits(GAS+16*i) for i in range(4)]+[word(j,i) for j in range(CAP) for i in range(2)]
def air():
    cs=[]
    def eq(a,b,gate=None):
        residual=sub(a,b);cs.append(residual if gate is None else mul(gate,residual))
    for i in range(WIDTH):eq(mul(v(i),sub(v(i),c(1))),c(0))
    eq(sm(v(PC+i) for i in range(CODE)),c(1));eq(sm(v(SP+i) for i in range(CAP+1)),c(1))
    # done/fail flags are monotone; failed implies done.
    eq(mul(v(FAIL),sub(c(1),v(DONE))),c(0))
    active=sub(c(1),v(DONE));failed=mul(active,v(BORROW+3));success=mul(active,sub(c(1),v(BORROW+3)))
    ops=[fetch(i) for i in range(4)];const,add,drop,end=ops
    eq(sm(ops),c(1))
    eq(v(PC),c(1),['first']);eq(v(SP),c(1),['first']);eq(v(DONE),c(0),['first'])
    eq(v(DONE),c(1),['last'])
    # Four limb bounded subtraction; terminal borrow is exact fee>gas test.
    for i in range(4):
        borrow=c(0) if i==0 else v(BORROW+i-1)
        eq(sub(sub(bits(GAS+16*i),fetch(6+i)),borrow),sub(bits(DIFF+16*i),mul(c(65536),v(BORROW+i))))
    stop=plus(failed,mul(success,end));advance=mul(success,sub(c(1),end))
    trans=['trans']
    eq(v(DONE,1),plus(v(DONE),stop),trans);eq(v(FAIL,1),plus(v(FAIL),failed),trans)
    for i in range(CODE):eq(v(PC+i,1),plus(mul(sub(c(1),advance),v(PC+i)),mul(advance,c(0) if i==0 else v(PC+i-1))),trans)
    eq(mul(advance,v(PC+CODE-1)),c(0))
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
    msg=boundary()
    return dict(format='np-air-v2',numPub=CODEPUB+10*CODE,maxPub=CODEPUB+10*CODE,numBuses=2,
      pubSegs=[dict(bus=i,countAt=4*i,indexBase=None,prefix=[],send=False,start=8+i*MSG,startAt=None,width=MSG) for i in range(2)],
      tables=[dict(width=WIDTH,maxLog=5,constraints=cs,interactions=[dict(bus=i,msg=msg,mult=[[flag]],send=True) for i,flag in enumerate(('first','last'))])])

def putbits(row,base,value,n):
    assert 0<=value<2**n
    row[base:base+n]=[(value>>i)&1 for i in range(n)]
def val(value):
    assert value['tag']==0 and len(value['limbs'])==2 and all(0<=x<65536 for x in value['limbs'])
    return value['limbs'][0]+65536*value['limbs'][1]
def row_at(code,pc,stack,g,done,failed):
    assert 0<=pc<len(code)<=CODE and len(stack)<=CAP
    row=[0]*WIDTH;row[PC+pc]=1;row[SP+len(stack)]=1;row[DONE]=int(done);row[FAIL]=int(failed)
    for i,value in enumerate(stack):putbits(row,STACK+32*i,value,32)
    putbits(row,GAS,g,64)
    fee=0 if code[pc]['charge'] is None else code[pc]['charge']['constant']
    putbits(row,DIFF,(g-fee)%2**64,64)
    borrow=0
    for i in range(4):
        d=((g>>(16*i))&65535)-((fee>>(16*i))&65535)-borrow
        borrow=int(d<0);row[BORROW+i]=borrow
    if code[pc]['instruction']['opcode']==106 and len(stack)>=2:
        a,b=stack[-2:];putbits(row,RESULT,(a+b)%2**32,32)
        row[CARRY]=int((a&65535)+(b&65535)>=65536);row[CARRY+1]=int(a+b>=2**32)
    return row

def eval_expr(e,row,nxt,public,first,last):
    op=e[0]
    if op=='c':return e[1]%P
    if op=='p':return public[e[1]] if e[1]<len(public) else 0
    if op=='v':return (nxt if e[2] else row)[e[1]]
    if op=='first':return int(first)
    if op=='last':return int(last)
    if op=='trans':return int(not last)
    if op=='-':return -eval_expr(e[1],row,nxt,public,first,last)%P
    a=eval_expr(e[1],row,nxt,public,first,last);b=eval_expr(e[2],row,nxt,public,first,last)
    return (a+b if op=='+' else a*b)%P

def make(case):
    code=case['code'];assert 0<len(code)<=CODE
    assert case['prepaid']<=10**15 and case['entry_after']['gas']['promises']==0
    descriptors=[]
    for i,entry in enumerate(code):
        assert entry['pc']==i and entry['function']==0
        op=entry['instruction']['opcode'];assert op in (65,106,26,11)
        imm=entry['instruction']['immediate'];assert 0<=imm<2**32
        fee=entry['charge'];assert fee is None or (fee['linear']==0 and not fee['linear_kind'] and 0<=fee['constant']<2**64)
        f=0 if fee is None else fee['constant']
        descriptors += [int(op==x) for x in (65,106,26,11)]+[imm%65536,imm//65536]+[(f>>(16*j))&65535 for j in range(4)]
    descriptors += ([0,0,0,1,0,0,0,0,0,0]*(CODE-len(code)))
    rows=[]
    for event in case['exec_rows']:
        before=event['before'];assert len(before['frames'])==1 and before['frames'][0]['fn']==0
        rows.append(row_at(code,event['pc'],[val(v) for v in before['stack']],before['gas']['g'],False,False))
    last=case['exec_rows'][-1];after=last['after'];failed=last['status']=='abort'
    assert last['status'] in ('finish','abort')
    rows.append(row_at(code,last['pc'],[val(v) for v in after['stack']],after['gas']['g'],True,failed))
    n=max(1,(len(rows)-1).bit_length());assert n<=5
    rows += [rows[-1][:] for _ in range(2**n-len(rows))]
    def message(row):return [eval_expr(e,row,row,[],False,False) for e in boundary()]
    public=[1,0,0,0,1,0,0,0]+message(rows[0])+message(rows[-1])+descriptors
    # Diagnostic boundary checks; these are NOT a proved PREP/runCall bridge.
    assert rows[0][PC]==1 and rows[0][SP]==1
    final_g=after['gas']['g'];expected_burnt=case['prepaid'] if failed else case['prepaid']-final_g
    assert case['final']['gas']['burnt']==expected_burnt
    return dict(air=air(),public=public,log_rows=[n]),rows

def check(spec,rows):
    for i,row in enumerate(rows):
        for j,e in enumerate(spec['air']['tables'][0]['constraints']):
            if eval_expr(e,row,rows[(i+1)%len(rows)],spec['public'],i==0,i+1==len(rows)):
                return False,(i,j)
    for t,row in enumerate((rows[0],rows[-1])):
        msg=[eval_expr(e,row,row,spec['public'],t==0,t==1) for e in boundary()]
        if msg!=spec['public'][8+t*MSG:8+(t+1)*MSG]:return False,('boundary',t)
    return True,None

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('fixture');ap.add_argument('out');args=ap.parse_args()
    from pathlib import Path
    out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    report=[]
    for case in json.load(open(args.fixture))['cases']:
        spec,rows=make(case);assert check(spec,rows)[0],check(spec,rows)
        name=case['label'];(out/(name+'-spec.json')).write_text(json.dumps(spec));(out/(name+'-rows.json')).write_text(json.dumps({'rows':rows}))
        report.append(dict(label=name,rows=len(rows),width=WIDTH,constraints=len(spec['air']['tables'][0]['constraints'])))
    print(json.dumps(dict(status='PASS',cases=report,limitation='diagnostic AIR; PREP and whole-machine refinement remain open')))
