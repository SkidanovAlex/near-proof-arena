"""Validate concrete program→terminal DAG rebuilding certificates.
Finite structural checks correspond to the Lean routes, not kernel proofs of captures.
"""
import argparse,copy,hashlib,json,sys,time
from pathlib import Path
from check_terminal_dag_certificates import require,replay

def arithmetic(nodes,kind,x,y,z):
    require(all(type(i)is int and 0<=i<len(nodes) for i in (x,y,z)),'arithmetic index')
    a,b,c=nodes[x],nodes[y],nodes[z]
    if tuple(c)==(kind,x,y):return 'direct'
    if a[0]==b[0]=='const' and tuple(c)==('const',*OPS[kind](a[1:],b[1:])):return 'constant'
    az=a==('const',*ZERO);bz=b==('const',*ZERO);ao=a==('const',*ONE);bo=b==('const',*ONE)
    if kind=='add' and az and z==y:return 'add-zero-left'
    if kind=='add' and bz and z==x:return 'add-zero-right'
    if kind=='sub' and bz and z==x:return 'sub-zero-right'
    if kind=='sub' and x==y and c==('const',*ZERO):return 'sub-same'
    if kind=='mul' and az and z==x:return 'mul-zero-left'
    if kind=='mul' and bz and z==y:return 'mul-zero-right'
    if kind=='mul' and ao and z==y:return 'mul-one-left'
    if kind=='mul' and bo and z==x:return 'mul-one-right'
    raise ValueError('invalid arithmetic route')

class Generator:
    def __init__(self,circuit):
        self.nodes=[tuple(n) for n in circuit['nodes']];self.lookup={n:i for i,n in enumerate(self.nodes)}
        self.zero=self.const(ZERO);self.one=self.const(ONE)
    def const(self,value):return self.lookup[('const',*value)]
    def op(self,kind,x,y):
        a,b=self.nodes[x],self.nodes[y]
        if a[0]==b[0]=='const':return self.const(OPS[kind](a[1:],b[1:]))
        if kind=='add':
            if x==self.zero:return y
            if y==self.zero:return x
        if kind=='sub':
            if y==self.zero:return x
            if x==y:return self.zero
        if kind=='mul':
            if x==self.zero or y==self.zero:return self.zero
            if x==self.one:return y
            if y==self.one:return x
        return self.lookup[(kind,x,y)]
    def balance(self,terms):
        stages=[terms]
        while len(terms)>1:
            nxt=[]
            for i in range(0,len(terms),2):
                if i+1==len(terms):nxt.append(terms[i]);continue
                (x,s),(y,t)=terms[i:i+2]
                if s==t:nxt.append((self.op('add',x,y),s))
                elif s:nxt.append((self.op('sub',x,y),True))
                else:nxt.append((self.op('sub',y,x),True))
            terms=nxt;stages.append(terms)
        result=self.zero if not terms else terms[0][0] if terms[0][1] else self.op('sub',self.zero,terms[0][0])
        return dict(stages=stages,result=result)
    def program(self,instructions,base,W,sels):
        uses=[0]*len(instructions)
        for code,x,y,*c in instructions:
            if code in (6,7,8):uses[x]+=1;uses[y]+=1
        records={}
        def rebuild(i):
            if i in records:return records[i]['node']
            code,x,y,*c=instructions[i];record={}
            if code==0:node=self.const(c)
            elif code in (1,2):node=self.lookup[('input',base+x+(W if code==2 else 0))]
            elif code in (3,4,5):node=self.const(sels[{3:'first',4:'last',5:'trans'}[code]])
            elif code==8:
                left,right=rebuild(x),rebuild(y);node=self.op('mul',left,right)
            elif code in (6,7):
                leaves=[]
                def collect(k,sign,root=False):
                    op,a,b,*_=instructions[k]
                    if op in (6,7) and (root or uses[k]==1):
                        return ['branch',k,sign,collect(a,sign),collect(b,sign if op==6 else not sign)]
                    leaves.append((k,sign));rebuild(k);return ['leaf',k,sign]
                tree=collect(i,True,True)
                balance=self.balance([(records[k]['node'],s) for k,s in leaves]);node=balance['result']
                record.update(tree=tree,balance=balance)
            else:raise ValueError('program opcode')
            record['node']=node;records[i]=record;return node
        root=rebuild(len(instructions)-1)
        return dict(instructions=instructions,base=base,column_capacity=W,selectors=sels,records=records,root=root)

class Checker:
    def __init__(self,circuit):
        self.nodes=[tuple(n) for n in circuit['nodes']];self.counts={}
    def index(self,i):
        require(type(i) is int and 0<=i<len(self.nodes),'finite node index')
        return i
    def op(self,kind,x,y,z):
        label=arithmetic(self.nodes,kind,x,y,z);self.counts[label]=self.counts.get(label,0)+1
    def balance(self,cert,expected):
        stages=[[(self.index(x),s) for x,s in st] for st in cert['stages']]
        require(all(type(sign) is bool for stage in stages for _,sign in stage),'balance sign')
        require(stages and stages[0]==expected,'balance initial terms')
        for old,new in zip(stages,stages[1:]):
            require(len(old)>1 and len(new)==(len(old)+1)//2,'balance pass shape')
            for k,(z,u) in enumerate(new):
                x,s=old[2*k];require(type(u)is bool and type(s)is bool,'balance sign')
                if 2*k+1==len(old):require((z,u)==(x,s),'odd carry');continue
                y,t=old[2*k+1];require(type(t)is bool,'balance sign')
                if s==t:require(u==s,'same sign');self.op('add',x,y,z)
                elif s:require(u is True,'positive subtraction');self.op('sub',x,y,z)
                else:require(u is True,'negative subtraction');self.op('sub',y,x,z)
        require(len(stages[-1])<=1,'unfinished balance');result=self.index(cert['result'])
        if not stages[-1]:require(self.nodes[result]==('const',*ZERO),'empty balance')
        else:
            x,s=stages[-1][0]
            if s:require(result==x,'positive singleton')
            else:
                zeros=[i for i,n in enumerate(self.nodes) if n==('const',*ZERO)]
                require(zeros,'zero missing');self.op('sub',zeros[0],x,result)
        return result
    def program(self,cert,expected_instructions,base,W,sels):
        require(cert['instructions']==expected_instructions and cert['base']==base and cert['column_capacity']==W,'program/placement binding')
        require({k:tuple(v) for k,v in cert['selectors'].items()}=={k:tuple(v) for k,v in sels.items()},'selector binding')
        ins=cert['instructions'];records={int(i):r for i,r in cert['records'].items()};done=set();active=set()
        for i,(op,x,y,*c) in enumerate(ins):
            require(0<=op<=8 and len(c)==4,'seven word opcode')
            if op>=6:require(0<=x<i and 0<=y<i,'program acyclicity')
        def expansion(tree,i,sign):
            require(tree[1:3]==[i,sign] and type(tree[2])is bool,'expansion identity/sign')
            if tree[0]=='leaf':require(len(tree)==3,'leaf shape');return [(i,sign)]
            require(tree[0]=='branch' and len(tree)==5,'branch shape');op,x,y,*_=ins[i]
            require(op in (6,7),'expand non additive')
            return expansion(tree[3],x,sign)+expansion(tree[4],y,sign if op==6 else not sign)
        def register(i):
            require(0<=i<len(ins) and i in records,'missing register certificate')
            if i in done:return records[i]['node']
            require(i not in active,'recursive certificate');active.add(i)
            record=records[i];z=record['node'];require(type(z)is int and 0<=z<len(self.nodes),'rebuilt node index')
            op,x,y,*c=ins[i]
            if op==0:require(self.nodes[z]==('const',*c),'constant binding')
            elif op in (1,2):require(0<=x<W and self.nodes[z]==('input',base+x+(W if op==2 else 0)),'current/next binding')
            elif op in (3,4,5):require(self.nodes[z]==('const',*sels[{3:'first',4:'last',5:'trans'}[op]]),'selector constant')
            elif op==8:self.op('mul',register(x),register(y),z)
            else:
                leaves=expansion(record['tree'],i,True)
                mapped=[(register(j),sign) for j,sign in leaves]
                require(self.balance(record['balance'],mapped)==z,'balance result')
            active.remove(i);done.add(i);return z
        require(register(len(ins)-1)==cert['root'],'program root')
        require(set(records)==done,'unreachable certificate records')
        return cert['root'],len(done)

def capture(path, *, input_log=None):
    import pq384_gkr_bus as old,pq384_seed_gkr_bus as seed
    args=[];original=old.compile_terminal
    def tracked(*a):args.append(a);return original(*a)
    a,b=old.compile_terminal,seed.compile_terminal;old.compile_terminal=tracked;seed.compile_terminal=tracked
    try:circuit,layout,profile=replay(path,input_log=input_log)
    finally:old.compile_terminal=a;seed.compile_terminal=b
    require(len(args)==(1 if input_log is None else 2),'compiler capture')
    require(all(a==args[-1] for a in args),'compiler replay arguments changed')
    return circuit,profile,args[-1]

def produce(circuit,args):
    spec,alpha,gamma,finals,terminals,rho=args;gen=Generator(circuit);programs=[];outputs=[];blocks={b['table']:b for b in circuit['input_blocks']}
    for ti,(table,term) in enumerate(zip(spec['air']['tables'],terminals)):
        raw=compile_weighted(table,spec['public'],alpha,gamma,[tuple(x) for x in finals[ti]],term['mixing'],bus)
        ins=[list(raw[i:i+7]) for i in range(0,len(raw),7)];block=blocks[ti]
        cert=gen.program(ins,block['offset'],block['column_capacity'],selectors(term['point']));programs.append(cert)
        weight=gen.const(eq_point(term['tau'],term['point']));node=gen.op('mul',cert['root'],weight);outputs.append(dict(node=node,weight=weight,claim=gen.const(term['claim'])))
    terms=[];power=ONE
    for output in outputs:
        p=gen.const(power);delta=gen.op('sub',output['node'],output['claim']);node=gen.op('mul',p,delta)
        terms.append((node,True));output.update(power=p,delta=delta,batch_node=node);power=mul(power,rho)
    balance=gen.balance(terms);root=balance['result']
    if gen.nodes[root][0] in ('const','input'):root=gen.lookup[('add',root,gen.zero)]
    require(root==circuit['root'],'compiler root reproduced')
    return dict(programs=programs,outputs=outputs,balance=balance,root=root)

def validate(circuit,args,cert):
    spec,alpha,gamma,finals,terminals,rho=args;checker=Checker(circuit);checker.index(cert['root']);blocks={b['table']:b for b in circuit['input_blocks']};records=0;power=ONE;terms=[]
    require(len(cert['programs'])==len(cert['outputs'])==len(terminals),'table count')
    for ti,(table,term,program,output) in enumerate(zip(spec['air']['tables'],terminals,cert['programs'],cert['outputs'])):
        for key in ('weight','claim','power','node','delta','batch_node'):checker.index(output[key])
        raw=compile_weighted(table,spec['public'],alpha,gamma,[tuple(x) for x in finals[ti]],term['mixing'],bus)
        ins=[list(raw[i:i+7]) for i in range(0,len(raw),7)];b=blocks[ti]
        root,n=checker.program(program,ins,b['offset'],b['column_capacity'],selectors(term['point']));records+=n
        require(checker.nodes[output['weight']]==('const',*eq_point(term['tau'],term['point'])),'terminal equality weight')
        require(checker.nodes[output['claim']]==('const',*term['claim']),'terminal claim')
        require(checker.nodes[output['power']]==('const',*power),'rho power')
        checker.op('mul',root,output['weight'],output['node']);checker.op('sub',output['node'],output['claim'],output['delta']);checker.op('mul',output['power'],output['delta'],output['batch_node'])
        terms.append((output['batch_node'],True));power=mul(power,rho)
    root=checker.balance(cert['balance'],terms)
    if checker.nodes[root][0] in ('const','input'):require(checker.nodes[cert['root']]==('add',root,Generator(circuit).zero),'forced final layer')
    else:require(cert['root']==root,'final root')
    require(cert['root']==circuit['root'],'bound circuit root')
    return dict(registers=records,arithmetic=checker.counts)

def shortcut_tests():
    def c(n):return ('const',n,0,0,0)
    nodes=[c(0),c(1),('input',0),('input',1),c(2),c(3),c(5),c(17)]
    cases=[]
    for op in OPS:
        nodes.append((op,2,3));cases.append((op,2,3,len(nodes)-1,'direct'))
        result=OPS[op]((2,0,0,0),(3,0,0,0));nodes.append(('const',*result));cases.append((op,4,5,len(nodes)-1,'constant'))
    cases.extend([('add',0,2,2,'add-zero-left'),('add',2,0,2,'add-zero-right'),
      ('sub',2,0,2,'sub-zero-right'),('sub',2,2,0,'sub-same'),
      ('mul',0,2,0,'mul-zero-left'),('mul',2,0,0,'mul-zero-right'),
      ('mul',1,2,2,'mul-one-left'),('mul',2,1,2,'mul-one-right')])
    labels=[]
    for op,x,y,z,label in cases:
        require(arithmetic(nodes,op,x,y,z)==label,'shortcut case '+label);labels.append(label)
        try:arithmetic(nodes,op,x,y,7)
        except ValueError:pass
        else:raise AssertionError('shortcut accepted wrong result')
    return dict(cases=len(cases),labels=labels,rejected_wrong_results=len(cases))

def malformed_tests(circuit,args,cert):
    rejected=[]
    def test(label,mutate):
        bad=copy.deepcopy(cert);mutate(bad)
        try:validate(circuit,args,bad)
        except (ValueError,KeyError,IndexError) as e:rejected.append(dict(label=label,reason=str(e)))
        else:raise AssertionError('malformed certificate accepted: '+label)
    test('negative-equivalent-weight',lambda c:c['outputs'][0].__setitem__('weight',c['outputs'][0]['weight']-len(circuit['nodes'])))
    test('boolean-node-index',lambda c:c['outputs'][0].__setitem__('power',True))
    test('negative-balance-result',lambda c:c['balance'].__setitem__('result',c['balance']['result']-len(circuit['nodes'])))
    test('wrong-root',lambda c:c.__setitem__('root',0))
    test('missing-table',lambda c:c['programs'].pop())
    test('changed-source-opcode',lambda c:c['programs'][0]['instructions'][0].__setitem__(0,9))
    test('changed-selector',lambda c:c['programs'][0]['selectors'].__setitem__('first',(123,0,0,0)))
    test('missing-final-register',lambda c:c['programs'][0]['records'].pop(len(c['programs'][0]['instructions'])-1))
    test('changed-column-offset',lambda c:c['programs'][0].__setitem__('base',c['programs'][0]['base']+1))
    ti,ri=next((ti,ri) for ti,p in enumerate(cert['programs']) for ri,r in p['records'].items() if 'tree' in r)
    test('wrong-expansion-sign',lambda c:c['programs'][ti]['records'][ri]['tree'].__setitem__(2,False))
    test('wrong-balanced-term',lambda c:c['programs'][ti]['records'][ri]['balance']['stages'][0].__setitem__(0,(len(circuit['nodes']),True)))
    lookup={tuple(node):i for i,node in enumerate(circuit['nodes'])}
    swapped=[]
    for ti,p in enumerate(cert['programs']):
        for ri in p['records']:
            op,x,*_=p['instructions'][ri]
            if op in (1,2):
                other=('input',p['base']+x+(p['column_capacity'] if op==1 else 0))
                if other in lookup:swapped.append((ti,ri,lookup[other]))
    require(swapped,'no current/next swap test')
    ti,ri,other=swapped[0]
    test('current-next-slot-swapped',lambda c:c['programs'][ti]['records'][ri].__setitem__('node',other))
    test('wrong-rho-power',lambda c:c['outputs'][0].__setitem__('power',0))
    test('wrong-equality-weight',lambda c:c['outputs'][0].__setitem__('weight',0))
    return rejected

def main():
    global OPS,ZERO,ONE,mul,compile_weighted,selectors,eq_point,bus
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--capture',action='append',required=True);ap.add_argument('--output',required=True);a=ap.parse_args();sys.path.insert(0,a.reference_dir)
    from check_whir_handoff import add,sub,mul
    from verify_whir_toy import ZERO,ONE
    from native_folded_v2 import compile_weighted
    from table_constraint_whir import selectors
    from pq384_shift import eq_point
    import pq384_global_bus as bus
    OPS={'add':add,'sub':sub,'mul':mul};shortcuts=shortcut_tests();out=Path(a.output);out.mkdir(parents=True,exist_ok=True);reports=[]
    for path in map(Path,a.capture):
        start=time.perf_counter();c,profile,args=capture(path);cert=produce(c,args);counts=validate(c,args,cert);rejected=malformed_tests(c,args,cert)
        raw=json.dumps(cert,separators=(',',':')).encode();wire=json.loads(raw);require(validate(c,args,wire)==counts,'JSON roundtrip')
        dest=out/(path.name+'-rebuild.json');dest.write_bytes(raw)
        report=dict(profile=profile,capture=str(path),statement_sha256=hashlib.sha256((path/'statement.json').read_bytes()).hexdigest(),proof_sha256=hashlib.sha256((path/'proof.json').read_bytes()).hexdigest(),counts=counts,rejected=rejected,artifact=str(dest),sha256=hashlib.sha256(raw).hexdigest(),seconds=time.perf_counter()-start)
        reports.append(report);print(json.dumps(report),flush=True);(out/'report.json').write_text(json.dumps(dict(status='PASS',shortcuts=shortcuts,captures=reports,source_sha256={name:hashlib.sha256((Path(a.reference_dir)/name).read_bytes()).hexdigest() for name in ('native_folded_v2.py','pq384_terminal_compile.py','pq384_terminal_gkr.py')},scope='Executable structural certificate checks; not Lean kernel proofs of captures or compile_weighted AIR correctness.'),indent=2))
if __name__=='__main__':main()
