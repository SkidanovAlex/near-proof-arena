"""Concrete terminal compiler structural certificate validation.
Checks the premises of TerminalDAGLayerCertificate; not a Lean parser refinement.
No cryptographic or AIR-program-to-DAG correctness claim.
"""
import argparse,copy,hashlib,json,sys,time
from pathlib import Path

def require(ok,msg):
    if not ok:raise ValueError(msg)

def closure(nodes,root):
    live=set(); todo=[root]
    while todo:
        i=todo.pop();require(type(i)is int and 0<=i<len(nodes),'node index')
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    return live

def generate(circuit,layout):
    nodes=circuit['nodes'];live=set(circuit['live_nodes']);levels=[];last=[0]*len(nodes)
    for i,node in enumerate(nodes):
        levels.append(0 if node[0] in ('input','const') else 1+max(levels[node[1]],levels[node[2]]))
    for i in live:
        if nodes[i][0] in ('add','sub','mul'):
            for j in nodes[i][1:]:last[j]=max(last[j],levels[i])
    cursor=layout['private_capacity'];initial={}
    for i in sorted(live):
        if nodes[i][0]=='input':initial[i]=nodes[i][1]
        elif nodes[i][0]=='const':initial[i]=cursor;cursor+=1
    plans=[]
    for d in range(1,len(layout['layers'])+1):
        current={};position=1
        for i in sorted(live):
            if levels[i]==d or (levels[i]<d and last[i]>d):current[i]=position;position+=1
        plans.append(current)
    return dict(initial=initial,plans=plans)

def validate(circuit,layout,cert, *, coordinate_degree=4):
    require(type(coordinate_degree) is int and coordinate_degree>0,'coordinate degree')
    nodes=circuit['nodes'];ops=('add','sub','mul');size=layout['input_size'];cap=layout['private_capacity']
    require(size>cap>0 and size&(size-1)==0 and cap&(cap-1)==0,'input shape')
    for i,node in enumerate(nodes):
        require(node[0] in (*ops,'const','input'),'node kind')
        if node[0] in ops:require(len(node)==3 and all(type(j)is int and 0<=j<i for j in node[1:]),'acyclic')
        elif node[0]=='input':require(len(node)==2 and type(node[1])is int and 0<=node[1]<cap,'input slot')
        else:require(len(node)==1+coordinate_degree and all(type(v)is int and 0<=v<2013265921 for v in node[1:]),'constant canonical')
    require(set(circuit['live_nodes'])==closure(nodes,circuit['root']) and len(set(circuit['live_nodes']))==len(circuit['live_nodes']),'source live closure')
    constants={int(i):tuple(v) for i,v in layout['constants'].items()}
    require(all(cap<=i<size-1 for i in constants),'constant range')
    previous=cert['initial'];zero=size-1;previous_size=size
    counts=dict(initial=len(previous),computed=0,relayed=0,padding=0)
    for i,pos in previous.items():
        require(0<=i<len(nodes) and 0<=pos<size,'initial bounds');node=nodes[i]
        if node[0]=='input':require(pos==node[1] and pos<cap,'initial input route')
        else:require(node[0]=='const' and cap<=pos and constants.get(pos,(0,)*coordinate_degree)==tuple(node[1:]),'initial constant route')
    require(len(cert['plans'])==len(layout['layers']),'layer count')
    for positions,gates in zip(cert['plans'],layout['layers']):
        require(len(gates)>0 and len(gates)&(len(gates)-1)==0,'layer shape')
        require(tuple(gates[0])==('add',zero,zero),'zero relay')
        for op,a,b in gates:require(op in ops and 0<=a<previous_size and 0<=b<previous_size,'gate bounds')
        require(len(set(positions.values()))==len(positions),'duplicate live position')
        used={0}
        for i,pos in positions.items():
            require(type(i)is int and 0<=i<len(nodes) and 0<pos<len(gates),'live placement bounds')
            node=nodes[i];actual=tuple(gates[pos]);used.add(pos)
            computed=node[0] in ops and node[1] in previous and node[2] in previous and actual==(node[0],previous[node[1]],previous[node[2]])
            relayed=i in previous and actual==('add',previous[i],zero)
            require(computed or relayed,'computed/relay route')
            counts['computed' if computed else 'relayed']+=1
        for pos,gate in enumerate(gates):
            if pos not in used:require(tuple(gate)==('add',zero,zero),'unaccounted nonzero gate');counts['padding']+=1
        previous=positions;zero=0;previous_size=len(gates)
    require(circuit['root'] in previous and previous[circuit['root']]==layout['root'],'root route')
    return counts

def replay(path, *, input_log=None):
    statement=json.loads((path/'statement.json').read_text());proof=json.loads((path/'proof.json').read_text());spec=statement['spec'];roots=[bytes.fromhex(x) for x in statement['roots']]
    if proof['profile']=='near-pq384-seed-gkr-bus-v1':
        require(input_log is None,'seed profile has no fixed input cap')
        import pq384_seed_gkr_bus as bus
        st,t,a,g=bus.begin(spec,roots,bus.configure(spec['air']))
    else:
        import pq384_gkr_bus as bus
        require(proof['profile']==bus.profile(input_log),'profile/configuration mismatch')
        if input_log is not None:
            require(bus.verify(proof,spec,roots,input_log=input_log),'fixed proof verification')
        st,t,a,g=bus.begin(spec,roots,input_log=input_log)
    ars=[bus.pcs.decode_hash(x) for x in proof['aux_roots']];bus.initialize_aux(t,spec,ars,proof['finals'])
    terminals=[bus.constraint_verify(spec,t,ti,rs) for ti,rs in enumerate(proof['tables'])]
    circuit,layout,_=bus.terminal_layout(spec,t,a,g,proof['finals'],terminals,**({} if input_log is None else {'input_log':input_log}))
    return circuit,layout,proof['profile']

def negatives(circuit,layout,cert):
    mutations=[]
    def add(label,which,fn):
        c,l,s=copy.deepcopy(circuit),copy.deepcopy(layout),copy.deepcopy(cert)
        fn({'c':c,'l':l,'s':s}[which]);mutations.append((label,c,l,s))
    add('out-of-range-operand','l',lambda x:x['layers'][0].__setitem__(1,('add',layout['input_size'],0)))
    add('negative-operand','l',lambda x:x['layers'][0].__setitem__(1,('add',-1,0)))
    add('non-power-two-layer','l',lambda x:x['layers'][0].pop())
    add('zero-relay','l',lambda x:x['layers'][0].__setitem__(0,('sub',0,0)))
    add('root-position','l',lambda x:x.__setitem__('root',0))
    add('source-live-missing-root','c',lambda x:x['live_nodes'].remove(x['root']))
    add('initial-position','s',lambda x:x['initial'].__setitem__(next(iter(x['initial'])),layout['input_size']))
    add('layer-live-missing-root','s',lambda x:x['plans'][-1].pop(circuit['root']))
    add('live-position','s',lambda x:x['plans'][-1].__setitem__(circuit['root'],0))
    add('layer-omitted','s',lambda x:x['plans'].pop())
    prev=cert['initial'];zero=layout['input_size']-1;found=False
    for d,positions in enumerate(cert['plans']):
        for i,pos in positions.items():
            if i in prev and tuple(layout['layers'][d][pos])==('add',prev[i],zero):
                add('nonzero-relay-operand','l',lambda x,d=d,pos=pos,i=i,prev=prev:x['layers'][d].__setitem__(pos,('add',prev[i],prev[i])))
                add('relay-source-not-live','s',lambda x,d=d,i=i:(x['initial'] if d==0 else x['plans'][d-1]).pop(i))
                found=True;break
        if found:break
        prev=positions;zero=0
    require(found,'capture has no relay test')
    rejected=[]
    for label,c,l,s in mutations:
        try:validate(c,l,s)
        except ValueError as e:rejected.append(dict(label=label,reason=str(e)))
        else:raise AssertionError('accepted mutation '+label)
    return rejected

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--capture',action='append',required=True);p.add_argument('--output',required=True);p.add_argument('--input-log',type=int);a=p.parse_args();sys.path.insert(0,a.reference_dir)
    out=Path(a.output);out.mkdir(parents=True,exist_ok=True);reports=[]
    for name in a.capture:
        start=time.perf_counter();path=Path(name);c,l,profile=replay(path,input_log=a.input_log);s=generate(c,l);counts=validate(c,l,s);bad=negatives(c,l,s)
        bundle=dict(circuit=c,layout=l,certificate=s);raw=json.dumps(bundle,separators=(',',':')).encode();dest=out/(path.name+'-certificate.json');dest.write_bytes(raw)
        restored=json.loads(raw);restored['certificate']['initial']={int(k):v for k,v in restored['certificate']['initial'].items()};restored['certificate']['plans']=[{int(k):v for k,v in plan.items()} for plan in restored['certificate']['plans']]
        require(validate(restored['circuit'],restored['layout'],restored['certificate'])==counts,'certificate JSON roundtrip')
        r=dict(profile=profile,trusted_input_log=a.input_log,full_proof_verified=a.input_log is not None,capture=str(path),nodes=len(c['nodes']),layers=len(l['layers']),counts=counts,rejected=bad,artifact=str(dest),sha256=hashlib.sha256(raw).hexdigest(),seconds=time.perf_counter()-start)
        reports.append(r);print(json.dumps(r),flush=True);(out/'report.json').write_text(json.dumps(dict(status='PASS',captures=reports,scope='Python structural premise validation, not a kernel proof for captures or emitter/AIR refinement.'),indent=2))
if __name__=='__main__':main()
