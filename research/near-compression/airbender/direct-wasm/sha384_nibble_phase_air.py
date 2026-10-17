"""Complete bounded compression AIR with public state/block/result boundary.
Research compiler, not Lean-certified; no succinct proof or security claim.
"""
from collections import Counter, defaultdict
import sha384_nibble_lookup_air as l
import plan_sha384_nibble_rows as planner
import sha384_nibble_circuit as c
C,V,A,M,N,S=l.C,l.V,l.A,l.M,l.N,l.S


def product(xs):
    out=C(1)
    for x in xs:out=M(out,x)
    return out


def prepare(g):
    phases,reads,missing,producers,_=planner.plan(g)
    constants={w:value for value,w in g.constants.items()}
    word_of={w:i for i,word in enumerate(g.words) for w in word}
    gates=defaultdict(list)
    for gate,phase in zip(g.gates,g.gate_phases):
        if gate[0]!='const':gates[phase].append(gate)
    result={}
    for phase,row in phases.items():
        external=set(row['wires'])-row['owned'];imports=[]
        for _,ins,_,_ in gates[phase]:
            for w in ins:
                if w in external and word_of[w] not in imports:imports.append(word_of[w])
        wires=[w for wi in imports for w in g.words[wi]]+sorted(row['owned'])
        assert len(wires)==len(set(wires)) and set(wires)==set(row['wires'])
        exports=list(row['exports'])
        if phase[0]=='endpoint':exports=[(word_of[word[0]],1) for word in g.outputs]
        result[phase]=dict(wires=wires,index={w:i for i,w in enumerate(wires)},imports=imports,exports=exports,gates=gates[phase],ranges=set())
    for w in missing:
        # Move boundary-word range checks to the endpoint which already imports
        # them through the exact word bus. Keep the hot round table uniform.
        candidates=[p for p,row in result.items() if w in row['index']]
        phase=next((p for p in candidates if p[0]=='endpoint'),candidates[0])
        result[phase]['ranges'].add(w)
    return result,reads,constants


def phase_table(g,program,kind,blocks,constants):
    entries=[row for phase,row in program.items() if phase[0]==kind]
    n=len(entries);active=V(0);block=V(1);selectors=[V(2+i) for i in range(n)];offset=2+n
    width=offset+len(entries[0]['wires']);assert all(len(r['wires'])+offset==width for r in entries)
    def pick(exprs):
        assert len(exprs)==n
        if all(e==exprs[0] for e in exprs):return exprs[0]
        return l.add([M(sel,e) for sel,e in zip(selectors,exprs)])
    def wire(row,w):return C(constants[w]) if w in constants else V(offset+row['index'][w])
    def selected_wire(ws):return pick([wire(row,w) for row,w in zip(entries,ws)])
    constraints=[l.bit(active)]+[l.bit(x) for x in selectors]+[S(l.add(selectors),active),M(['first'],S(selectors[0],C(1))),M(['first'],block)]
    constraints += [M(['trans'],M(V(0,1),S(C(1),active)))]
    for i in range(n):constraints.append(M(['trans'],S(V(2+i,1),M(V(0,1),selectors[(i-1)%n]))))
    constraints.append(M(['trans'],S(V(1,1),A(block,M(V(0,1),selectors[-1])))))
    stop=M(active,A(['last'],M(['trans'],S(C(1),V(0,1)))))
    constraints += [M(stop,S(block,C(blocks-1))),M(stop,S(selectors[-1],C(1)))]
    constraints += [M(S(C(1),active),V(i)) for i in range(offset,width)]
    interactions=[]
    def send(bus,msg,mult=None,direction=True):
        interactions.append(dict(bus=bus,send=direction,mult=[active] if mult is None else mult,msg=msg))
    assert len({len(r['gates']) for r in entries})==1
    for gi in range(len(entries[0]['gates'])):
        gs=[row['gates'][gi] for row in entries]
        op,_,_,bound=gs[0]
        assert all(x[0]==op and x[3]==bound and len(x[1])==len(gs[0][1]) for x in gs)
        ins=[selected_wire([gate[1][i] for gate in gs]) for i in range(len(gs[0][1]))]
        outs=[selected_wire([gate[2][i] for gate in gs]) for i in range(len(gs[0][2]))]
        if op=='add':
            constraints += [M(active,S(l.add(ins),A(outs[0],M(C(16),outs[1])))),
                            product([S(outs[1],C(i)) for i in range(bound)]),
                            product([S(ins[-1],C(i)) for i in range(bound)])]
        else:send(0,[C(l.OPS.index(op)),*ins,*([C(0)] if len(ins)==2 else []),outs[0]])
    for col in sorted({r['index'][w] for r in entries for w in r['ranges']}):
        mask=l.add([selectors[i] for i,r in enumerate(entries) if r['wires'][col] in r['ranges']])
        send(1,[V(offset+col)],[mask])
    assert len({len(r['imports']) for r in entries})==1 and len({len(r['exports']) for r in entries})==1
    for i in range(len(entries[0]['imports'])):
        ids=[r['imports'][i] for r in entries]
        msg=[block,pick([C(wi) for wi in ids])]+[selected_wire([g.words[wi][j] for wi in ids]) for j in range(16)]
        send(2,msg,direction=False)
    for i in range(len(entries[0]['exports'])):
        pairs=[r['exports'][i] for r in entries];ids=[wi for wi,_ in pairs]
        msg=[block,pick([C(wi) for wi in ids])]+[selected_wire([g.words[wi][j] for wi in ids]) for j in range(16)]
        mult=[l.add([selectors[j] for j,(_,count) in enumerate(pairs) if (count>>bit)&1]) for bit in range(max(count for _,count in pairs).bit_length())]
        send(2,msg,mult)
    return dict(width=width,maxLog=max(1,(blocks*n-1).bit_length()),constraints=constraints,interactions=interactions)


def compile_air(records):
    assert 1<=len(records)<=64
    g=c.compile_graph();program,reads,constants=prepare(g);tables=[];traces=[];names=[]
    witnesses=[]
    for state,block,result in records:
        source=c.inputs(state,block);values=c.witness(g,source)
        assert c.check(g,source,values,result)
        witnesses.append(values)
    for kind in ('schedule','round','endpoint'):
        entries=[row for phase,row in program.items() if phase[0]==kind];n=len(entries)
        table=phase_table(g,program,kind,len(records),constants);rows=[]
        for bi,values in enumerate(witnesses):
            for i,row in enumerate(entries):rows.append([1,bi]+[int(i==j) for j in range(n)]+[values[w] for w in row['wires']])
        rows += [[0,len(records)-1]+[0]*(table['width']-2) for _ in range((1<<table['maxLog'])-len(rows))]
        tables.append(table);traces.append(rows);names.append(kind)
    counts={0:Counter(),1:Counter()}
    for table,rows in zip(tables,traces):
        for ri in range(len(rows)):
            for interaction in table['interactions']:
                if interaction['bus'] not in counts:continue
                ev=lambda e:l.ref.evaluate(e,rows,ri,[])
                mult=sum((1<<i)*ev(e) for i,e in enumerate(interaction['mult']))
                counts[interaction['bus']][tuple(ev(e) for e in interaction['msg'])]+=mult
    multiplicity_bits=(18688*len(records)).bit_length()
    for op in (*l.OPS,'range'):
        table=l.fixed_table(op,multiplicity_bits);rows=l.table_rows(op,counts[1 if op=='range' else 0],multiplicity_bits)
        tables.append(table);traces.append(rows);names.append(op+'/fixed')
    # Public boundary contains repeated input-word sends and final output receives.
    inputs=[];outputs=[]
    for bi,((state,block,result),values) in enumerate(zip(records,witnesses)):
        source=c.inputs(state,block)
        for wi,count in reads.items():
            if all(w<384 for w in g.words[wi]):inputs += [[bi,wi,*[source[w] for w in g.words[wi]]]]*count
        for wi,word in enumerate(g.words):
            if word in [tuple(w) for w in g.outputs]:
                index=[tuple(w) for w in g.outputs].index(word)
                outputs.append([bi,wi,*[(result[index]>>(4*j))&15 for j in range(16)]])
    public=[];segments=[]
    for send,messages in ((True,inputs),(False,outputs)):
        count_at=len(public);public += list(len(messages).to_bytes(4,'little'));start=len(public)
        public += [x for message in messages for x in message]
        segments.append(dict(bus=2,send=send,width=18,countAt=count_at,start=start,startAt=None,indexBase=None,prefix=[]))
    air=dict(format='np-air-v2',numBuses=3,numPub=len(public),maxPub=len(public),pubSegs=segments,tables=tables)
    l.ref.schema(air)
    return air,traces,public,names
