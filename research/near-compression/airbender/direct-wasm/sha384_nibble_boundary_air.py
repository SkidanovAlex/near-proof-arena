"""Replace diagnostic public compression words with a committed boundary table.
The boundary root must still be linked to application/recursive call routing.
"""
from collections import Counter
from copy import deepcopy
import sha384_nibble_phase_air as phase
l=phase.l
C,V,A,M,S=l.C,l.V,l.A,l.M,l.S


def privatize(air,traces,public,names):
    g=phase.c.compile_graph();_,reads,_=phase.prepare(g)
    messages=l.ref.public_messages(air,public)
    inputs={};outputs={};counts=Counter()
    for bus,send,message in messages:
        assert bus==2 and len(message)==18
        block,word,*values=message
        assert all(0<=x<16 for x in values)
        target=inputs if send else outputs;key=(block,word)
        if key in target:assert target[key]==values
        target[key]=values;counts[(send,key)]+=1
    blocks=1+max(block for block,_ in inputs)
    assert 1<=blocks<=64
    final_ids=[g.words.index(tuple(word)) for word in g.outputs]
    assert set(inputs)=={(b,w) for b in range(blocks) for w in range(24)}
    assert set(outputs)=={(b,w) for b in range(blocks) for w in final_ids}
    assert all(counts[(True,(b,w))]==reads[w] for b,w in inputs)
    assert all(counts[(False,key)]==1 for key in outputs)
    active=V(0);index=V(1);width=514
    stop=M(active,A(['last'],M(['trans'],S(C(1),V(0,1)))))
    constraints=[l.bit(active),M(['first'],S(active,C(1))),M(['first'],index),
        M(['trans'],M(V(0,1),S(C(1),active))),
        M(['trans'],S(V(1,1),A(index,V(0,1)))),M(stop,S(index,C(blocks-1)))]
    constraints += [M(S(C(1),active),V(i)) for i in range(2,width)]
    interactions=[]
    for slot,word in enumerate(list(range(24))+final_ids):
        send=slot<24;count=reads[word] if send else 1
        interactions.append(dict(bus=2,send=send,mult=[active if (count>>i)&1 else C(0) for i in range(count.bit_length())],
            msg=[index,C(word)]+[V(2+16*slot+i) for i in range(16)]))
    table=dict(width=width,maxLog=max(1,(blocks-1).bit_length()),constraints=constraints,interactions=interactions)
    rows=[]
    for b in range(blocks):rows.append([1,b]+[v for w in range(24) for v in inputs[(b,w)]]+[v for w in final_ids for v in outputs[(b,w)]])
    rows += [[0,blocks-1]+[0]*512 for _ in range((1<<table['maxLog'])-blocks)]
    result=deepcopy(air);result.update(numPub=0,maxPub=0,pubSegs=[]);result['tables'].append(table)
    l.ref.schema(result)
    return result,traces+[rows],[],names+['private-boundary']
