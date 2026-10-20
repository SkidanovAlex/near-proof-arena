"""Replay full optimized verifier DAG on fresh fused GKR, then export live slices."""
import collections,gzip,hashlib,json
from pathlib import Path
from compile_swirl_gkr_verifier import Circuit
from prove_swirl_binary_root import context
from check_binius_hash_graph import ROOT
OUT=ROOT/'results/swirl-security-review/fused-gkr-arithmetic'

def closure(nodes,roots):
    live=set();stack=list(roots)
    while stack:
        i=stack.pop()
        if i in live:continue
        live.add(i);node=nodes[i]
        if node[0] not in ('input','const'):stack.extend(node[1:])
    return sorted(live)

def main():
    OUT.mkdir(exist_ok=True)
    base=OUT.parent
    raw=gzip.decompress((base/'bdd-gkr-verifier/circuit.json.gz').read_bytes());dag=json.loads(raw)
    proof=json.loads(gzip.decompress((base/'fused-gkr-candidate/proof.json.gz').read_bytes()))
    graph=json.loads((base/'fused-gkr-candidate/graph.json').read_text())
    _,_,known,claim,_,_=context()
    inputs={'claim':claim,**{f'known/{i}':v for i,v in known.items()}}
    cursor=0
    for k,part in enumerate(proof['layers']):
        for j,row in enumerate(part['rounds']):
            for i,v in enumerate(row):inputs[f'proof/{k}/round/{j}/{i}']=v
            inputs[f'challenge/{k}/{j}']=graph['draws'][cursor]['values'];cursor+=1
        for i,v in enumerate(part['inputs']):inputs[f'proof/{k}/input/{i}']=v
        inputs[f'challenge/{k}/gamma']=graph['draws'][cursor]['values'];cursor+=1
    assert cursor==437
    c=Circuit();c.nodes=dag['nodes'];c.inputs=dag['inputs'];values=c.evaluate(inputs)
    assert all(values[i]==(0,0,0,0) for i in dag['checks'])
    expected=json.loads(gzip.decompress((base/'fused-gkr-candidate/pcs-obligation.json.gz').read_bytes()))
    assert list(values[dag['residual']])==expected['claim']
    assert [(i,list(values[w])) for i,w in dag['pcs']]==[(v['slot'],v['weight']) for v in expected['coordinates']]
    full=closure(c.nodes,dag['checks']+[dag['residual']]+[w for _,w in dag['pcs']])
    counts=collections.Counter(c.nodes[i][0] for i in full)
    mulkinds=collections.Counter()
    for i in full:
        node=c.nodes[i]
        if node[0]=='mul':
            a,b=(c.nodes[j] for j in node[1:]);mulkinds['constant_operand' if 'const' in (a[0],b[0]) else 'two_dynamic_operands']+=1
    slices=[]
    for n in [32,128]:
        roots=dag['checks'][:n];live=closure(c.nodes,roots);mapping={i:j for j,i in enumerate(live)}
        nodes=[c.nodes[i] if c.nodes[i][0] in ('input','const') else [c.nodes[i][0],*[mapping[j] for j in c.nodes[i][1:]]] for i in live]
        names=[x[1] for x in nodes if x[0]=='input']
        artifact=dict(nodes=nodes,checks=[mapping[i] for i in roots],inputs={name:inputs[name] for name in names})
        (OUT/f'slice-{n}.json').write_text(json.dumps(artifact,separators=(',',':'))+'\n')
        slices.append(dict(checks=n,nodes=len(nodes),operations=dict(collections.Counter(x[0] for x in nodes)),inputs=len(names)))
    report=dict(source_dag_sha256=hashlib.sha256(raw).hexdigest(),full_live_nodes=len(full),full_operations=dict(counts),
        multiplication_classes=dict(mulkinds),slices=slices,
        checks='All437checks, residual and2603PCSweights replay identically for fresh fused GKR.',
        scope='Slices are selected verifier equalities, not a full verifier. Transcript and PCS obligations remain external.')
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
