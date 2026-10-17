"""Fixed DAG export parity and layered-GKR cost probe, not a proof system.

Output batching uses fixed diagnostic coefficients, NOT sound random batching.
Native reference cases lie in the base field; extension-field parity is open.
"""
import copy
import gzip
import hashlib
import json
from pathlib import Path
from pq384_terminal_gkr import layer_circuit

P = 2013265921
ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'results/swirl-security-review/dag-export'


def input_value(key, seed):
    if key[0] == 'variable':
        _, kind, part, offset, index, *namespace = key
        return ((seed+1)*(1+kind*100003+part*1009+offset*97+index*7)) % P
    return {'first_row': seed+13, 'last_row': seed+17, 'transition': 1-(seed+17)}[key[0]] % P


def compile_air(record, *, reassociate=False, return_artifacts=False):
    nodes=[]; mapping=[]; slots={}
    for original_index, node in enumerate(record['nodes']):
        op,*args=node
        if op in ('variable','first_row','last_row','transition'):
            key=tuple(node)
            slot=slots.setdefault(key,len(slots)); new=('input',slot)
        elif op=='const':
            assert len(args)==1 and 0 <= args[0] < P
            new=('const',args[0],0,0,0)
        elif op=='neg':
            assert len(args)==1 and 0 <= args[0] < original_index
            zero=len(nodes);nodes.append(('const',0,0,0,0));new=('sub',zero,mapping[args[0]])
        else:
            assert op in ('add','sub','mul') and len(args)==2
            assert all(type(a) is int and 0 <= a < original_index for a in args)
            new=(op,*(mapping[a] for a in args))
        mapping.append(len(nodes));nodes.append(new)
    outputs=list(record['constraints'])
    for interaction in record['interactions']:
        outputs.extend([interaction['count'],*interaction['message']])
    outputs=sorted(set(outputs)); assert outputs
    assert all(type(i) is int and 0 <= i < len(mapping) for i in outputs)
    # Diagnostic balanced output checksum keeps all semantic outputs reachable.
    terms=[]
    for j,i in enumerate(outputs):
        c=len(nodes);nodes.append(('const',j+1,0,0,0))
        terms.append(len(nodes));nodes.append(('mul',mapping[i],c))
    while len(terms)>1:
        nxt=[]
        for j in range(0,len(terms),2):
            if j+1==len(terms): nxt.append(terms[j]);continue
            nxt.append(len(nodes));nodes.append(('add',terms[j],terms[j+1]))
        terms=nxt
    root=terms[0]
    if reassociate:
        from rebalance_swirl_dag import rebalance
        original_nodes=nodes
        requested=mapping+[root]
        nodes, rewritten = rebalance(nodes, requested)
        # Independent slot assignments exercise different AIR namespaces and
        # selectors; these are rewrite checks, not accepted verifier witnesses.
        import random
        def evaluate_base(graph, private):
            vals=[]
            for op,*args in graph:
                if op=='input':value=private[args[0]]
                elif op=='const':value=args[0]
                elif op=='add':value=vals[args[0]]+vals[args[1]]
                elif op=='sub':value=vals[args[0]]-vals[args[1]]
                else:value=vals[args[0]]*vals[args[1]]
                vals.append(value%P)
            return vals
        rng=random.Random(20261017)
        assignments=[[c]*len(slots) for c in (0,1,P-1)]
        assignments.append([rng.randrange(P) for _ in slots])
        for private in assignments:
            old_values=evaluate_base(original_nodes,private)
            new_values=evaluate_base(nodes,private)
            assert [old_values[i] for i in requested]==[new_values[i] for i in rewritten]
        mapping, root = rewritten[:-1], rewritten[-1]
    live=set(); todo=[root]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    circuit=dict(nodes=nodes,live_nodes=sorted(live),private_input_capacity=1<<max(0,(len(slots)-1).bit_length()),root=root)
    layout=layer_circuit(circuit)
    for case in record['cases']:
        values=[]
        private=[0]*circuit['private_input_capacity']
        for key,slot in slots.items():private[slot]=input_value(key,case['seed'])
        for op,*args in nodes:
            if op=='const':v=args[0]
            elif op=='input':v=private[args[0]]
            elif op=='add':v=values[args[0]]+values[args[1]]
            elif op=='sub':v=values[args[0]]-values[args[1]]
            else:v=values[args[0]]*values[args[1]]
            values.append(v%P)
        assert [values[i] for i in mapping]==case['values']
        v=private+[0]*(layout['input_size']-len(private))
        for i,c in layout['constants'].items():v[i]=c[0]
        for gates in layout['layers']:
            v=[(v[a]+v[b] if op=='add' else v[a]-v[b] if op=='sub' else v[a]*v[b])%P for op,a,b in gates]
        assert v[layout['root']]==values[root]
    previous_widths=[layout['input_size']]+[len(x) for x in layout['layers'][:-1]]
    gkr_elements=sum(6*((w-1).bit_length())+2 for w in previous_widths)
    stats=dict(gkr_field_elements=gkr_elements, air=record['air'],source_nodes=len(mapping),inputs=len(slots),semantic_outputs=len(outputs),
                lowered_nodes=len(nodes),live_nodes=len(live),input_size=layout['input_size'],
                layers=len(layout['layers']),layer_widths=[len(x) for x in layout['layers']],
                padded_gates=sum(len(x) for x in layout['layers']),cases=len(record['cases']))
    return (stats,layout,slots) if return_artifacts else stats


def main():
    source=(OUT/'dag.jsonl.gz').read_bytes()
    records=[json.loads(x) for x in gzip.decompress(source).splitlines()]
    rows=[compile_air(r) for r in records]
    summary={k:sum(r[k] for r in rows) for k in ('source_nodes','inputs','semantic_outputs','lowered_nodes','live_nodes','padded_gates','cases','gkr_field_elements')}
    # Mutation gates exercise reference-value and topological-edge validation.
    mutations=[]
    changed=copy.deepcopy(records[0])
    changed['cases'][0]['values'][0]=(changed['cases'][0]['values'][0]+1)%P
    mutations.append(changed)
    changed=copy.deepcopy(records[0])
    idx=next(i for i,n in enumerate(changed['nodes']) if n[0] in ('add','sub','mul'))
    changed['nodes'][idx][1]=idx
    mutations.append(changed)
    for changed in mutations:
        try: compile_air(changed)
        except AssertionError: pass
        else: raise AssertionError('malformed or inconsistent export accepted')
    summary['rejected_mutations']=len(mutations)
    summary['separate_gkr_ext9_field_bytes']=36*summary['gkr_field_elements']
    result=dict(summary=summary,records=rows,source_sha256=hashlib.sha256(source).hexdigest(),
                status='BASE_FIELD_NODE_AND_LAYER_PARITY_ONLY',
                exclusions=['No GKR proof generated or input PCS link.', 'Fixed diagnostic output checksum is not sound batching.',
                            'No extension-field parity, compiler Lean theorem, PQ128 or full NEAR proof.'])
    (OUT/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(summary))


if __name__=='__main__':main()
