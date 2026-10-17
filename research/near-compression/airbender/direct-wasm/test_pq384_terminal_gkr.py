import argparse,copy,json,random,sys,time
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--circuit-directory');p.add_argument('--output-directory');a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_terminal_gkr as g
    import pq384_terminal_input_weights as w
    rng=random.Random(429);checks=neg=0
    def rand():return tuple(rng.randrange(2013265921) for _ in range(4))
    def dot(a,b):
        v=g.ZERO
        for x,y in zip(a,b):v=g.add(v,g.mul(x,y))
        return v
    # Independent naive subset sums: trace values -> Mobius coefficients.
    for n in range(1,5):
        for k in range(0,4):
            rows=[[rand() for _ in range(1<<k)] for _ in range(1<<n)]
            point=[rand() for _ in range(n)];ac=[rand() for _ in range(1<<k)];bc=[rand() for _ in range(1<<k)]
            flat=[rows[i][j] for j in range(1<<k) for i in range(1<<n)];coeff=[]
            for mask in range(len(flat)):
                value=g.ZERO;s=mask
                while True:
                    value=(g.sub if (mask.bit_count()-s.bit_count())%2 else g.add)(value,flat[s])
                    if s==0:break
                    s=(s-1)&mask
                coeff.append(value)
            e=g.eqs(point);direct=g.ZERO
            for i in range(1<<n):
                for j in range(1<<k):direct=g.add(direct,g.mul(e[i],g.add(g.mul(ac[j],rows[i][j]),g.mul(bc[j],rows[(i+1)%(1<<n)][j]))))
            weights=w.lane_weights(point,ac,bc);assert dot(coeff,weights)==direct;checks+=1
            for u in [[rand() for _ in range(n+k)],[g.ZERO]*(n+k),[g.ONE]*(n+k)]:
                assert g.mle(weights,u)==w.lane_weight_mle(point,ac,bc,u);checks+=1
    # Mixed depth, fanout, all gate types; no witness constant folding.
    for trial in range(8):
        private=[rand() for _ in range(8)];nodes=[['input',i] for i in range(8)];vals=list(private)
        for _ in range(22):
            op=rng.choice(['add','sub','mul']);i=rng.randrange(len(nodes));j=rng.randrange(len(nodes));nodes.append([op,i,j]);vals.append(g.gate(op,vals[i],vals[j]))
        root=len(nodes)-1;c=dict(nodes=nodes,root=root,live_nodes=list(range(len(nodes))),private_input_capacity=8)
        layout=g.layer_circuit(c);proof,ob=g.prove(layout,b'test',private,vals[root]);assert ob==g.verify(layout,b'test',proof,vals[root]);assert dot(ob['private_weights'],private)==ob['private_claim'];checks+=1
        for change in ('round','input','drop','statement','circuit'):
            bad=copy.deepcopy(proof);statement=b'test';trusted=layout
            if change=='round':bad['layers'][0]['rounds'][0][0]=g.add(bad['layers'][0]['rounds'][0][0],g.ONE)
            if change=='input':bad['layers'][0]['inputs'][0]=g.add(bad['layers'][0]['inputs'][0],g.ONE)
            if change=='drop':bad['layers'].pop()
            if change=='statement':statement=b'other'
            if change=='circuit':
                trusted=copy.deepcopy(layout);op,i,j=trusted['layers'][0][1];trusted['layers'][0][1]=('sub' if op!='sub' else 'add',i,j)
            try:g.verify(trusted,statement,bad,vals[root])
            except ValueError:neg+=1
            else:raise AssertionError(change)
    report=dict(status='PASS',algebra_checks=checks,negative_checks=neg,scope='GKR reduction plus exact input-functional mapping; PCS obligation remains required')
    if a.circuit_directory:
        inp=Path(a.circuit_directory);c=json.loads((inp/'circuit.json').read_text());private=json.loads((inp/'input-values.json').read_text());layout=g.layer_circuit(c);start=time.perf_counter()
        proof,ob=g.prove(layout,b'actual-air-terminal-circuit',private);elapsed=time.perf_counter()-start;start=time.perf_counter();assert g.verify(layout,b'actual-air-terminal-circuit',proof)==ob
        assert dot(ob['private_weights'],[tuple(x) for x in private])==ob['private_claim']
        report.update(actual_layers=len(layout['layers']),prover_seconds=elapsed,verifier_seconds=time.perf_counter()-start,extension_elements=sum(3*len(x['rounds'])+2 for x in proof['layers']),transport_field_bytes=16*sum(3*len(x['rounds'])+2 for x in proof['layers']))
        if a.output_directory:
            out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);(out/'proof.json').write_text(json.dumps(proof));(out/'obligation.json').write_text(json.dumps(ob));(out/'report.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
