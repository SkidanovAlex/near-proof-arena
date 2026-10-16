"""Actual compression terminal DAG rewrite and independent evaluation parity."""
import argparse,gzip,hashlib,json,random,time
from pathlib import Path
import pq384_ext8_reference as f
import pq384_ext8_terminal_gkr as g
from rebalance_terminal_linear import rebalance
from check_terminal_dag_certificates import generate,validate


def evaluate(circuit,private):
    values=[]
    for node in circuit['nodes']:
        op=node[0]
        if op=='input':value=private[node[1]]
        elif op=='const':value=tuple(node[1:])
        else:value={'add':f.add,'sub':f.sub,'mul':f.mul}[op](values[node[1]],values[node[2]])
        values.append(value)
    return values[circuit['root']]


def summary(circuit,layout):
    rounds=sum(2*((layout['input_size'] if i==0 else len(layout['layers'][i-1])).bit_length()-1) for i in range(len(layout['layers'])))
    return dict(nodes=len(circuit['nodes']),live_nodes=len(circuit['live_nodes']),layers=len(layout['layers']),gates=sum(map(len,layout['layers'])),sumcheck_rounds=rounds,gkr_scalar_bytes=32*(3*rounds+2*len(layout['layers'])))


def main():
    p=argparse.ArgumentParser();source=p.add_mutually_exclusive_group(required=True)
    source.add_argument('--input',type=Path);source.add_argument('--reduction',type=Path)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    if a.reduction:
        import verify_ext8_execution as verifier
        raw=a.reduction.read_bytes()
        reduction=json.loads(gzip.decompress(raw) if a.reduction.suffix=='.gz' else raw)
        _,_,_,old,layout=verifier.reduction_prefix(reduction,reduction['spec'],reduction['source_roots'])
    else:
        raw=a.input.read_bytes();fixture=json.loads(raw);old=fixture['circuit'];layout=fixture['layout']
    started=time.perf_counter()
    new,stats=rebalance(old);new_layout=g.layer_circuit(new);elapsed=time.perf_counter()-started
    cert=generate(new,new_layout);counts=validate(new,new_layout,cert,coordinate_degree=8)
    rng=random.Random(90400);checks=[]
    for case in ('zero','one','random_ext8'):
        values=[f.ZERO if case=='zero' else f.ONE if case=='one' else tuple(rng.randrange(f.P) for _ in range(8)) for _ in range(old['private_input_capacity'])]
        assert evaluate(old,values)==evaluate(new,values);checks.append(case)
    baseline=summary(old,layout);optimized=summary(new,new_layout);assert baseline['gkr_scalar_bytes']==111616
    report=dict(status='PASS',baseline=baseline,optimized=optimized,rewrite_seconds=elapsed,region_stats=stats,layer_certificate=counts,differential_vectors=checks,gkr_scalar_bytes_saved=baseline['gkr_scalar_bytes']-optimized['gkr_scalar_bytes'],scope='Prototype rewrite of the actual verifier-derived compression terminal DAG. Three differential input vectors and structural layer certificate pass. No actual new GKR/PCS proof, accepted compiler change, universal semantic theorem or full-proof size claim.',source_sha256=hashlib.sha256(raw).hexdigest(),source_kind='reduction' if a.reduction else 'compiled_fixture')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
    a.output.with_suffix('.circuit.json').write_text(json.dumps(dict(circuit=new,layout=new_layout),separators=(',',':')))

if __name__=='__main__':main()
