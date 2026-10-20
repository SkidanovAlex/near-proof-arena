"""Compare separate and combined diagnostic DAG layouts, no GKR/PCS proof."""
import gzip
import hashlib
import json
from pathlib import Path
from compile_swirl_fixed_dag import compile_air

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/dag-rebalance'


def merge(records):
    merged=dict(air='combined',nodes=[],constraints=[],interactions=[],cases=[dict(seed=c['seed'],values=[]) for c in records[0]['cases']])
    for r in records:
        offset=len(merged['nodes'])
        for op,*args in r['nodes']:
            if op in ('add','sub','mul','neg'):args=[a+offset for a in args]
            # Coordinate namespaces must remain distinct between AIRs.
            elif op in ('variable','first_row','last_row','transition'):args.append(r['air'])
            merged['nodes'].append([op,*args])
        merged['constraints'].extend(i+offset for i in r['constraints'])
        for x in r['interactions']:
            merged['interactions'].append(dict(x,count=x['count']+offset,message=[i+offset for i in x['message']]))
        for dst,src in zip(merged['cases'],r['cases'],strict=True):
            assert dst['seed']==src['seed'];dst['values'].extend(src['values'])
    return merged


def main():
    source=ROOT/'results/swirl-security-review/dag-export/dag.jsonl.gz'
    records=[json.loads(x) for x in gzip.decompress(source.read_bytes()).splitlines()]
    scenarios=[]
    for combined in (False,True):
        for reassociate in (False,True):
            rows=[compile_air(r,reassociate=reassociate) for r in ([merge(records)] if combined else records)]
            scenarios.append(dict(combined=combined,reassociate=reassociate,records=rows,
                padded_gates=sum(x['padded_gates'] for x in rows),
                layers=sum(x['layers'] for x in rows),max_depth=max(x['layers'] for x in rows),
                field_elements=sum(x['gkr_field_elements'] for x in rows),
                ext9_field_bytes=36*sum(x['gkr_field_elements'] for x in rows)))
            print({k:v for k,v in scenarios[-1].items() if k!='records'})
    # Merging must not collapse independently bound AIR coordinates.
    assert scenarios[-1]['records'][0]['inputs']==sum(r['inputs'] for r in scenarios[1]['records'])
    OUT.mkdir(parents=True,exist_ok=True)
    paths=[source,Path(__file__),Path(__file__).with_name('compile_swirl_fixed_dag.py'),Path(__file__).with_name('rebalance_swirl_dag.py')]
    pins={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (OUT/'report.json').write_text(json.dumps(dict(scenarios=scenarios,sha256=pins,
        exclusions=['Three native base-field assignments plus four independent rewrite assignments; extension-field parity remains open.',
                    'Fixed diagnostic checksum coefficients are not sound random output batching.',
                    'No GKR proof generated; exact message-shape estimate for existing format only.',
                    'No PCS input binding, transcript schedule, QROM or Lean compiler theorem.',
                    'Field-degree9 is a cost sensitivity, not a PQ128 instantiation.']),indent=2)+'\n')


if __name__=='__main__':main()
