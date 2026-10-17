"""Independent canonical AIR interpreter and adversarial table checks."""
import argparse
import hashlib
import gzip
import json
from pathlib import Path
import sha384_nibble_lookup_air as lookup
import pq384_ext8_auxiliary as aux
import scheduled_bus_whir as algebra

ROOT=Path(__file__).resolve().parents[2]


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    air,traces,names,requests=lookup.fixture()
    result=lookup.ref.check(air,traces,[])
    constraints=sum(len(row) for table in result['residuals'] for row in table)
    shapes=[dict(name=name,rows=len(rows),source_width=table['width'],
        aux_base_width=8*aux.layout(table)['aux_columns'],degree=algebra.table_degree(table,0))
        for name,table,rows in zip(names,air['tables'],traces)]
    # Each independently enumerated request/table message uses exactly the
    # expected host truth-table value. AIR outputs have no free output column.
    truth_rows=0
    for ti,name in enumerate(names):
        if not name.endswith('/fixed'):continue
        op=name.split('/')[0]
        actual=[tuple(row[0]['message']) for row in result['interactions'][ti]]
        assert len(actual)==len(set(actual))
        for msg in actual:
            if op=='range':assert 0<=msg[0]<16
            else:
                args=msg[1:3] if op.startswith('splice') else msg[1:4]
                assert msg[-1]==lookup.circuit.relation(op,args)
            truth_rows+=1
    del result
    rejected=[]
    def mutation(name,ti,ri,ci,value):
        old=traces[ti][ri][ci];traces[ti][ri][ci]=value
        try:lookup.ref.check(air,traces,[])
        except ValueError:rejected.append(name)
        else:raise AssertionError(name)
        finally:traces[ti][ri][ci]=old
    mutation('fixed-index-bit',0,1,0,0)
    mutation('fixed-nonboolean-index',0,1,0,2)
    mutation('fixed-nonboolean-multiplicity',0,0,12,2)
    mutation('fixed-extra-multiplicity',0,0,12,1-traces[0][0][12])
    mutation('request-wrong-output',1,0,5,(traces[1][0][5]+1)%16)
    mutation('request-hidden',1,0,0,0)
    mutation('range-request-outside-nibble',13,0,1,16)
    saved=traces[0]
    traces[0]=saved[:2048]
    try:lookup.ref.check(air,traces,[])
    except ValueError:rejected.append('truncated-fixed-enumeration')
    else:raise AssertionError('accepted shortened table')
    finally:traces[0]=saved
    traces[0][1],traces[0][2]=traces[0][2],traces[0][1]
    try:lookup.ref.check(air,traces,[])
    except ValueError:rejected.append('reordered-fixed-enumeration')
    else:raise AssertionError('accepted reordered table')
    finally:traces[0][1],traces[0][2]=traces[0][2],traces[0][1]
    raw=json.dumps(air,sort_keys=True,separators=(',',':')).encode()
    spec_path=a.output.resolve().with_suffix('.spec.json.gz')
    spec_path.write_bytes(gzip.compress(raw,mtime=0))
    report=dict(air_spec_sha256=hashlib.sha256(raw).hexdigest(),status='FIXED_LOOKUP_AIR_FULL_WITNESS_CHECKED',table_shapes=shapes,
        source_constraints_evaluated=constraints,fixed_truth_rows_checked=truth_rows,
        lookup_requests=sum(len(v) for k,v in requests.items() if k!='range'),range_requests=len(requests['range']),
        negative_cases=rejected,
        fixed_tables_source_aux_cells=sum(s['rows']*(s['source_width']+s['aux_base_width']) for s in shapes if s['name'].endswith('/fixed')),
        scope='Actual canonical polynomial AIR constrains enumeration, lookup values and multiplicity bits; natural bus checker balances requests. Requests remain external to SHA phase AIR. No succinct proof, compiler/Lean theorem, randomized-bus soundness, or PQ128 result.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(lookup.__file__),Path(lookup.circuit.__file__),Path(__file__).with_name('plan_sha384_nibble_rows.py'),Path(aux.__file__),Path(lookup.ref.__file__),Path(algebra.__file__),spec_path]})
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
