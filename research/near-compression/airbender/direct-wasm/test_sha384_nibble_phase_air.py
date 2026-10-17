"""Full-witness complete compression AIR test; no succinct proof claim."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sha384_nibble_phase_air as phase
import pq384_ext8_auxiliary as aux
import scheduled_bus_whir as algebra
from measure_sha384_block_dag import Probe

ROOT=Path(__file__).resolve().parents[2]


def main():
    p=argparse.ArgumentParser();p.add_argument('--probe-library',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    probe=Probe(a.probe_library);padded,states=probe.run(bytes(range(129)))
    records=[(states[i],padded[128*i:128*(i+1)],states[i+1]) for i in range(len(states)-1)]
    air,traces,public,names=phase.compile_air(records)
    result=phase.l.ref.check(air,traces,public)
    evaluated=sum(len(row) for table in result['residuals'] for row in table)
    del result
    shapes=[dict(name=name,rows=len(rows),source_width=t['width'],aux_base_width=8*aux.layout(t)['aux_columns'],degree=algebra.table_degree(t,len(public))) for name,t,rows in zip(names,air['tables'],traces)]
    g=phase.c.compile_graph();program,_,constants=phase.prepare(g)
    shape64=[]
    for kind in ('schedule','round','endpoint'):
        t=phase.phase_table(g,program,kind,64,constants)
        shape64.append(dict(name=kind,rows=1<<t['maxLog'],source_width=t['width'],aux_base_width=8*aux.layout(t)['aux_columns'],degree=algebra.table_degree(t,len(public))))
    for op in (*phase.l.OPS,'range'):
        t=phase.l.fixed_table(op,(18688*64).bit_length())
        shape64.append(dict(name=op+'/fixed',rows=1<<t['maxLog'],source_width=t['width'],aux_base_width=8*aux.layout(t)['aux_columns'],degree=algebra.table_degree(t,0)))
    for shape in shape64:
        shape['packing']={kind:phase.planner.geometry(shape['rows'],shape[key]) for kind,key in [('source','source_width'),('auxiliary','aux_base_width')]}
    assert all(x['within_current_degree_lane_caps'] and x['rows']<=8192 for shape in shape64 for x in shape['packing'].values())
    rejected=[]
    def mutate(name,ti,ri,ci):
        old=traces[ti][ri][ci];traces[ti][ri][ci]=(old+1)%16
        try:phase.l.ref.check(air,traces,public)
        except ValueError:rejected.append(name)
        else:raise AssertionError(name)
        finally:traces[ti][ri][ci]=old
    for args in [('schedule-selector',0,0,2),('round-word-copy',1,0,82),('round-carry',1,0,air['tables'][1]['width']-1),('block-id',1,80,1),('endpoint-output',2,0,air['tables'][2]['width']-2),('fixed-multiplicity',3,0,12)]:mutate(*args)
    traces[1][10][12],traces[1][10][13]=traces[1][10][13],traces[1][10][12]
    try:phase.l.ref.check(air,traces,public)
    except ValueError:rejected.append('valid-onehot-wrong-phase')
    else:raise AssertionError('phase reordered')
    finally:traces[1][10][12],traces[1][10][13]=traces[1][10][13],traces[1][10][12]
    old=public[-1];public[-1]=(old+1)%16
    try:phase.l.ref.check(air,traces,public)
    except ValueError:rejected.append('public-result')
    else:raise AssertionError('public result accepted')
    finally:public[-1]=old
    raw=json.dumps(air,sort_keys=True,separators=(',',':')).encode();spec_path=a.output.resolve().with_suffix('.spec.json.gz');spec_path.write_bytes(gzip.compress(raw,mtime=0))
    sources=[Path(__file__),Path(phase.__file__),Path(phase.c.__file__),Path(phase.l.__file__),Path(phase.planner.__file__),Path(phase.l.ref.__file__),Path(aux.__file__),Path(algebra.__file__),Path(Probe.run.__code__.co_filename),spec_path]
    report=dict(status='COMPLETE_NIBBLE_COMPRESSION_AIR_CHECKED',compression_blocks=len(records),source_constraints_evaluated=evaluated,public_field_elements=len(public),table_shapes=shapes,negative_cases=rejected,
        source_aux_cells=sum(s['rows']*(s['source_width']+s['aux_base_width']) for s in shapes),
        actual_compiled_64_block_shapes=shape64,
        compiled_64_block_source_aux_cells=sum(s['rows']*(s['source_width']+s['aux_base_width']) for s in shape64),
        compiled_64_block_witness_checked=False,
        scope='Canonical AIR jointly enforces phase programs, bounded additions, lookup relations, routing and public full512-bit state/block/result boundaries. Full-witness interpreter only; no generated succinct proof, universal compiler/Lean theorem or PQ128 security. Public boundary transport is diagnostic, not private recursive call binding.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
