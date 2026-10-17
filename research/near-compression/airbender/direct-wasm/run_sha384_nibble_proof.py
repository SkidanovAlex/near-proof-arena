"""Prepare bounded nibble AIR witness and run the existing Ext8 prover.
Diagnostic public boundary; no recursive/PQ128 or Lean correctness certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import sha384_nibble_phase_air as phase
import pq384_ext8_auxiliary as aux
import pq384_ext8_weighted as pcs
from pq384_ext8_native import Kernel
from measure_sha384_block_dag import Probe
from run_pq384_gkr_bus import choose_packing
import scheduled_bus_whir as algebra


def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()


def main():
    p=argparse.ArgumentParser();p.add_argument('--blocks',type=int,default=64);p.add_argument('--queries',type=int,default=8)
    p.add_argument('--probe-library',required=True);p.add_argument('--native-library',required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');p.add_argument('--reuse-prepared',action='store_true');a=p.parse_args()
    assert 1<=a.blocks<=64 and 1<=a.queries<=4096
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);source=out/'source';source.mkdir(exist_ok=True)
    if a.reuse_prepared:
        report=json.loads((out/'preparation.json').read_text());assert report['blocks']==a.blocks and report['full_witness_verified']
        for name,digest in report['files'].items():assert hashlib.sha256((out/name).read_bytes()).hexdigest()==digest
        assert report['generator_sha256']==hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    else:
        started=time.monotonic();probe=Probe(a.probe_library)
        message=bytes((17*i+3)%256 for i in range(128*a.blocks-17))
        padded,states=probe.run(message);assert len(states)==a.blocks+1
        records=[(states[i],padded[128*i:128*(i+1)],states[i+1]) for i in range(a.blocks)]
        print('Compiling and generating '+str(a.blocks)+' compression blocks',flush=True)
        air,traces,public,names=phase.compile_air(records);generation_seconds=time.monotonic()-started
        print('Generated; independently checking complete canonical AIR',flush=True);started=time.monotonic()
        checked=phase.l.ref.check(air,traces,public)
        evaluations=sum(len(row) for table in checked['residuals'] for row in table);del checked
        check_seconds=time.monotonic()-started
        print('Full witness checked: '+str(evaluations)+' constraints',flush=True)
        logs=[len(rows).bit_length()-1 for rows in traces]
        spec=dict(air=air,public=public,log_rows=logs,
            source_packings=[choose_packing(n,t['width']) for n,t in zip(logs,air['tables'])],
            aux_packings=[choose_packing(n,8*aux.layout(t)['aux_columns']) for n,t in zip(logs,air['tables'])],terminal_degree=64)
        assert all(n<=13 for n in logs)
        algebra.validate(spec)
        files={};roots=[];native=Kernel(a.native_library);started=time.monotonic()
        for i,(rows,packing) in enumerate(zip(traces,spec['source_packings'])):
            raw=canonical(dict(rows=rows));path=source/f'source-{i:02d}-rows.json';path.write_bytes(raw)
            files[str(path.relative_to(out))]=hashlib.sha256(raw).hexdigest()
            cache=pcs.Source(rows,packing,native);roots.append(cache.root.hex());del cache
            print('Prepared source '+str(i)+' '+names[i],flush=True)
        commit_seconds=time.monotonic()-started
        statement=canonical(dict(spec=spec,roots=roots));(out/'statement.json').write_bytes(statement)
        files['statement.json']=hashlib.sha256(statement).hexdigest()
        report=dict(status='PREPARED_FULL_WITNESS_CHECKED',blocks=a.blocks,full_witness_verified=True,
            source_constraints_evaluated=evaluations,source_rows=[len(r) for r in traces],
            table_names=names,public_field_elements=len(public),public_json_bytes=len(canonical(public)),
            minimum_public_u32_bytes=4*len(public),
            source_aux_cells=sum(len(rows)*(t['width']+8*aux.layout(t)['aux_columns']) for rows,t in zip(traces,air['tables'])),
            generation_seconds=generation_seconds,canonical_check_seconds=check_seconds,source_commit_seconds=commit_seconds,
            generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),files=files,
            scope='Actual full witness, canonical AIR interpreter and source commitments. Public state/block/result boundaries included in statement; not a compact private recursive interface. No proof yet, Lean theorem or PQ128 certification.')
        (out/'preparation.json').write_text(json.dumps(report,indent=2)+'\n')
        del traces,air,public,spec
    if a.prepare_only:return
    cmd=[sys.executable,str(Path(__file__).with_name('test_ext8_execution_reduction.py')),
        '--statement',str(out/'statement.json'),'--source-directory',str(source),'--pcs-queries',str(a.queries),
        '--terminal-profile','affine-v1','--capture-dir',str(out/'proof'),'--output',str(out/'prover-report.json')]
    print('Running full diagnostic Ext8 prover; log '+str(out/'prover.log'),flush=True)
    with (out/'prover.log').open('w') as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=True)
    print('PASS diagnostic prover; proof must still be encoded and freshly replayed',flush=True)


if __name__=='__main__':main()
