"""Reprove the full retained slice's opening using original source/aux roots.
Local/GKR reduction is retained and independently verified, not regenerated.
"""
import argparse,gzip,hashlib,json,subprocess,sys,tempfile,time
from pathlib import Path
import ext8_switch_execution_codec as envelope
import ext8_weighted_code_switch as switch
import ext8_weighted_code_switch_codec as codec
import ext8_commitment_profiles as commitments
from pq384_ext8_native import Kernel
from pq384_primitives import Transcript
from verify_sha384_node_chunk import contract
v=envelope.v


def read(path):
    raw=path.read_bytes();return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)


def main():
    p=argparse.ArgumentParser()
    for key in ('statement','reduction','source-directory','receipt','source-report','config','output'):p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);started=time.perf_counter()
    st,reduction,receipt,config=map(read,(a.statement,a.reduction,a.receipt,a.config));contract(st,receipt)
    params=v.opening_parameters(reduction,st['spec'],st['roots'],terminal_profile='affine-v1',commitment_profile='phase-pooled-v1')
    print('Retained local/GKR reduction verified; opening obligation derived',flush=True)
    expected=read(a.source_report)['source_sha256'];rows=[]
    for i,digest in enumerate(expected):
        raw=(a.source_directory/f'source-{i:02d}-rows.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==digest
        rows.append(json.loads(raw)['rows'])
    with tempfile.TemporaryDirectory(prefix='full-switch-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(Path(__file__).with_name('native-folded')/'kernel_ext8.rs'),'-o',str(lib)],check=True);native=Kernel(lib)
        start=time.perf_counter();sources=commitments.source_caches(st['spec'],rows,native);assert [c.root.hex() for c in sources]==st['roots']
        print('Original packed source roots reproduced',flush=True)
        t=Transcript(params[0]);alpha,gamma=v.local.draw(t,2)
        generated=[v.aux.generate(table,rs,st['spec']['public'],alpha,gamma) for table,rs in zip(st['spec']['air']['tables'],rows)]
        assert json.loads(json.dumps([x['finals'] for x in generated]))==reduction['finals']
        coordinates=[[[c for value in row for c in value] for row in x['aux_rows']] for x in generated]
        auxiliaries=commitments.auxiliary_caches(st['spec'],coordinates,native);assert [c.root.hex() for c in auxiliaries]==reduction['aux_roots']
        caches=[sources[0],auxiliaries[0],sources[3]];source_seconds=time.perf_counter()-start
        assert [c.root.hex() for c in caches]==[b['root'] for b in params[2]]
        del rows,coordinates,generated
        print('Original auxiliary roots reproduced; starting code-switch PCS',flush=True)
        start=time.perf_counter();proof=switch.prove(caches,native,*params,config);prove_seconds=time.perf_counter()-start
        (a.output/'proof.json').write_bytes(switch.stage.canonical_json(proof));print('Code-switch proof produced',flush=True)
        start=time.perf_counter();opening=codec.encode(proof,*params,config,native=native);assert codec.decode(opening,*params,config,native=native)==proof;codec_seconds=time.perf_counter()-start
        (a.output/'opening.bin').write_bytes(opening);detail=codec.breakdown(opening,*params,config,native=native)
        wire=envelope.encode(reduction,opening,st['spec'],st['roots'],config=config,native=native)
        (a.output/'compression.bin').write_bytes(wire);assert envelope.decode(wire,st['spec'],st['roots'],config=config,native=native)==(reduction,opening)
        print('Full execution envelope verified and roundtripped',flush=True)
        fresh=subprocess.run([sys.executable,envelope.__file__,'--proof',str(a.output/'compression.bin'),'--statement',str(a.statement),'--config',str(a.config),'--native-library',str(lib)],capture_output=True,text=True)
        (a.output/'fresh-execution-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode()
    for name,path in [('statement',a.statement),('reduction',a.reduction),('source-report',a.source_report)]:
        raw=path.read_bytes();(a.output/(name+'.json.gz')).write_bytes(raw if path.suffix=='.gz' else gzip.compress(raw,mtime=0))
    (a.output/'config.json').write_bytes(switch.stage.canonical_json(config))
    report=dict(status='PASS',profile=envelope.PROFILE,source_sha256=expected,retained_reduction_sha256=hashlib.sha256(a.reduction.read_bytes()).hexdigest(),source_and_aux_roots_unchanged=True,compression_opening_bytes=len(opening),compression_envelope_bytes=len(wire),reduction_and_framing_bytes=len(wire)-len(opening),breakdown=detail,source_seconds=source_seconds,prove_seconds=prove_seconds,codec_seconds=codec_seconds,total_seconds=time.perf_counter()-started,fresh_execution_verified=True,scope='Full retained SHA384 slice execution opening reproof; call conjunction measured separately. Diagnostic schedule, no code-switch extraction/proximity/QROM/PQ128 or full NEAR certificate.')
    (a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
