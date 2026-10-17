"""Resume separate affine-v1 PCS from a checked reduction, rebuilding root-bound caches.
Replays local/GKR verification, never their prover. Diagnostic security only.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import pq384_ext8_auxiliary_base as aux
import pq384_ext8_local as local
import pq384_ext8_packed_prover as packed
import pq384_ext8_weighted_codec as codec
import verify_ext8_execution as verifier
from pq384_ext8_native import Kernel
from pq384_primitives import Transcript
import ext8_commitment_profiles as commitments


def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(path):
    raw=path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)


def checked_parameters(checkpoint,statement,queries):
    raw=gzip.decompress((checkpoint/'reduction.json.gz').read_bytes())
    reduction=json.loads(raw);opening_path=checkpoint/'opening.json'
    if not opening_path.exists():opening_path=checkpoint/'opening.json.gz'
    opening=read(opening_path);status=read(checkpoint/'status.json')
    if hashlib.sha256(raw).hexdigest()!=status['reduction_sha256']:raise ValueError('checkpoint reduction hash')
    if hashlib.sha256(canonical(opening)).hexdigest()!=status['opening_sha256']:raise ValueError('checkpoint opening hash')
    if opening['queries']!=queries:raise ValueError('external query count')
    parameters=verifier.opening_parameters(reduction,statement['spec'],statement['roots'],terminal_profile='affine-v1')
    expected=(bytes.fromhex(opening['statement']),bytes.fromhex(opening['parent']),opening['branches'],opening['claim'])
    if parameters[:2]!=expected[:2] or canonical(parameters[2:])!=canonical(expected[2:]):raise ValueError('derived opening mismatch')
    return reduction,opening,parameters


def reconstruct(statement,reduction,source_directory,native):
    spec=statement['spec'];st=commitments.statement(spec,[bytes.fromhex(r) for r in statement['roots']],'separate')
    alpha,gamma=local.draw(Transcript(st),2);sources=[];auxiliaries=[]
    for i,table in enumerate(spec['air']['tables']):
        path=source_directory/f'source-{i:02d}-rows.json'
        if not path.exists():path=path.with_suffix('.json.gz')
        rows=read(path)['rows'];source=packed.p.Source(rows,spec['source_packings'][i],native)
        if source.root.hex()!=statement['roots'][i]:raise ValueError('reconstructed source root')
        generated=aux.generate(table,rows,spec['public'],alpha,gamma)
        if canonical(generated['finals'])!=canonical(reduction['finals'][i]):raise ValueError('reconstructed auxiliary finals')
        coordinates=[[c for value in row for c in value] for row in generated['aux_rows']]
        auxiliary=packed.p.Source(coordinates,spec['aux_packings'][i],native)
        if auxiliary.root.hex()!=reduction['aux_roots'][i]:raise ValueError('reconstructed auxiliary root')
        sources.append(source);auxiliaries.append(auxiliary)
        del rows,generated,coordinates
        print('Rebuilt source/auxiliary cache '+str(i),flush=True)
    return sources+auxiliaries


def main():
    ap=argparse.ArgumentParser()
    for name in ('checkpoint','statement','source-directory','native-library','output-dir'):ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--queries',type=int,required=True);a=ap.parse_args()
    started=time.monotonic();statement=read(a.statement)
    reduction,opening,parameters=checked_parameters(a.checkpoint,statement,a.queries)
    native=Kernel(a.native_library);all_caches=reconstruct(statement,reduction,a.source_directory,native)
    indices=opening['cache_indices']
    if len(indices)!=len(parameters[2]) or any(type(i)is not int or not 0<=i<len(all_caches) for i in indices):raise ValueError('cache indices')
    caches=[all_caches[i] for i in indices]
    for cache,b in zip(caches,parameters[2]):
        if cache.root.hex()!=b['root']:raise ValueError('cache branch root')
    reconstruction_seconds=time.monotonic()-started
    started=time.monotonic();proof=packed.prove(caches,native,*parameters,queries=a.queries)
    wire=codec.encode(proof,*parameters,queries=a.queries,shared_sources=True)
    a.output_dir.mkdir(parents=True,exist_ok=True)
    (a.output_dir/'proof.bin').write_bytes(wire)
    (a.output_dir/'reduction.json').write_bytes(canonical(reduction))
    (a.output_dir/'proof.json').write_bytes(canonical(proof))
    # Fresh process derives its own opening descriptors from the external statement.
    statement_path=a.output_dir/'statement.json';statement_path.write_bytes(canonical(statement))
    fresh=subprocess.run([sys.executable,verifier.__file__,'--reduction',str(a.output_dir/'reduction.json'),
        '--opening',str(a.output_dir/'proof.bin'),'--statement',str(statement_path),'--queries',str(a.queries),
        '--terminal-profile','affine-v1'],capture_output=True,text=True)
    (a.output_dir/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode()
    report=dict(status='RESUMED_PCS_FRESHLY_VERIFIED',queries=a.queries,opening_bytes=len(wire),
        opening_sha256=hashlib.sha256(wire).hexdigest(),reconstruction_seconds=reconstruction_seconds,
        pcs_encode_and_verify_seconds=time.monotonic()-started,
        scope='Reconstructed root-bound source/aux caches and replayed local/GKR verification. Local/GKR proving not repeated. Diagnostic only; no cryptographic soundness or PQ128 claim.')
    (a.output_dir/'resume-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)


if __name__=='__main__':main()
