"""Generate/verify the complete bounded private Merkle diagnostic bundle."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import private_merkle_proof as proof
from pq384_ext8_native import Kernel
from run_pq384_gkr_bus import choose_packing
import pq384_ext8_auxiliary as aux


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source-directory',type=Path,required=True)
    ap.add_argument('--public',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--native-library',type=Path,required=True);ap.add_argument('--queries',type=int,required=True)
    ap.add_argument('--reuse-compression',action='store_true');ap.add_argument('--reuse-routing',action='store_true');args=ap.parse_args()
    out=args.output;out.mkdir(exist_ok=True,parents=True);public=json.loads(args.public.read_text())
    native=Kernel(args.native_library);source=args.source_directory
    spec=json.loads((source/'spec.json').read_text())
    spec['source_packings']=[choose_packing(n,t['width']) for n,t in zip(spec['log_rows'],spec['air']['tables'])]
    spec['aux_packings']=[choose_packing(n,8*aux.layout(t)['aux_columns']) for n,t in zip(spec['log_rows'],spec['air']['tables'])]
    hashes=[hashlib.sha256((source/f'source-{i:02d}-rows.json').read_bytes()).hexdigest() for i in range(4)]
    if args.reuse_compression:
        st=json.loads((out/'statement.json').read_text());old=json.loads((out/'prover-report.json').read_text())
        assert st['spec']==spec and old['status']=='PASS' and old['source_sha256']==hashes
        assert old['weighted_pcs']['queries']==args.queries and old['terminal_profile']=='affine-v1' and old['commitment_profile']=='separate'
    else:
        roots=[]
        for i,packing in enumerate(spec['source_packings']):
            rows=json.loads((source/f'source-{i:02d}-rows.json').read_text())['rows']
            roots.append(proof.call.pcs.Source(rows,packing,native).root.hex())
        st=dict(spec=spec,roots=roots)
        (out/'statement.json').write_bytes(proof.canonical(st))
        cmd=[sys.executable,str(Path(__file__).with_name('test_ext8_execution_reduction.py')),
             '--statement',str(out/'statement.json'),'--source-directory',str(source),'--pcs-queries',str(args.queries),
             '--terminal-profile','affine-v1','--capture-dir',str(out/'compression'),'--output',str(out/'prover-report.json')]
        with (out/'prover.log').open('w') as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=True)
    roots=st['roots'];proof.receipt(spec,roots,public)
    started=time.monotonic()
    if args.reuse_routing:
        routing_wire=(out/'routing.bin').read_bytes()
    else:
        rows=json.loads((source/'source-03-rows.json').read_text())['rows']
        cache=proof.call.pcs.Source(rows,spec['source_packings'][3],native)
        routing=proof.prove_routing(rows,spec,roots,public,cache,native,args.queries)
        routing_wire=proof.encode_routing(routing,spec,roots,public,args.queries)
        (out/'routing.bin').write_bytes(routing_wire)
        (out/'routing.json.gz').write_bytes(gzip.compress(proof.canonical(routing),mtime=0))
    assert proof.verify_routing(routing_wire,spec,roots,public,args.queries)
    routing_seconds=time.monotonic()-started
    reduction=json.loads((out/'compression/reduction.json').read_text());opening=(out/'compression/proof.bin').read_bytes()
    compressed=proof.compression.encode(reduction,opening,spec,roots,queries=args.queries,terminal_profile='affine-v1')
    wire=proof.combine(compressed,routing_wire);(out/'proof.bin').write_bytes(wire)
    (out/'trusted-spec.json').write_bytes(proof.canonical(spec));(out/'public.json').write_bytes(proof.canonical(public))
    cmd=[sys.executable,str(Path(proof.__file__)),'--proof',str(out/'proof.bin'),'--trusted-spec',str(out/'trusted-spec.json'),'--public',str(out/'public.json'),'--queries',str(args.queries)]
    started=time.monotonic();fresh=subprocess.run(cmd,capture_output=True,text=True);(out/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode();verify_seconds=time.monotonic()-started
    negatives=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,AssertionError,IndexError,KeyError):negatives.append(name)
        else:raise AssertionError('accepted '+name)
    for key,value in [('root_hex','00'*48),('index',public['index']^1),('leaf_hex','ff'*(len(public['leaf_hex'])//2))]:
        bad=dict(public);bad[key]=value
        reject('public-'+key,lambda bad=bad:proof.verify_routing(routing_wire,spec,roots,bad,args.queries))
    reject('routing-truncated',lambda:proof.verify_routing(routing_wire[:-1],spec,roots,public,args.queries))
    reject('routing-trailing',lambda:proof.verify_routing(routing_wire+b'\0',spec,roots,public,args.queries))
    changed=bytearray(routing_wire);changed[8]^=1
    reject('routing-scalar',lambda:proof.verify_routing(bytes(changed),spec,roots,public,args.queries))
    wrongroots=list(roots);wrongroots[3]='00'*48
    reject('routing-other-use-root',lambda:proof.verify_routing(routing_wire,spec,wrongroots,public,args.queries))
    reject('routing-other-queries',lambda:proof.verify_routing(routing_wire,spec,roots,public,args.queries+1))
    reject('bundle-missing-routing',lambda:proof.verify(proof.combine(compressed,b''),spec,public,args.queries))
    bad=bytearray(wire);bad[16+8]^=1
    reject('bundle-compression-root',lambda:proof.verify(bytes(bad),spec,public,args.queries))
    public_bytes=(out/'public.json').stat().st_size
    report=dict(status='COMPLETE_BOUNDED_MERKLE_DIAGNOSTIC_VERIFIED',complete_bounded_merkle_verifier=True,
        complete_recursive_pcs_verifier=False,quantum_security_certified=False,queries=args.queries,
        compression_blocks=proof.route.compile_routes(public)['use_count'],depth=public['leaf_count'].bit_length()-1,
        compression_envelope_bytes=len(compressed),routing_proof_bytes=len(routing_wire),bundle_framing_bytes=16,
        proof_bytes=len(wire),public_statement_json_bytes=public_bytes,proof_and_public_bytes=len(wire)+public_bytes,
        static_trusted_spec_json_bytes=(out/'trusted-spec.json').stat().st_size,original_private_path_bytes=48*(public['leaf_count'].bit_length()-1),
        beats_raw_path_bytes=len(wire)<48*(public['leaf_count'].bit_length()-1),
        original_path_required_by_verifier=False,original_hash_messages_required_by_verifier=False,full_trace_required_by_verifier=False,zero_knowledge_claimed=False,
        fresh_verifier_passed=True,negative_cases=negatives,routing_prove_encode_verify_seconds=routing_seconds,
        fresh_verify_seconds=verify_seconds,compression_reused=args.reuse_compression,routing_reused=args.reuse_routing,source_sha256=hashes,
        scope='Complete executable bounded Merkle verification via compression AIR and same-use-root routing GKR/PCS. Trusted static canonical AIR/spec excluded from wire; public statement counted separately. No original sibling path, expected call messages or full use trace is a verifier input. PCS openings may leak witness information; no zero-knowledge claim. Ext8/query diagnostic, not a soundness/PQ128 certificate, full PCS recursion, 1Pgas NEAR proof, or formal route-compiler correctness theorem.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
