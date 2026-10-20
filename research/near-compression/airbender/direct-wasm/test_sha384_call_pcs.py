"""Actual same-root call-link proof without disclosed verifier rows."""
import argparse,gzip,hashlib,json,subprocess,sys,time
from pathlib import Path
import sha384_call_pcs as cp
from pq384_source_cache import SourceCache
from pq384_native_fft import NativeFFT
from pq384_gkr4_native import Kernel


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True)
    p.add_argument('--rs-binary',required=True);p.add_argument('--fft-library',required=True);p.add_argument('--gkr-library',required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];source=package/'results/ext8-linked-calls';out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    read=lambda f:json.loads(f.read_text())
    statement=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()));expected=read(package/'results/ext8-node-batch/expected-use.json')
    rows=read(source/'rows.json');calls=read(source/'calls.json');spec=statement['spec'];cache=out/'use-cache'
    request=out/'commit.json';request.write_bytes(cp.canonical(dict(rows=rows,packing=spec['source_packings'][3],indices=[],cache_directory=str(cache))))
    subprocess.run([a.rs_binary,str(request),str(out/'commit-result.json')],check=True,capture_output=True)
    assert read(cache/'manifest.json')['root_hex']==expected['use_root']
    started=time.perf_counter()
    with SourceCache(cache,expected_root=bytes.fromhex(expected['use_root']),log_rows=spec['log_rows'][3],width=179,packing=spec['source_packings'][3]) as data:
        proof=cp.prove(rows,statement,expected,calls,data,NativeFFT(a.fft_library),Kernel(a.gkr_library))
    proving=time.perf_counter()-started;started=time.perf_counter()
    wire=cp.encode(proof,statement,expected,calls);decoded=cp.decode(wire,statement,expected,calls)
    assert cp.canonical(decoded)==cp.canonical(proof)
    (out/'proof.bin').write_bytes(wire);(out/'proof.json').write_bytes(cp.canonical(proof));(out/'statement.json').write_bytes(cp.canonical(statement))
    verification=time.perf_counter()-started
    command=[sys.executable,str(Path(__file__).with_name('verify_sha384_call_pcs_bundle.py')),
        '--call-proof',str(out/'proof.bin'),'--compression-proof',str(package/'results/ext8-node-batch/proof.bin'),
        '--statement',str(out/'statement.json'),'--receipt',str(package/'results/ext8-node-batch/expected-use.json'),'--calls',str(source/'calls.json')]
    result=subprocess.run(command,text=True,capture_output=True);(out/'fresh-verifier.log').write_text(result.stdout+result.stderr);result.check_returncode()
    negatives=[]
    def reject(name,wire2=wire,cs=calls):
        try:cp.decode(wire2,statement,expected,cs)
        except (ValueError,KeyError):negatives.append(name)
        else:raise AssertionError(name)
    reject('truncated',wire[:-1]);reject('trailing',wire+b'\0')
    changed=bytearray(wire);changed[8]^=1;reject('gkr-coefficient',bytes(changed))
    changed=bytearray(wire);changed[-1]^=1;reject('pcs-authentication',bytes(changed))
    changed=json.loads(json.dumps(calls));changed[0]['digest_hex']='00'*48;reject('external-digest',cs=changed)
    changed=json.loads(json.dumps(calls));changed[0]['message_hex']='00'+changed[0]['message_hex'][2:];reject('external-message',cs=changed)
    reject('call-order',cs=list(reversed(calls)))
    layout,_,_,equations=cp.compile_layout(statement,expected,calls)
    # Independently check compiler coverage on canonical base rows, before PCS.
    n=len(rows);private=[cp.g.base(rows[r][c]) if c<179 else cp.g.ZERO for c in range(256) for r in range(n)]
    assert cp.g.values(layout,private)[-1][layout['root']]==cp.g.ZERO
    source_mutations=[]
    for row,col,name in [(0,3,'IV'),(0,35,'message-block'),(0,127,'hidden-chaining-output'),
                         (1,31,'hidden-chaining-input'),(1,131,'final-digest')]:
        bad=list(private);bad[row+n*col]=cp.g.add(bad[row+n*col],cp.g.ONE)
        assert any(cp.g.sub(bad[x],bad[y] if y is not None else cp.g.base(k))!=cp.g.ZERO for x,y,k in equations)
        assert cp.g.values(layout,bad)[-1][layout['root']]!=cp.g.ZERO
        source_mutations.append(name)
    compression_bytes=(package/'results/ext8-node-batch/proof.bin').stat().st_size
    report=dict(status='PASS',call_count=len(calls),equations=len(equations),input_capacity=layout['private_capacity'],gkr_layers=len(layout['layers']),
        call_proof_bytes=len(wire),compression_proof_bytes=compression_bytes,combined_proof_bytes=len(wire)+compression_bytes,
        trusted_calls_json_bytes=(source/'calls.json').stat().st_size,receipt_json_bytes=(package/'results/ext8-node-batch/expected-use.json').stat().st_size,
        combined_proofs_calls_receipt_bytes=len(wire)+compression_bytes+(source/'calls.json').stat().st_size+(package/'results/ext8-node-batch/expected-use.json').stat().st_size,
        prover_seconds=proving,encode_decode_seconds=verification,fresh_conjunction_verified=True,disclosed_row_bytes=0,
        negative_cases=negatives,source_mutation_checks=source_mutations,proof_sha256=hashlib.sha256(wire).hexdigest(),
        scope='Same committed use root for call-link GKR/PCS and compression proof. Caller fixes message bytes, digests and ordered use ordinals. Q8/Ext4 diagnostic; no 128-bit security, QROM, compiler refinement, full recursive verifier or zero-knowledge claim; static AIR/spec external.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
