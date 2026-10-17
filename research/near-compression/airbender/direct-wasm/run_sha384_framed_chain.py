"""Prove every actual SHA384 compression block and verify full-message bindings."""
import argparse,copy,hashlib,json,os,subprocess,sys,time
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--input-directory',required=True);ap.add_argument('--output-directory',required=True)
    ap.add_argument('--rs-binary',required=True);ap.add_argument('--folded-library',required=True);ap.add_argument('--fft-library',required=True);a=ap.parse_args();sys.path.append(a.reference_dir)
    import verify_sha384_framed_chain as verify
    import pq384_global_bus_codec as codec
    inp=Path(a.input_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);capture=json.loads((inp/'captured-hash.json').read_text());chain=json.loads((inp/'chain/chain.json').read_text())
    message=bytes(chain['message_bytes']);expected=bytes.fromhex(capture['expected_digest_hex']);tag=bytes.fromhex(capture['tag_hex']);parts=[bytes.fromhex(x) for x in capture['parts_hex']]
    assert message==bytes.fromhex(capture['message_hex'])==verify.frame(tag,parts,verify.PREFIX)
    assert bytes(chain['padded_bytes'])==verify.padded(message)
    assert bytes(chain['digest_bytes'])==hashlib.sha384(message).digest()==expected
    items=[];binary_bytes=0;start=time.perf_counter();env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir]);runner=Path(__file__).with_name('run_pq384_global_bus.py')
    for i in range(chain['block_count']):
        source=inp/'chain'/f'block-{i}';dest=out/f'block-{i}'
        completed=subprocess.run([sys.executable,str(runner),'--reference-dir',a.reference_dir,'--spec',str(source/'spec.json'),'--source-directory',str(source),
            '--rs-binary',a.rs_binary,'--folded-library',a.folded_library,'--fft-library',a.fft_library,'--output-dir',str(dest)],env=env,capture_output=True,text=True)
        if completed.returncode:raise RuntimeError(completed.stderr)
        statement=json.loads((dest/'statement.json').read_text());proof=json.loads((dest/'proof.json').read_text());item=dict(statement=statement,proof=proof);items.append(item)
        wire=codec.encode(proof,statement['spec'],[bytes.fromhex(x) for x in statement['roots']]);assert codec.decode(wire,statement['spec'],[bytes.fromhex(x) for x in statement['roots']])==proof
        (dest/'proof.bin').write_bytes(wire);binary_bytes+=len(wire);print(f'proved and roundtripped compression block {i+1}/{chain["block_count"]}',flush=True)
    canonical=json.loads((inp/'chain/block-0/spec.json').read_text())['air'];assert verify.verify(items,canonical,tag,parts,expected)
    (out/'chain-proof.json').write_text(json.dumps(items,separators=(',',':')))
    completed=subprocess.run([sys.executable,str(Path(verify.__file__)),str(out/'chain-proof.json'),str(inp/'captured-hash.json'),str(inp/'chain/block-0/spec.json')],env=env,check=True,capture_output=True,text=True)
    negatives=0
    def reject(v=items,t=tag,ps=parts,d=expected):
        nonlocal negatives
        try:verify.boundaries(v,canonical,t,ps,d)
        except (ValueError,KeyError,IndexError,TypeError):negatives+=1
        else:raise AssertionError('invalid full-message boundary accepted')
    reject(items[:-1]);reject(items+items[-1:]);reject(items[::-1]);reject(items[1:]+items[:1]);reject(t=tag+b'x')
    ps=copy.deepcopy(parts);ps[-1]=bytes([ps[-1][0]^1])+ps[-1][1:];reject(ps=ps);reject(d=bytes([expected[0]^1])+expected[1:])
    bad=copy.deepcopy(items);bad[0]['statement']['spec']['public'][0]=65536;reject(bad)
    bad=copy.deepcopy(items);bad[0]['statement']['spec']['air']['tables'][0]['constraints']=[];reject(bad)
    report=dict(status='PASS',message_bytes=len(message),compression_blocks=chain['block_count'],rows_per_block=128,width=6944,all_canonical_lean_constraints_evaluated=True,
        source_compression_matches=True,hashlib_match=True,full_chain_verifier=completed.stdout.strip(),chain_boundary_negative_checks=negatives,
        individually_valid_blocks_reordered_truncated_duplicated_reject=True,total_compression_proof_binary_bytes=binary_bytes,
        byte_accounting='sum of individually transported compression proofs including roots; excludes outer framing/statement/public message',
        seconds=time.perf_counter()-start,expected_digest_hex=expected.hex(),scope='Full framed hash relation; external padding/state-link checks, no multiblock AIR bus or full recursive verifier',
        source_fullproof_sha256=capture['source_proof_sha256'])
    (out/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))

if __name__=='__main__':main()
