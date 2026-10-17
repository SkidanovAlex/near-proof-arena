"""Hash-work census of the complete retained switch fixture verifier.
This is an implementation workload measurement, not a recursive proof.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
from measure_ext8_recursive_hash_work import measure, frame
import pq384_primitives as h
import ext8_switch_execution_codec as codec
import sha384_call_ext8_pcs as calls
from verify_sha384_node_chunk import contract
from pq384_ext8_native import Kernel

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--native-library',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    base=ROOT/'results/ext8-switch-execution-q309'
    paths=dict(compression=base/'compression.bin',statement=base/'statement.json.gz',
        config=base/'config.json',receipt=ROOT/'results/ext8-affine-q309/receipt.json',
        calls=ROOT/'results/ext8-linked-calls/calls.json',call_proof=ROOT/'results/call-ext8-shared-q309/proof.bin')
    def read(path):
        raw=path.read_bytes()
        return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)
    statement,receipt,expected=read(paths['statement']),read(paths['receipt']),read(paths['calls'])
    config=read(paths['config'])
    wire,call_wire=paths['compression'].read_bytes(),paths['call_proof'].read_bytes()
    native=Kernel(args.native_library)
    for size in (0,1,63,64,111,112,127,128,255):
        tag=b'measurement/check';parts=(bytes(size),b'x')
        assert hashlib.sha384(frame(tag,parts)).digest()==h.hash_parts(tag,*parts)
    def verify():
        contract(statement,receipt)
        calls.decode(call_wire,statement,receipt,expected,queries=309)
        codec.decode(wire,statement['spec'],statement['roots'],config=config,native=native)
        return True
    measured=measure(verify)
    gadget_path=ROOT/'results/sha384-compression-baseline/fixture-report.json'
    gadget=read(gadget_path)
    assert gadget['formal_air_evaluation'] and (gadget['rows'],gadget['width'])==(128,6944)
    trace={}
    for name in ('blocks','unique_blocks'):
        blocks=measured['totals'][name]
        cells=blocks*gadget['rows']*gadget['width']
        trace[name]=dict(compression_blocks=blocks,rows=blocks*gadget['rows'],base_field_cells=cells,
            dense_u32_bytes=cells*4,dense_u32_gib=cells*4/2**30)
    report=dict(status='FULL_FIXTURE_VERIFIER_HASH_WORK_MEASURED',fresh_verifier_passed=True,
        compression_envelope_bytes=len(wire),call_proof_bytes=len(call_wire),measurement=measured,
        current_gadget_accounting=trace,
        scope='Actual latest switch fixture contract, call-link decoder and compression envelope decoder, including local/GKR and PCS verification. Counts pq384_primitives.hash_parts calls and their exact framing. Static statement/configuration are externally supplied. This is not full NEAR verification or a recursive proof. Unique sharing requires proved routing/equality constraints. Gadget dense bytes are arithmetic estimates, not measured RAM, runtime or outer proof size. No PQ128 certification.',
        input_sha256={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths.values()},
        source_sha256={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in
            (Path(__file__),Path(__file__).with_name('measure_ext8_recursive_hash_work.py'),gadget_path)},
        native_library_sha256=hashlib.sha256(args.native_library.read_bytes()).hexdigest())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(totals=measured['totals'],gadget_accounting=trace),indent=2))


if __name__=='__main__':main()
