"""Fresh code-switch execution + unchanged same-use-root call proof verifier."""
import argparse,gzip,json
from pathlib import Path
import ext8_switch_execution_codec as codec
import sha384_call_ext8_pcs as calls
from verify_sha384_node_chunk import contract
from pq384_ext8_native import Kernel


def main():
    p=argparse.ArgumentParser()
    for key in ('call-proof','compression-proof','statement','receipt','calls','config'):p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--call-queries',type=int,required=True);p.add_argument('--native-library',type=Path);a=p.parse_args()
    def read(path):
        raw=path.read_bytes();return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)
    st,receipt,expected=read(a.statement),read(a.receipt),read(a.calls);contract(st,receipt)
    calls.decode(a.call_proof.read_bytes(),st,receipt,expected,queries=a.call_queries)
    native=Kernel(a.native_library) if a.native_library else None
    codec.decode(a.compression_proof.read_bytes(),st['spec'],st['roots'],config=read(a.config),native=native)
    print('PASS code-switch compression and same-root call-link conjunction; diagnostic security only.')

if __name__=='__main__':main()
