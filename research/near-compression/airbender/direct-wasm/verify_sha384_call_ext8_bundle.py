"""Verified diagnostic conjunction; no source rows or prover cache input."""
import argparse,json
from pathlib import Path
import sha384_call_ext8_pcs as calls
from verify_sha384_node_chunk import verify as compression

def main():
    p=argparse.ArgumentParser()
    for key in ['call-proof','compression-proof','statement','receipt','calls']:p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--queries',type=int,required=True)
    p.add_argument('--compression-format',choices=('ext4','ext8'),default='ext4')
    a=p.parse_args();read=lambda f:json.loads(f.read_text())
    st,receipt,expected=read(a.statement),read(a.receipt),read(a.calls)
    calls.decode(a.call_proof.read_bytes(),st,receipt,expected,queries=a.queries)
    if a.compression_format=='ext4':compression(a.compression_proof.read_bytes(),st,receipt)
    else:
        from verify_sha384_node_chunk import contract
        import ext8_execution_codec
        contract(st,receipt)
        ext8_execution_codec.decode(a.compression_proof.read_bytes(),st['spec'],st['roots'],queries=a.queries)
    print('PASS same-root call-link and compression proof conjunction; no disclosed rows; diagnostic security only.')

if __name__=='__main__':main()
