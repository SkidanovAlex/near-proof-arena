"""Verified diagnostic conjunction; no source rows or prover cache input."""
import ext8_commitment_profiles as commitments
import argparse,json
import ext8_terminal_profiles as profiles
from pathlib import Path
import sha384_call_ext8_pcs as calls
from verify_sha384_node_chunk import verify as compression

def main():
    p=argparse.ArgumentParser()
    for key in ['call-proof','compression-proof','statement','receipt','calls']:p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--queries',type=int,required=True)
    p.add_argument('--compression-format',choices=('ext4','ext8'),default='ext4')
    p.add_argument("--terminal-profile",choices=profiles.PROFILES,default="baseline")
    p.add_argument("--commitment-profile",choices=commitments.PROFILES,default="separate")
    a=p.parse_args();
    if a.compression_format=="ext4" and (a.terminal_profile!="baseline" or a.commitment_profile!="separate"):p.error("terminal profile requires Ext8 compression")
    read=lambda f:json.loads(f.read_text())
    st,receipt,expected=read(a.statement),read(a.receipt),read(a.calls)
    calls.decode(a.call_proof.read_bytes(),st,receipt,expected,queries=a.queries)
    if a.compression_format=='ext4':compression(a.compression_proof.read_bytes(),st,receipt)
    else:
        from verify_sha384_node_chunk import contract
        import ext8_execution_codec
        contract(st,receipt)
        ext8_execution_codec.decode(a.compression_proof.read_bytes(),st['spec'],st['roots'],queries=a.queries,terminal_profile=a.terminal_profile,commitment_profile=a.commitment_profile)
    print('PASS same-root call-link and compression proof conjunction; no disclosed rows; diagnostic security only.')

if __name__=='__main__':main()
