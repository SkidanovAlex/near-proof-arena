"""Witness-free table-local verifier; expected specification/root are external."""
import argparse,json
from pathlib import Path
from pq384_table_air import verify_table_local
from pq384_table_codec import decode

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('proof',type=Path);p.add_argument('spec',type=Path)
    p.add_argument('--expected-root',required=True,help='Trusted SHA384 commitment, 96 hex digits')
    p.add_argument('--binary',action='store_true');a=p.parse_args()
    if len(a.expected_root)!=96:raise ValueError('expected root length')
    root=bytes.fromhex(a.expected_root);spec=json.loads(a.spec.read_text())
    proof=decode(a.proof.read_bytes(),spec) if a.binary else json.loads(a.proof.read_text())
    if not verify_table_local(proof,spec,root):raise ValueError('proof rejected')
    print('PASS: table-local SHA384 diagnostic; no global bus or security certification')
if __name__=='__main__':main()
