"""Exact compact GKR wire sections, checked against an already verified wire."""
import argparse,json,struct,sys
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--proof-directory',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    from pq384_compact_weighted_codec import Writer
    from pq384_compact_gkr_bus_codec import MAGIC
    d=Path(a.proof_directory);pr=json.loads((d/'proof.json').read_text());st=json.loads((d/'statement.json').read_text());wire=(d/'proof.bin').read_bytes();w=Writer();w.raw(MAGIC+b''.join(bytes.fromhex(v) for v in st['roots']))
    for r,fs in zip(pr['aux_roots'],pr['finals']):w.raw(bytes.fromhex(r));w.vector(fs)
    for rounds in pr['tables']:
        for row in rounds:w.vector([row[0]]+row[2:])
    w.align();prefix=len(w.data)
    for layer in pr['gkr']['layers']:
        for row in layer['rounds']:w.vector([row[0],row[2]])
        w.vector(layer['inputs'])
    w.align();gkr=len(w.data)-prefix;assert bytes(w.data)==wire[:len(w.data)]
    opening=struct.unpack('<Q',wire[len(w.data):len(w.data)+8])[0];assert len(wire)==prefix+gkr+8+opening
    report=dict(status='PASS',whole_binary_bytes=len(wire),roots_bus_finals_and_AIR_bytes=prefix,gkr_bytes=gkr,opening_framing_bytes=8,weighted_joint_opening_bytes=opening,source_roots_included=len(st['roots']),bus_finals=sum(map(len,pr['finals'])),gkr_layers=len(pr['gkr']['layers']),gkr_quadratic_rounds=sum(len(v['rounds']) for v in pr['gkr']['layers']),scope='Exact accepted-wire accounting; this analyzer does not replace the complete verifier.')
    (d/'compact-size.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
