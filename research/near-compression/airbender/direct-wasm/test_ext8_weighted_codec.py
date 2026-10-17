"""Retained weighted opening binary codec and adversarial decode checks."""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path
import pq384_ext8_weighted_codec as c

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--capture',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--verify-only',action='store_true');args=ap.parse_args()
    cfg=json.loads((args.capture/'opening.json').read_text());params=(bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']),cfg['branches'],cfg['claim']);q=cfg['queries']
    if args.verify_only:
        assert c.verify((args.capture/'proof.bin').read_bytes(),*params,queries=q);print('PASS fresh weighted Ext8 binary');return
    proof=json.loads((args.capture/'proof.json').read_text());wire=c.encode(proof,*params,queries=q)
    assert c.decode(wire,*params,queries=q)==proof
    assert c.verify(wire,*params,queries=q)
    detail=c.breakdown(proof,*params,queries=q);assert detail['total_bytes']==len(wire)
    (args.capture/'proof.bin').write_bytes(wire)
    fresh=subprocess.run([sys.executable,__file__,'--capture',str(args.capture),'--verify-only'],check=True,capture_output=True,text=True)
    rejected=[]
    cases=[('version',b'BADMAGIC'+wire[8:]),('truncated',wire[:-1]),('trailing',wire+b'\0'),
        ('noncanonical',wire[:8]+c.p.f.P.to_bytes(4,'little')+wire[12:]),
        ('changed-header',wire[:40]+bytes([wire[40]^1])+wire[41:]),
        ('changed-leaf',wire[:detail['header_bytes']]+bytes([wire[detail['header_bytes']]^1])+wire[detail['header_bytes']+1:]),
        ('changed-sibling',wire[:-1]+bytes([wire[-1]^1]))]
    for name,data in cases:
        try:c.verify(data,*params,queries=q)
        except ValueError:rejected.append(name)
        else:raise AssertionError('accepted '+name)
    try:c.verify(wire,*params,queries=q-1)
    except ValueError:rejected.append('changed-query-budget')
    else:raise AssertionError('accepted changed query budget')
    report=dict(status='PASS',queries=q,opening_bytes=len(wire),opening_json_bytes=(args.capture/'proof.json').stat().st_size,
        sha256=hashlib.sha256(wire).hexdigest(),fresh_process=fresh.stdout.strip(),rejections=rejected,breakdown=detail,
        scope='Lossless canonical weighted Ext8 multiproof transport; external statement/parent/roots/weights/claim required. Opening size only, excluding local/GKR/public envelope. No formal codec/refinement or quantum security certification.')
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='breakdown'}))
if __name__=='__main__':main()
