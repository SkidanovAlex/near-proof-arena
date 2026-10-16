"""Full-envelope measurement and malformed-input checks on a retained proof."""
import argparse,json,hashlib,subprocess,sys
from pathlib import Path
import ext8_execution_codec as c


def main():
    p=argparse.ArgumentParser();p.add_argument('--capture',type=Path,required=True);p.add_argument('--statement',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--queries',type=int,required=True);a=p.parse_args()
    statement=json.loads(a.statement.read_text());spec,roots=statement['spec'],statement['roots']
    reduction=json.loads((a.capture/'reduction.json').read_text());opening=(a.capture/'proof.bin').read_bytes()
    wire=c.encode(reduction,opening,spec,roots,queries=a.queries)
    rd,op=c.decode(wire,spec,roots,queries=a.queries)
    assert rd==reduction and op==opening
    assert c.encode(rd,op,spec,roots,queries=a.queries)==wire
    negatives=[]
    cases=[('truncated',wire[:-1]),('trailing',wire+b'\0'),('version',b'BADMAGIC'+wire[8:]),('source-root',wire[:8]+bytes([wire[8]^1])+wire[9:])]
    at=8+96*len(roots)
    cases.append(('noncanonical-scalar',wire[:at]+c.v.f.P.to_bytes(4,'little')+wire[at+4:]))
    gkr_at=at+32*sum(map(len,reduction['finals']))+32*sum(len(row) for table in reduction['local'] for row in table)
    for name,pos in [('aux-root',8+48*len(roots)),('bus-final',at),('gkr-round',gkr_at),('pcs-authentication',len(wire)-1)]:
        cases.append((name,wire[:pos]+bytes([wire[pos]^1])+wire[pos+1:]))
    for name,bad in cases:
        try:c.decode(bad,spec,roots,queries=a.queries)
        except ValueError:negatives.append(name)
        else:raise AssertionError(name)
    (a.capture/'envelope.bin').write_bytes(wire)
    fresh=subprocess.run([sys.executable,str(Path(c.__file__)),str(a.capture/'envelope.bin'),str(a.statement),'--queries',str(a.queries)],text=True,capture_output=True);fresh.check_returncode()
    report=dict(fresh_verifier=fresh.stdout.strip(),status='PASS',queries=a.queries,opening_bytes=len(opening),complete_envelope_bytes=len(wire),reduction_and_framing_bytes=len(wire)-len(opening),negative_cases=negatives,roundtrip=True,sha256=hashlib.sha256(wire).hexdigest(),scope='Includes source/auxiliary commitments, bus finals, local/GKR proofs and PCS opening. Static trusted AIR/spec and external receipts excluded. Not PQ128 or full NEAR certification.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
