"""Retain reconstruction certificates after full fixed-profile proof verification."""
import sys,json,hashlib
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import check_terminal_rebuild_certificates as c
from check_whir_handoff import add,sub,mul
from verify_whir_toy import ZERO,ONE
from native_folded_v2 import compile_weighted
from table_constraint_whir import selectors
from pq384_shift import eq_point
import pq384_global_bus as bus
for k,v in dict(OPS={'add':add,'sub':sub,'mul':mul},ZERO=ZERO,ONE=ONE,mul=mul,compile_weighted=compile_weighted,selectors=selectors,eq_point=eq_point,bus=bus).items():setattr(c,k,v)
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--capture',type=Path,required=True);ap.add_argument('--input-log',type=int,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--bundle',type=Path,required=True);cli=ap.parse_args()
circuit,profile,args=c.capture(cli.capture,input_log=cli.input_log)
c.require(json.loads(json.dumps(circuit))==json.loads(cli.bundle.read_text())['circuit'],'retained circuit mismatch')
cert=c.produce(circuit,args);counts=c.validate(circuit,args,cert);print(counts)
cli.output.write_text(json.dumps(cert,separators=(',',':'))+'\n')

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
expected_batch=dict(rho=list(args[-1]),weights=[list(eq_point(t['tau'],t['point'])) for t in args[-2]],claims=[t['claim'] for t in args[-2]])
report=dict(expected_batch=expected_batch,status='PASS',capture=str(cli.capture),input_log=cli.input_log,profile=profile,counts=counts,
    statement_sha256=sha(cli.capture/'statement.json'),proof_sha256=sha(cli.capture/'proof.json'),
    bundle_sha256=sha(cli.bundle),rebuild_sha256=sha(cli.output),
    scope='Full fixed-profile proof verified before replay; reconstructed circuit equals retained bundle. Structural certificate validation, not security certification.')
cli.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
