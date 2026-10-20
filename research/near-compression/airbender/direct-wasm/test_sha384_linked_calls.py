"""Real retained-proof integration and same-root rejection regressions."""
import argparse,copy,gzip,hashlib,json,subprocess,sys,time
from pathlib import Path
import verify_sha384_linked_calls as v


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    base=package/'results/ext8-node-batch'
    statement=json.loads(gzip.decompress((base/'statement.json.gz').read_bytes()))
    receipt=json.loads((base/'expected-use.json').read_text())
    # Runtime-checker fixture retains all active use rows; canonical padding is zero.
    cases=json.loads(gzip.decompress((package/'results/ext8-call-check/cases.json.gz').read_bytes()))
    positive=[c for c in cases if c['expected']]
    rows=positive[0]['rows']+[[0]*179 for _ in range((1<<statement['spec']['log_rows'][3])-receipt['use_count'])]
    assert all(c['rows']==positive[0]['rows'] for c in positive)
    calls=[dict(message_hex=bytes(c['message']).hex(),ordinals=c['ordinals'],digest_hex=hashlib.sha384(bytes(c['message'])).hexdigest()) for c in positive]
    write=lambda name,x:(out/name).write_text(json.dumps(x,separators=(',',':'))+'\n')
    write('rows.json',rows);write('calls.json',calls);write('statement.json',statement)
    started=time.perf_counter()
    command=[sys.executable,str(Path(v.__file__)),'--proof',str(base/'proof.bin'),'--statement',str(out/'statement.json'),
        '--receipt',str(base/'expected-use.json'),'--rows',str(out/'rows.json'),'--calls',str(out/'calls.json'),'--package',str(package)]
    result=subprocess.run(command,text=True,capture_output=True)
    (out/'fresh-verifier.log').write_text(result.stdout+result.stderr);result.check_returncode()
    seconds=time.perf_counter()-started
    negatives=[]
    def reject(name,edit,semantic=False):
        rr,cc=copy.deepcopy(rows),copy.deepcopy(calls);edit(rr,cc)
        try:
            if semantic:v.verify((base/'proof.bin').read_bytes(),statement,receipt,rr,cc,package)
            else:v.linked_cases(statement,receipt,rr,cc)
        except (ValueError,subprocess.CalledProcessError):negatives.append(name)
        else:raise AssertionError('accepted '+name)
    for col,name in [(2,'node-id'),(3,'input-state'),(35,'block'),(127,'hidden-output-state'),(131,'digest-field')]:
        reject(name,lambda r,c,col=col:r[0].__setitem__(col,r[0][col]^1))
    reject('padding-row',lambda r,c:r[-1].__setitem__(0,1))
    reject('noncanonical-field',lambda r,c:r[0].__setitem__(3,v.P))
    reject('reordered-use-rows',lambda r,c:(r[0].__setitem__(slice(2,None),rows[1][2:]),r[1].__setitem__(slice(2,None),rows[0][2:])))
    reject('missing-call',lambda r,c:c.pop())
    reject('reordered-calls',lambda r,c:c.reverse())
    reject('duplicate-ordinal',lambda r,c:c[0]['ordinals'].__setitem__(0,1))
    reject('wrong-expected-digest',lambda r,c:c[0].__setitem__('digest_hex','00'*48))
    reject('wrong-message-same-length',lambda r,c:c[0].__setitem__('message_hex',('00' if c[0]['message_hex'][:2]!='00' else '01')+c[0]['message_hex'][2:]),True)
    wire=bytearray((base/'proof.bin').read_bytes());wire[0]^=1
    try:v.verify(bytes(wire),statement,receipt,rows,calls,package)
    except ValueError:negatives.append('invalid-compression-proof')
    else:raise AssertionError('compression proof verification skipped')
    # Account for disclosed base-field words, caller configuration, receipt and
    # the actual serialized JSON form separately; static AIR remains external.
    report=dict(status='PASS',calls=len(calls),use_rows=receipt['use_count'],padded_rows=len(rows),width=179,
        fresh_process_verified=True,verification_seconds=seconds,negative_cases=negatives,
        proof_bytes=(base/'proof.bin').stat().st_size,disclosed_rows_u32_bytes=len(rows)*179*4,
        disclosed_rows_json_bytes=(out/'rows.json').stat().st_size,trusted_calls_json_bytes=(out/'calls.json').stat().st_size,
        receipt_json_bytes=(base/'expected-use.json').stat().st_size,
        total_proof_rows_calls_receipt_json_bytes=sum(f.stat().st_size for f in [base/'proof.bin',out/'rows.json',out/'calls.json',base/'expected-use.json']),
        use_root=receipt['use_root'],files={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in [base/'proof.bin',out/'rows.json',out/'calls.json',out/'statement.json',Path(v.__file__)]},
        scope='Diagnostic verified conjunction: retained Q8/Ext4 compression proof, independently reconstructed disclosed-use root, exact external call coverage, proved Lean full-state/padding checker, external expected digests. Static AIR/spec external. No zero knowledge, succinct recursive authentication, operand provenance, full verifier recursion or quantum-security claim.')
    write('report.json',report);print(json.dumps(report,indent=2))

if __name__=='__main__':main()
