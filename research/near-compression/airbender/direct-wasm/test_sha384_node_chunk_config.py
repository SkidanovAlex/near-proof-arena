"""Bounded exporter rejects invalid declared dimensions, capacities and source records."""
import argparse,copy,hashlib,json,subprocess,time
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--fixture-source',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--lean-package',required=True);a=p.parse_args();src=Path(a.fixture_directory);cfg=json.loads((src/'config.json').read_text());out=src/'config-negatives';out.mkdir(exist_ok=True)
    tests=[('zero-node-count',lambda c:c.__setitem__('count',0),'bounded chunk config'),('node-count-over-cap',lambda c:c.__setitem__('count',26),'bounded chunk config'),('global-field-wrap',lambda c:c.__setitem__('base',2013265920),'bounded chunk config'),('zero-fanout-bits',lambda c:c.__setitem__('fanout_bits',0),'bounded chunk config'),('too-many-fanout-bits',lambda c:c.__setitem__('fanout_bits',14),'bounded chunk config'),('fanout-overflow',lambda c:c.__setitem__('fanout_bits',2),'fanout capacity'),('empty-use-list',lambda c:c.__setitem__('uses',[]),'bounded chunk config'),('use-outside-global-interval',lambda c:c['uses'].__setitem__(0,c['base']-1),'use global ID outside interval'),('noncanonical-state-word',lambda c:c['nodes'][0].__setitem__(0,1<<64),'noncanonical node bytes/words'),('wrong-full-output-state',lambda c:c['nodes'][0].__setitem__(143,c['nodes'][0][143]^1),'actual node compression mismatch')]
    results=[];start=time.perf_counter()
    for name,edit,error in tests:
        value=copy.deepcopy(cfg);edit(value);path=out/(name+'.json');path.write_text(json.dumps(value,separators=(',',':')));dest=out/name
        proc=subprocess.run(['lake','env','lean','--run',a.fixture_source,str(path),str(dest)],cwd=a.lean_package,text=True,capture_output=True)
        assert proc.returncode!=0 and error in proc.stdout+proc.stderr,(name,proc.stdout,proc.stderr)
        assert not (dest/'spec.json').exists() and not list(dest.glob('source-*-rows.json')),name
        results.append(dict(name=name,expected_error=error,rejected_before_trace_export=True))
    report=dict(status='PASS',cases=results,elapsed_seconds=time.perf_counter()-start,source_sha256=hashlib.sha256(Path(a.fixture_source).read_bytes()).hexdigest())
    (src/'config-negative-checks.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
