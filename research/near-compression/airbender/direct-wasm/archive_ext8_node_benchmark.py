"""Archive completed diagnostic node-batch evidence; refuses incomplete runs."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil


def timing(path):
    text=path.read_text();assert 'Exit status: 0' in text
    wall=re.search(r'Elapsed \(wall clock\) time .*: ([\d:.]+)',text).group(1)
    seconds=0.0
    for part in wall.split(':'):seconds=seconds*60+float(part)
    rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',text).group(1))
    return dict(wall_seconds=seconds,peak_rss_kib=rss)


def main():
    p=argparse.ArgumentParser();p.add_argument('--fixture',type=Path,required=True);p.add_argument('--proof',type=Path,required=True);p.add_argument('--time-prefix',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    report=json.loads((a.proof/'chunk-report.json').read_text());assert report['status']=='PASS' and report['fresh_process_verify']
    checks=json.loads((a.fixture/'checks.json').read_text());assert checks['status']=='PASS'
    a.output.mkdir(parents=True,exist_ok=True)
    for name in ('config.json','selection.json','checks.json'):shutil.copyfile(a.fixture/name,a.output/name)
    for name in ('proof.bin','expected-use.json','chunk-report.json','report.json','fresh-verifier.log'):shutil.copyfile(a.proof/name,a.output/name)
    # Canonical statement needed for standalone verification; compress transport only.
    (a.output/'statement.json.gz').write_bytes(gzip.compress((a.proof/'statement.json').read_bytes(),mtime=0))
    times={key:timing(Path(str(a.time_prefix)+suffix)) for key,suffix in [('export','-export.time'),('reference_checks','-check.time'),('diagnostic_proof_pipeline','-proof.time')]}
    manifest=dict(status='COMPLETED_DIAGNOSTIC_BATCH',timings=times,
        files={f.name:dict(bytes=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest()) for f in sorted(a.output.iterdir()) if f.is_file() and f.name!='benchmark.json'},
        scope='Measured24-node compression/routing component from Ext8 inner verifier capture. Outer prover remains Q8/Ext4 diagnostic. '
              'Proof pipeline includes setup/prover and repeated verification; not pure proving latency. '
              'Expected ordered-use root external. Full call provenance/cross-chunk aggregation/secure recursion excluded. '
              'One batch is not representative throughput for every DAG node or full1Pgas execution.')
    (a.output/'benchmark.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(times,indent=2))

if __name__=='__main__':main()
