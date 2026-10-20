"""Audit a fresh verifier run's data-file reads: only proof/spec/public allowed."""
import argparse
import json
from pathlib import Path
import sys


def main():
    p=argparse.ArgumentParser()
    for name in ('proof','trusted-spec','public'):p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--queries',type=int,required=True);a=p.parse_args()
    permitted={path.resolve() for path in (a.proof,a.trusted_spec,a.public)};reads=set()
    def audit(event,args):
        if event!='open' or not isinstance(args[0],str):return
        path=Path(args[0]).resolve();mode=args[1]
        if isinstance(mode,str) and any(x in mode for x in ('w','a','+')):raise RuntimeError('verifier wrote a file')
        if path.suffix in ('.json','.gz','.bin'):
            if path not in permitted:raise RuntimeError('unexpected verifier data input: '+str(path))
            reads.add(path)
    sys.dont_write_bytecode=True
    sys.addaudithook(audit)
    import private_merkle_proof as proof
    assert proof.verify(a.proof.read_bytes(),json.loads(a.trusted_spec.read_text()),json.loads(a.public.read_text()),a.queries)
    assert reads==permitted
    print(json.dumps(dict(status='PASS',data_files_read=sorted(path.name for path in reads),
        original_path_or_trace_data_read=False,scope='Observed fresh verifier data-file audit. Code/library imports allowed; no confidentiality or formal information-flow claim.')))


if __name__=='__main__':main()
