"""Separate-process PCS recovery equals uninterrupted proof bytes on a tiny AIR."""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import resume_ext8_checkpoint as resume
from pq384_ext8_native import Kernel


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--native-library',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    native=Kernel(a.native_library);here=Path(__file__).parent
    with tempfile.TemporaryDirectory(prefix='ext8-resume-test-') as tmp:
        root=Path(tmp);source=root/'source';source.mkdir();rows=[[3]]*4
        table=dict(width=1,maxLog=2,constraints=[['+',['v',0,0],['-',['c',3]]]],interactions=[dict(bus=0,send=send,mult=[],msg=[['v',0,0]]) for send in (True,False)])
        spec=dict(air=dict(format='np-air-v1',numPub=0,maxPub=0,numBuses=1,pubSegs=[],tables=[table]),public=[],log_rows=[2],terminal_degree=1,source_packings=[1],aux_packings=[1])
        statement=dict(spec=spec,roots=[resume.packed.p.Source(rows,1,native).root.hex()])
        statement_path=root/'statement.json';statement_path.write_bytes(resume.canonical(statement))
        source_path=source/'source-00-rows.json';source_path.write_bytes(resume.canonical(dict(rows=rows)))
        checkpoint=root/'checkpoint';capture=root/'proof'
        cmd=[sys.executable,str(here/'run_ext8_checkpointed_prover.py'),'--statement',str(statement_path),'--source-directory',str(source),'--checkpoint-dir',str(checkpoint),'--output',str(root/'report.json'),'--capture-dir',str(capture),'--pcs-queries','8','--terminal-profile','affine-v1']
        run=subprocess.run(cmd,capture_output=True,text=True)
        if run.returncode:raise RuntimeError(run.stdout+run.stderr)
        opening_raw=(checkpoint/'opening.json').read_bytes()
        (checkpoint/'opening.json.gz').write_bytes(gzip.compress(opening_raw,mtime=0))
        (checkpoint/'opening.json').unlink()
        # Recovery starts with only checkpoint, statement and source files: no proof cache input.
        cmd=[sys.executable,str(here/'resume_ext8_checkpoint.py'),'--checkpoint',str(checkpoint),'--statement',str(statement_path),'--source-directory',str(source),'--native-library',str(a.native_library.resolve()),'--output-dir',str(root/'resumed'),'--queries','8']
        run=subprocess.run(cmd,capture_output=True,text=True)
        if run.returncode:raise RuntimeError(run.stdout+run.stderr)
        wire=(capture/'proof.bin').read_bytes();assert wire==(root/'resumed/proof.bin').read_bytes()
        (checkpoint/'opening.json').write_bytes(opening_raw)
        negatives=[]
        def reject(name,fn):
            try:fn()
            except (ValueError,AssertionError):negatives.append(name)
            else:raise AssertionError('accepted '+name)
        reject('query-count',lambda:resume.checked_parameters(checkpoint,statement,9))
        bad=copy.deepcopy(statement);bad['roots'][0]='00'*48
        reject('external-root',lambda:resume.checked_parameters(checkpoint,bad,8))
        reduction,opening,_=resume.checked_parameters(checkpoint,statement,8)
        raw=(checkpoint/'opening.json').read_bytes();(checkpoint/'opening.json').write_bytes(raw+b' ')
        # JSON whitespace does not change the canonical opening commitment.
        resume.checked_parameters(checkpoint,statement,8)
        altered=copy.deepcopy(opening);altered['claim'][0]=(altered['claim'][0]+1)%resume.packed.f.P
        (checkpoint/'opening.json').write_bytes(resume.canonical(altered))
        reject('checkpoint-opening-hash',lambda:resume.checked_parameters(checkpoint,statement,8))
        (checkpoint/'opening.json').write_bytes(raw)
        source_path.write_bytes(resume.canonical(dict(rows=[[4]]*4)))
        reject('source-root',lambda:resume.reconstruct(statement,reduction,source,native))
        source_path.write_bytes(resume.canonical(dict(rows=rows)))
        bad=copy.deepcopy(reduction);bad['aux_roots'][0]='00'*48
        reject('auxiliary-root',lambda:resume.reconstruct(statement,bad,source,native))
        report=dict(status='PCS_RECOVERY_BYTE_PARITY',opening_bytes=len(wire),opening_sha256=hashlib.sha256(wire).hexdigest(),negative_cases=negatives,fresh_verifier_passed=True,
            scope='Tiny one-table AIR uninterrupted adapter versus PCS-only reconstruction in separate processes. No full-scale recovery/memory or cryptographic soundness claim.',
            sha256={str(p.relative_to(here.parents[1])):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(resume.__file__),here/'run_ext8_checkpointed_prover.py']})
        a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
