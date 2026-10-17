#!/usr/bin/env python3
"""Actual hash_parts updates vs canonical Lean framing, with explicit bounds."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',type=Path,required=True)
    p.add_argument('--lean-directory',type=Path,required=True);p.add_argument('--fixture',type=Path,required=True)
    p.add_argument('--call-map',type=Path,required=True);p.add_argument('--output-directory',type=Path,required=True)
    a=p.parse_args();sys.path.insert(0,str(a.reference_dir));import pq384_primitives as primitive
    calls=json.loads(a.call_map.read_text());cases=[(c['tag'].encode('ascii'),[bytes.fromhex(x) for x in c['parts_hex']]) for c in calls]
    cases += [(b'',[]),(b'',[b'']),(bytes(range(256)),[bytes(range(256)),b'',bytes(range(255,-1,-1))]),(b'x',[b'a',b'bc']),(b'x',[b'ab',b'c'])]
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    inputs=out/'lean-input.json';binary=out/'lean-frames.bin';lengthpath=out/'lean-lengths.json'
    inputs.write_text(json.dumps([[list(tag),[list(x) for x in parts]] for tag,parts in cases],separators=(',',':')))
    subprocess.run(['lake','env','lean','--run',str(a.fixture),str(inputs),str(binary),str(lengthpath)],cwd=a.lean_directory,check=True)
    data=binary.read_bytes();lengths=json.loads(lengthpath.read_text());assert len(lengths)==len(cases)
    original=hashlib.sha384;captured=[]
    class Spy:
        def __init__(self):self.h=original();self.chunks=[];captured.append(self)
        def update(self,value):self.chunks.append(value);self.h.update(value)
        def digest(self):return self.h.digest()
    cursor=0
    try:
        primitive.hashlib.sha384=Spy
        for i,((tag,parts),length) in enumerate(zip(cases,lengths)):
            result=primitive.hash_parts(tag,*parts)
            frame=b''.join(captured[-1].chunks)
            assert frame==data[cursor:cursor+length]
            assert length==32+len(tag)+sum(8+len(part) for part in parts)
            assert original(frame).digest()==result
            if i<len(calls):assert result.hex()==calls[i]['digest_hex']
            cursor+=length
    finally:primitive.hashlib.sha384=original
    assert cursor==len(data)
    assert b''.join(captured[-1].chunks)!=b''.join(captured[-2].chunks)
    rejected=[]
    for name,tag,parts in [('tag bytearray',bytearray(b't'),()),('tag string','t',()),('part bytearray',b't',(bytearray(b'x'),)),('part string',b't',('x',))]:
        try:primitive.hash_parts(tag,*parts)
        except ValueError:rejected.append(name)
        else:raise AssertionError(name)
    for n in [-1,True,1<<64]:
        try:primitive.u64(n)
        except ValueError:rejected.append('u64 '+repr(n))
        else:raise AssertionError(n)
    report={'status':'PASS','captured_unique_calls':len(calls),'additional_cases':5,'framed_bytes':len(data),'negative_cases':rejected,
      'files':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in [a.call_map,a.fixture,Path(__file__),a.reference_dir/'pq384_primitives.py',binary,lengthpath]],
      'limits':['Actual immutable bytes enforced by Python; Lean List UInt8 enforces byte range by type.',
      'u32/u64 fit theorems prohibit truncation; huge Python containers are not allocated for overflow tests.',
      'Byte-format parity does not establish verifier operand provenance, commitment binding or cryptographic soundness.']}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
