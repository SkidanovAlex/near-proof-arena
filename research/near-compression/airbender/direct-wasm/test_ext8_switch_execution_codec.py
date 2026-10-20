"""Full retained execution-envelope negative and profile separation tests."""
import argparse,copy,gzip,hashlib,json,subprocess,tempfile
from pathlib import Path
import ext8_switch_execution_codec as c
import ext8_execution_codec as legacy
from pq384_ext8_native import Kernel


def read(path):
    raw=path.read_bytes();return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)


def main():
    p=argparse.ArgumentParser()
    for key in ('capture','statement','config','output'):p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args();st,config=read(a.statement),read(a.config);wire=(a.capture/'compression.bin').read_bytes();negatives=[]
    with tempfile.TemporaryDirectory(prefix='switch-envelope-test-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(Path(__file__).with_name('native-folded')/'kernel_ext8.rs'),'-o',str(lib)],check=True);native=Kernel(lib)
        reduction,opening=c.decode(wire,st['spec'],st['roots'],config=config,native=native)
        assert c.encode(reduction,opening,st['spec'],st['roots'],config=config,native=native)==wire
        def reject(name,bad,cfg=config):
            try:c.decode(bad,st['spec'],st['roots'],config=cfg,native=native)
            except ValueError:negatives.append(name)
            else:raise AssertionError(name)
        reject('truncated',wire[:-1]);reject('trailing',wire+b'\0');reject('version',b'BADMAGIC'+wire[8:])
        for name,at in [('source-root',8),('aux-root',8+48*len(st['roots'])),('bus-final',8+96*len(st['roots'])),('pcs-terminal',len(wire)-1)]:
            reject(name,wire[:at]+bytes([wire[at]^1])+wire[at+1:])
        at=8+96*len(st['roots'])
        reject('noncanonical',wire[:at]+c.v.f.P.to_bytes(4,'little')+wire[at+4:])
        cfg=copy.deepcopy(config);cfg['tail_steps'][0]['queries']-=1;reject('external-schedule',wire,cfg)
        old=Path('results/ext8-phase-pooled-q309/compression.bin').read_bytes()
        reject('legacy-profile',old);reject('relabelled-legacy-profile',c.MAGIC+old[8:])
        try:legacy.decode(legacy.magic('affine-v1','phase-pooled-v1')+wire[8:],st['spec'],st['roots'],queries=309,terminal_profile='affine-v1',commitment_profile='phase-pooled-v1')
        except ValueError:negatives.append('relabelled-switch-as-legacy')
        else:raise AssertionError('profile relabeling accepted')
    report=dict(status='PASS',roundtrip=True,negative_cases=negatives,compression_envelope_bytes=len(wire),opening_bytes=len(opening),sha256=hashlib.sha256(wire).hexdigest(),scope='Full fixture envelope checks, not full NEAR or cryptographic soundness certification.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
