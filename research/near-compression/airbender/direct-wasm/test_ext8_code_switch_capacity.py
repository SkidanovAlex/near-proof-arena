"""Capacity boundaries and fresh native verification of retained switch proofs."""
import argparse,json,subprocess,sys,tempfile
from pathlib import Path
import pq384_ext8_reference as f
from pq384_ext8_native import Kernel
import ext8_code_switch_stage as stage


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();negative=[]
    with tempfile.TemporaryDirectory(prefix='switch-capacity-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(Path(__file__).with_name('native-folded')/'kernel_ext8.rs'),'-o',str(lib)],check=True);native=Kernel(lib)
        n=262144;ws,cl=native.inject([f.ZERO]*n,f.ZERO,[f.ONE],[f.ONE],[f.ONE]);assert ws==[f.ONE]*n and cl==f.ONE
        ws,cl=native.inject([f.ZERO]*2,f.ZERO,[f.ONE]*4096,[f.ONE]*4096,[f.ONE]*4096);assert ws==[f.base(4096)]*2 and cl==f.base(4096)
        assert stage.geometry(262144,16,4)[:2]==(4194304,262144)
        def reject(name,fn):
            try:fn()
            except ValueError:negative.append(name)
            else:raise AssertionError(name)
        reject('degree-cap',lambda:native.inject([f.ZERO]*262145,f.ZERO,[],[],[]))
        reject('domain-cap',lambda:stage.geometry(262144,32,4))
        reject('stage-degree-cap',lambda:stage.geometry(524288,4,4))
        fresh=[]
        for script,directory in [('ext8_code_switch_stage.py','ext8-code-switch-stage'),('ext8_weighted_code_switch.py','ext8-weighted-code-switch')]:
            root=Path('results')/directory
            result=subprocess.run([sys.executable,str(Path(__file__).with_name(script)),'--proof',str(root/'proof.json'),'--statement',str(root/'statement.json'),'--native-library',str(lib)],text=True,capture_output=True);result.check_returncode();fresh.append(result.stdout.strip())
    report=dict(status='PASS',native_degree_boundary=262144,native_constraints_boundary=4096,accepted_geometry_domain=4194304,negative_cases=negative,fresh_native_verifiers=fresh,scope='Exact boundary checks and retained proof replay. Geometry acceptance is not a full4M encoding or full-slice prover run.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
