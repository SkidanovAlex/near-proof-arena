"""Actual configured seed-profile verifier, with setup cost reported separately."""
import argparse,hashlib,json,sys
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--input-directory',required=True);p.add_argument('--output',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_seed_gkr_bus as bus
    from profile_pq384_verifier import measure
    inp=Path(a.input_directory);s=json.loads((inp/'statement.json').read_text());proof=json.loads((inp/'proof.json').read_text());roots=[bytes.fromhex(x) for x in s['roots']]
    configs=[]
    def setup():configs.append(bus.configure(s['spec']['air']));return True
    configured=measure(setup);actual=measure(lambda:bus.verify(proof,s['spec'],roots,configs[0]))
    result=dict(status='PASS',tables=len(roots),proof_sha256=hashlib.sha256((inp/'proof.json').read_bytes()).hexdigest(),statement_sha256=hashlib.sha256((inp/'statement.json').read_bytes()).hexdigest(),
        trusted_configuration_setup=configured,configured_expanded_verifier=actual,setup_and_verification_sha384_blocks=configured['total_sha384_compression_blocks']+actual['total_sha384_compression_blocks'],
        limits=['Configuration AIR/compiler is fixed trusted verifier setup, never proof selected','Actual fullheight33table Q8/Ext4 input; unchanged algebra and source authentication checks','Reference operation counts are not circuit constraint estimates','No proven recursive/QROM soundness'])
    Path(a.output).write_text(json.dumps(result,indent=2))
    print(json.dumps({label:{k:v[k] for k in ('total_hash_calls','total_sha384_compression_blocks','ext4_operation_calls')} for label,v in [('setup',configured),('configured_verifier',actual)]},indent=2))

if __name__=='__main__':main()
