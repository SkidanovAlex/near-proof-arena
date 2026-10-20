"""Reproducible endpoint-split accounting; no controlled speedup claim."""
import argparse,hashlib,json
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--baseline-report',required=True);p.add_argument('--split-report',required=True);p.add_argument('--hash-accounting',required=True);p.add_argument('--output',required=True);a=p.parse_args()
    paths=[a.baseline_report,a.split_report,a.hash_accounting];old,new,account=[json.loads(Path(p).read_text()) for p in paths]
    def total(r):return sum(r['timing'].values())+sum(sum(t.values()) for t in r['table_timings'])
    blocks=account['identical_hash_inputs_shared']['compression_blocks'];endpoint_rows=1<<max(1,(blocks-1).bit_length())
    result=dict(input_sha256={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths},
        baseline_recorded_components_seconds=total(old),split_recorded_components_seconds=total(new),baseline_auxiliary_seconds=old['timing']['fresh_auxiliaries_and_commitments'],split_auxiliary_seconds=new['timing']['fresh_auxiliaries_and_commitments'],
        dense_shared_hash_source_gib=(blocks*128*5280+endpoint_rows*1668)*4/2**30,core_tables_needed_if_unbatched=blocks,
        scope='Single runs; sum of recorded components only, not wall time or controlled performance benchmark. Dense source extrapolation excludes routing auxiliaries, FFT, commitments and other verifier operations.',
        remaining_obligations=['Exact tagged A/B matching to core first/phase79 states from actual HoldsP','Nonlast output matching next core initial state','Public digest segment matches final active endpoint','Compose existing core rounds/add64 semantics with padding, IV and byte decoding','Cryptographic fingerprint/PCS/Fiat-Shamir soundness remains conditional'],
        batched80round_requirements=['Replace mandatory phaseLast127 and exact128height contract','Gate round/window transitions and resets at block starts','Bind block identity,roundindex and80keys','Prove mapping to full80round segments before endpoint composition'])
    Path(a.output).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
