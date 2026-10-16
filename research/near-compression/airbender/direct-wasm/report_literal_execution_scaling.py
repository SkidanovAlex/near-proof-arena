"""Compare retained fixed-profile literal artifacts; no secure parameter claim."""
import argparse
import json
from pathlib import Path
import prepared_code_table_air as air


def main():
    ap=argparse.ArgumentParser();ap.add_argument('fixtures',type=Path,nargs='+');ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();cases=[]
    for directory in args.fixtures:
        compact=json.loads((directory/'compact-slice-report.json').read_text())
        spec=json.loads((directory/'statement.json').read_text())['spec']
        n=compact['fresh_verifier']['code_length']
        assert len(spec['public'])==air.CODEPUB+air.RECORD*n
        assert (directory/'proof.bin').stat().st_size==compact['proof_bytes']
        assert (directory/'envelope.bin').stat().st_size==compact['complete_envelope_bytes']
        cases.append(dict(fixture=str(directory),instructions=n,rows=[1<<x for x in spec['log_rows']],
          input_log=compact['trusted_input_log'],proof_bytes=compact['proof_bytes'],
          public_bytes=4*len(spec['public']),envelope_bytes=compact['complete_envelope_bytes'],
          transport_bytes=compact['transport_overhead_bytes'],
          envelope_plus_external_request_json_bytes=compact['envelope_plus_external_request_json_bytes']))
    cases.sort(key=lambda c:c['instructions'])
    floor=4*air.CODEPUB;slope=4*air.RECORD
    first_over=(300000-floor)//slope+1
    assert floor+slope*first_over>300000 and floor+slope*(first_over-1)<=300000
    report=dict(status='PASS',cases=cases,public_byte_formula=dict(fixed=floor,per_instruction=slope),
      first_instruction_count_public_alone_exceeds_300000=first_over,
      implication='This public CODE representation cannot meet the total-byte target at larger distinct-code sizes, regardless of proof compression. Authenticate code against a commitment instead of carrying every public CODE record.',
      limits=['Q8/Ext4 diagnostic; neither artifact certifies security.',
              'Input caps and transcripts differ, so the comparison is not an isolated execution-length performance experiment.',
              'Instruction count is distinct straight-line literal code size, not a model of full NEAR dynamic execution or1Pgas.',
              'Committed-code authentication and full-state/host semantics remain unimplemented here.'])
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
