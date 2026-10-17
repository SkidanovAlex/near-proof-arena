"""Reject corrupted capture pins, contradictory sizes and stale security ledgers."""
import hashlib
import json
from pathlib import Path
from unittest.mock import patch
import report_current_feasibility as report


def main():
    good=report.build()
    assert good['status']=='NOT_PASSED' and not good['measured_fixture']['security_certified']
    assert not good['same_parameters_as_measured_fixture']
    assert good['screened_candidates_passing_partial_bound_and_size']==0
    assert sum(good['measured_fixture']['components'].values())==1344645
    choices={x['replaced_component']:x for x in good['replacement_break_even']}
    opening=choices['entire_opening']
    assert opening['fixed_remainder_bytes']+opening['maximum_replacement_bytes_for_strict_target']==299999
    assert not choices['all_opening_authentication']['possible_even_with_free_replacement']
    original=Path.read_bytes
    base=report.ROOT/'results/ext8-switch-execution-q309'
    manifest_path=base/'manifest.json'
    mutations=[
        (base/'report.json',lambda d:d.update(combined_bytes=1),True),
        (base/'report.json',lambda d:d.update(fresh_conjunction_verified=False),True),
        (base/'prover-report.json',lambda d:d['breakdown'].update(header_and_terminal_bytes=1),True),
        (report.ROOT/'results/larger-field-code-switch-screen.json',
            lambda d:d['results'][0]['conditional_ledger'].update(partial_within_half_success=True),False),
        (report.ROOT/'results/larger-field-code-switch-screen.json',
            lambda d:d['results'][0].update(min_subtotal_bytes=1),False),
        (base/'config.json',lambda d:d.update(queries=1),False),
    ]
    for path,mutate,repin in mutations:
        data=json.loads(original(path));mutate(data);raw=json.dumps(data).encode()
        changes={path:raw}
        if repin:
            manifest=json.loads(original(manifest_path))
            manifest['files'][str(path.relative_to(report.REPO))]=hashlib.sha256(raw).hexdigest()
            changes[manifest_path]=json.dumps(manifest).encode()
        def patched(path): return changes[path] if path in changes else original(path)
        with patch.object(Path,'read_bytes',patched):
            try: report.build()
            except (AssertionError,ValueError): pass
            else: raise AssertionError('accepted contradictory evidence: '+str(path))
    print(json.dumps(dict(status='PASS',corrupt_or_inconsistent_evidence_rejections=len(mutations),
        strict_target_boundary_checked=True,scope='Evidence reconciliation and arithmetic only; no security certification.')))


if __name__=='__main__':main()
