#!/usr/bin/env python3
"""Compare evaluated Lean coverage to literal branches of the pinned dispatcher.

This is inventory evidence, not a soundness theorem or a change to admission.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
HOST = REPO / 'spec/lean/v3/NearSpecV3/Wasm/Host.lean'
EXEC = REPO / 'spec/lean/v3/NearSpecV3/Wasm/Exec.lean'
COVERAGE = HERE / 'NearCompression/HostCoverage.lean'


def main():
    source = HOST.read_text().split('def hostCall (name : String)', 1)[1]
    branches = re.findall(r'^  \| "([^"\n]+)" => some\b', source, re.M)
    branch_lines = re.findall(r'^  \| .*$', source, re.M)
    if len(branch_lines) != len(branches) + 1 or branch_lines[-1] != '  | _ => none':
        raise SystemExit('Dispatcher shape changed: review inventory extraction')
    result = subprocess.run(['lake', 'env', 'lean', 'HostInventory.lean'], cwd=HERE,
                            text=True, capture_output=True, check=True)
    def section(label):
        matches = re.findall(rf'^{label}\n(.*?)\nEND$', result.stdout, re.M | re.S)
        if len(matches) != 1:
            raise SystemExit(f'Expected one evaluated {label} list')
        names = matches[0].splitlines()
        if len(names) != len(set(names)):
            raise SystemExit(f'Duplicate names in {label}')
        return set(names)
    covered, gated, curves = (section(n) for n in ['COVERED', 'REAL_GATED', 'CURVES'])
    wrappers = section("REAL_WRAPPERS")
    if wrappers != covered | gated:
        raise SystemExit("Real wrapper coverage differs from proved/gated union")
    dispatch = set(branches)
    if len(dispatch) != len(branches) or covered - dispatch or gated - dispatch:
        raise SystemExit('Duplicate branches or inventory names without dispatch')
    missing = dispatch - covered
    report = {
        'meaning': 'Evaluated coverage list versus literal hostCall branches; not full NEAR coverage or admission',
        'dispatch_count': len(dispatch), 'covered_count': len(covered),
        'covered': sorted(covered),
        'real_wrapper_count': len(wrappers),
        'real_wrapper_names_without_dispatch': sorted(wrappers - dispatch),
        'dispatch_names_without_real_wrapper': sorted(dispatch - wrappers),
        'real_wrapper_scope': 'Host wrapper, direct/indirect calls, all existing instruction constructors and one-step simulation on real states; full-run integration remains open',
        'uncovered_not_real_gated': sorted(missing - gated),
        'uncovered_real_gated': sorted(missing & gated),
        'covered_real_gated': sorted(covered & gated),
        'curve_names_without_host_dispatch': sorted(curves - dispatch),
        'limitation': 'Real-gated functions reject when called with a real backend; proving mock dispatches would not add their full protocol semantics. Curve handling and other preparation/domain exclusions remain separate.',
        'source_sha256': {str(p.relative_to(REPO)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [HOST, EXEC, COVERAGE, HERE / 'NearCompression/RealHostGate.lean', HERE / 'NearCompression/RealInstruction.lean', HERE / 'HostInventory.lean']},
    }
    (HERE / 'host-inventory.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Host inventory: {len(covered)}/{len(dispatch)} dispatcher names covered; '
          f'{len(missing-gated)} ungated and {len(missing & gated)} real-gated names remain.')
    print('Uncovered ungated: ' + ', '.join(sorted(missing-gated)))


if __name__ == '__main__':
    main()
