#!/usr/bin/env python3
"""Adversarial checks of the real-D1 sample diagnostic, not a proof verifier."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
from check_d1_trace_export import check_samples, P


def main():
    out = Path(__file__).resolve().parents[2]/'results'
    directory = out/'d1-real-00-h10012-s2'
    air = json.loads((out/'d1-air.json').read_text())
    report = json.loads((directory/'report.json').read_text())
    samples = json.loads((directory/'samples.json').read_text())
    public = list((directory/'prepared.bin').read_bytes())
    assert check_samples(directory, air, report, public)['status'] == 'PASS'
    rejected = []

    def reject(label, mutate):
        bad = deepcopy(samples)
        mutate(bad)
        with tempfile.TemporaryDirectory(prefix='near-d1-sample-negative-') as temp:
            path = Path(temp)
            (path/'samples.json').write_text(json.dumps(bad))
            try:
                check_samples(path, air, report, public)
            except (ValueError, KeyError, TypeError, IndexError):
                rejected.append(label)
            else:
                raise AssertionError('Accepted '+label)

    reject('missing table', lambda s: s.pop())
    reject('noncanonical cell', lambda s: s[0]['samples'][0]['current'].__setitem__(0, P))
    reject('wrong cyclic successor', lambda s: s[0]['samples'][-1]['next'].__setitem__(0, 2))

    def nonboolean(s):
        # Preserve the duplicated row0 representation to reach the AIR evaluator.
        s[0]['samples'][0]['current'][0] = 2
        s[0]['samples'][-1]['next'][0] = 2

    reject('consistent nonboolean SHA cell', nonboolean)
    result = {'status': 'PASS', 'rejections': rejected,
              'scope': 'Sample diagnostic only; no full trace/proof soundness claim.'}
    (directory/'sample-negative-tests.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
