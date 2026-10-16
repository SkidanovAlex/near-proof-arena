"""Statement preservation and mutation regression for migrated seed component."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
from verify_sha384_direct_seed import verify


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--original', type=Path, required=True)
    ap.add_argument('--migrated', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    old = json.loads((a.original/'statement.json').read_text())
    statement = json.loads((a.migrated/'statement.json').read_text())
    expected = json.loads((a.original/'expected-input.json').read_text())
    proof = json.loads((a.migrated/'proof.json').read_text())
    if old != statement:
        raise ValueError('migration changed AIR, public values, roots, or encoding shapes')
    assert verify(proof, statement, expected)
    rejected = []

    def reject(label, p=proof, s=statement, e=expected):
        try:
            verify(p, s, e)
        except (ValueError, TypeError, KeyError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError('accepted '+label)

    reject('missing trusted receipt', e=None)
    for key, value in [('input_root', '00'*48), ('input_context_hex', ''),
                       ('air_sha384', '00'*48), ('declared_length', 375)]:
        bad = copy.deepcopy(expected); bad[key] = value
        reject('trusted '+key, e=bad)
    for index in range(3):
        bad = copy.deepcopy(statement); bad['roots'][index] = '00'*48
        reject('source root '+str(index), s=bad)
    bad = copy.deepcopy(statement); bad['spec']['public'][0] ^= 1
    reject('public digest', s=bad)
    bad = copy.deepcopy(statement); bad['spec']['public'][48] = 0
    reject('public count', s=bad)
    bad = copy.deepcopy(statement); bad['spec']['air']['tables'][0]['constraints'].append(['c', 1])
    reject('AIR substitution', s=bad)
    for key in ('gkr', 'opening', 'finals', 'aux_roots'):
        bad = copy.deepcopy(proof); del bad[key]
        reject('missing '+key, p=bad)
    bad = copy.deepcopy(proof); bad['gkr']['layers'][0]['inputs'][0][0] ^= 1
    reject('GKR input', p=bad)
    bad = copy.deepcopy(proof); bad['opening']['queries'][0]['sources'][0]['leaf'][0] ^= 1
    reject('PCS source leaf', p=bad)
    paths = [a.original/'statement.json', a.original/'expected-input.json',
             a.migrated/'statement.json', a.migrated/'proof.json', Path(__file__),
             Path(__file__).with_name('verify_sha384_direct_seed.py')]
    report = dict(status='PASS', exact_statement_preserved=True, negative_cases=rejected,
                  files={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                  limits=['Expanded diagnostic proof; no recursive compression or secure parameter claim.',
                          'Trusted configuration hashing is performed by the wrapper.'])
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(status='PASS', negative_cases=len(rejected))))


if __name__ == '__main__':
    main()
