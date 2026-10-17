"""Actual-workload statement, AIR handoff, and joint-oracle binding regressions."""
import argparse
import copy
import json
from collections import Counter
from pathlib import Path
import pq384_joint_bus as combined


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('directory', type=Path)
    ap.add_argument('output', type=Path)
    a = ap.parse_args()
    original = json.loads((a.directory/'proof.json').read_text())
    statement = json.loads((a.directory/'statement.json').read_text())
    spec = statement['spec']
    roots = [bytes.fromhex(v) for v in statement['roots']]
    assert combined.verify(original, spec, roots)
    counts = Counter()

    def reject(label, proof=original, public=spec, commitments=roots):
        try:
            combined.verify(proof, public, commitments)
        except ValueError:
            counts[label] += 1
        else:
            raise AssertionError('accepted mutation: '+label)

    for ti in range(len(roots)):
        changed = list(roots)
        changed[ti] = bytes([roots[ti][0]^1])+roots[ti][1:]
        reject('source_root', commitments=changed)
        for section in ('current_evals', 'next_evals', 'column_claims'):
            proof = copy.deepcopy(original)
            table = proof['air']['tables'][ti]
            values = table[section] if section == 'column_claims' else table['shift_reduction'][section]
            values[0][0] = (values[0][0]+1) % combined.bus.P
            reject(section, proof=proof)
    for index in (0, len(spec['public'])//2, len(spec['public'])-1):
        changed = copy.deepcopy(spec)
        changed['public'][index] = (changed['public'][index]+1) % combined.bus.P
        reject('public_value', public=changed)
    changed = copy.deepcopy(spec)
    changed['air']['tables'][0]['constraints'][0] = ['c', 1]
    reject('air_constraint', public=changed)
    proof = copy.deepcopy(original)
    proof['air']['finals'][0][0][0] ^= 1
    reject('bus_final', proof=proof)
    for section in ('sources', 'folds'):
        for index in range(len(original['joint']['queries'][0][section])):
            proof = copy.deepcopy(original)
            proof['joint']['queries'][0][section][index]['leaf'][0] ^= 1
            reject(section+'_leaf', proof=proof)
    for section in ('reduction', 'rounds'):
        for index in range(len(original['joint'][section])):
            proof = copy.deepcopy(original)
            values = proof['joint'][section][index]
            if section == 'rounds':
                values = values['quadratic']
            values[0][0] ^= 1
            reject(section+'_quadratic', proof=proof)
    proof = copy.deepcopy(original)
    proof['joint']['terminal']['coefficients'][0][0][0] ^= 1
    reject('terminal', proof=proof)
    proof = copy.deepcopy(original)
    proof['joint']['queries'][0]['sources'].reverse()
    reject('source_order', proof=proof)
    report = dict(status='PASS', rejections=sum(counts.values()), categories=dict(counts),
        scope='Mutation regressions on actual33table joint diagnostic; not a soundness bound.')
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
