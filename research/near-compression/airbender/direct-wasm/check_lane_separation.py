"""Independently enumerate live slots to check canonical lane separators."""
import argparse, copy, hashlib, json
from pathlib import Path

def check(meta):
    lanes = meta['lanes']
    supports = []
    for lane in lanes:
        packing = 1 << lane['packingLog']
        cols = range(lane['group'] * packing, min((lane['group'] + 1) * packing, lane['width']))
        supports.append(tuple({lane['inputStart'] + next_ * lane['nextOffset'] + col for col in cols} for next_ in (0, 1)))
    selected = []
    for i, (current, following) in enumerate(supports):
        if not current:
            raise ValueError('empty lane')
        slot = min(current)
        if slot >= 1 << meta['layout']['inputLog'] or slot in following:
            raise ValueError('invalid own selector')
        if any(slot in a or slot in b for j, (a, b) in enumerate(supports) if j != i):
            raise ValueError('selector collision')
        selected.append(slot)
    return selected

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('metadata', nargs='+', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    reports = []
    for path in args.metadata:
        raw = path.read_bytes()
        meta = json.loads(raw)
        slots = check(meta)
        mutations = []
        duplicate = copy.deepcopy(meta); duplicate['lanes'].append(copy.deepcopy(duplicate['lanes'][0])); mutations.append(duplicate)
        overlap = copy.deepcopy(meta); overlap['lanes'][0]['nextOffset'] = 0; mutations.append(overlap)
        empty = copy.deepcopy(meta); empty['lanes'][0]['width'] = 0; mutations.append(empty)
        outside = copy.deepcopy(meta); outside['layout']['inputLog'] = 0; mutations.append(outside)
        for mutated in mutations:
            try:
                check(mutated)
            except ValueError:
                continue
            raise AssertionError('accepted invalid geometry')
        reports.append(dict(path=str(path), sha256=hashlib.sha256(raw).hexdigest(), lanes=len(slots), selectors=slots, rejected_mutations=len(mutations)))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(status='PASS', captures=reports, scope='Natural slot geometry on captured metadata; not cryptographic or quantum security.'), indent=2)+'\n')
    print(json.dumps(dict(status='PASS', captures=len(reports), lanes=sum(r['lanes'] for r in reports), rejected_mutations=sum(r['rejected_mutations'] for r in reports))))

if __name__ == '__main__':
    main()
