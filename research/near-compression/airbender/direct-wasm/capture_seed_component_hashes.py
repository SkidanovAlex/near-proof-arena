"""Capture actual configured core+setup hashing for both migrated components.

Application wrapper checks are separate; this is work accounting, not a proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

import pq384_primitives as primitives
import pq384_seed_gkr_bus as bus


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--results', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    calls, events, pending, unique, sources = [], [], {}, {}, []
    component = 0

    def trace(frame, event, arg):
        if frame.f_code is not primitives.hash_parts.__code__:
            return
        if event == 'call':
            tag, parts = frame.f_locals['tag'], frame.f_locals['parts']
            key = (tag, parts)
            if key not in unique:
                unique[key] = len(calls)
                calls.append(dict(tag_hex=tag.hex(), parts_hex=[p.hex() for p in parts]))
            index = unique[key]
            pending[id(frame)] = index
            events.append([component, index])
        elif event == 'return':
            index = pending.pop(id(frame))
            if type(arg) is not bytes or len(arg) != 48:
                raise ValueError('incomplete hash return')
            old = calls[index].get('digest_hex')
            if old is not None and old != arg.hex():
                raise ValueError('inconsistent repeated hash')
            calls[index]['digest_hex'] = arg.hex()

    for component, name in enumerate(('sha384-direct-seed', 'sha384-committed-seed')):
        directory = a.results / name
        proof_path, statement_path = directory/'proof.json', directory/'statement.json'
        proof = json.loads(proof_path.read_text())
        statement = json.loads(statement_path.read_text())
        roots = [bytes.fromhex(r) for r in statement['roots']]
        if sys.getprofile() is not None:
            raise ValueError('profiler occupied')
        sys.setprofile(trace)
        try:
            config = bus.configure(statement['spec']['air'])
            if bus.verify(proof, statement['spec'], roots, config) is not True:
                raise ValueError('core verifier rejected')
        finally:
            sys.setprofile(None)
        if pending:
            raise ValueError('pending hash calls')
        sources.extend([proof_path, statement_path])
        print('verified and captured '+name, flush=True)
    a.output.mkdir(parents=True, exist_ok=True)
    for name, data in [('hash-calls.json', calls), ('hash-occurrences.json', events)]:
        (a.output/name).write_text(json.dumps(data, separators=(',', ':')))
    sources += [Path(__file__), Path(bus.__file__), Path(primitives.__file__)]
    report = dict(status='PASS', components=2, unique_calls=len(calls), occurrences=len(events),
                  files={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
                  limits=['Configured core and configuration setup only; application wrapper AIR digest checks excluded.',
                          'No operation coverage or recursion soundness claim.',
                          'Full-state deduplication is a separate checked analysis.'])
    (a.output/'report.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
