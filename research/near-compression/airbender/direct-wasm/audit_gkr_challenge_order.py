"""Replay retained proofs and inspect challenge chronology; no randomness proof."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--reference-dir', required=True)
    ap.add_argument('--fixture', type=Path, required=True)
    ap.add_argument('--input-log', type=int, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    sys.path.insert(0, args.reference_dir)
    import pq384_gkr_bus as bus
    import pq384_terminal_gkr as gkr
    import pq384_weighted_joint as pcs
    from pq384_primitives import Transcript

    proof = json.loads((args.fixture / 'proof.json').read_text())
    statement = json.loads((args.fixture / 'statement.json').read_text())
    events, restores, captured = [], [], {}
    phase = ['outside']

    def replace(obj, name, value):
        restores.append((obj, name, getattr(obj, name)))
        setattr(obj, name, value)

    commit, draw = Transcript.commit, Transcript.draw

    def traced_commit(self, label, payload):
        result = commit(self, label, payload)
        events.append(dict(phase=phase[0], kind='commit', label=label.decode(), bytes=len(payload)))
        return result

    def traced_draw(self, label, count, coefficients, max_blocks=4096):
        result = draw(self, label, count, coefficients, max_blocks)
        events.append(dict(phase=phase[0], kind='draw', label=label.decode(), count=count,
                           coefficients=coefficients, values=result[0]))
        return result

    def wrap(obj, name, tag):
        original = getattr(obj, name)

        def call(*a, **kw):
            prior = phase[0]
            phase[0] = tag
            try:
                result = original(*a, **kw)
                captured.setdefault(tag, []).append(result)
                return result
            finally:
                phase[0] = prior
        replace(obj, name, call)

    try:
        replace(Transcript, 'commit', traced_commit)
        replace(Transcript, 'draw', traced_draw)
        for obj, name, tag in [(bus, 'begin', 'source-and-bus'),
                               (bus, 'initialize_aux', 'auxiliary'),
                               (bus, 'constraint_verify', 'constraints'),
                               (bus, 'terminal_layout', 'layout'),
                               (gkr, 'verify', 'gkr'), (pcs, 'verify', 'pcs')]:
            wrap(obj, name, tag)
        assert bus.verify(proof, statement['spec'], [bytes.fromhex(x) for x in statement['roots']],
                          input_log=args.input_log)
    finally:
        for obj, name, original in reversed(restores):
            setattr(obj, name, original)

    order = ['source-and-bus', 'auxiliary', 'constraints', 'layout', 'gkr', 'pcs']
    ranks = [order.index(e['phase']) for e in events]
    assert ranks == sorted(ranks)
    assert set(e['phase'] for e in events) == set(order)
    start = [e for e in events if e['phase'] == 'source-and-bus']
    assert start[0]['label'] == 'all-source-commitments'
    assert [e['kind'] for e in start] == ['commit', 'draw', 'draw']
    aux = [e for e in events if e['phase'] == 'auxiliary']
    assert aux[0]['label'] == 'all-auxiliary-commitments'
    assert all(e['kind'] == 'commit' for e in aux)
    terminals = captured['constraints']
    ce = [e for e in events if e['phase'] == 'constraints']
    cursor = 0
    assert len(terminals) == len(statement['spec']['log_rows'])
    for terminal, n in zip(terminals, statement['spec']['log_rows']):
        assert ce[cursor]['label'] == 'table-constraint-start'
        assert ce[cursor+1]['kind'] == ce[cursor+2]['kind'] == 'draw'
        assert tuple(ce[cursor+1]['values'][0]) == tuple(terminal['mixing'])
        assert [tuple(v) for v in ce[cursor+2]['values']] == list(terminal['tau'])
        cursor += 3
        assert len(terminal['point']) == n
        for coordinate in terminal['point']:
            assert ce[cursor]['kind'] == 'commit' and ce[cursor+1]['kind'] == 'draw'
            assert tuple(ce[cursor+1]['values'][0]) == tuple(coordinate)
            cursor += 2
    assert cursor == len(ce)
    layout = captured['layout'][0][1]
    assert layout['input_size'] == 1 << args.input_log
    ge = [e for e in events if e['phase'] == 'gkr']
    assert len(ge) % 2 == 0
    assert all(ge[i]['kind'] == 'commit' and ge[i+1]['kind'] == 'draw'
               for i in range(0, len(ge), 2))
    gd = [tuple(e['values'][0]) for e in ge if e['kind'] == 'draw']
    final = gd[-(2*args.input_log+1):]
    obligation = captured['gkr'][0]
    assert list(obligation['queries'][0][0]) == final[:args.input_log]
    assert list(obligation['queries'][1][0]) == final[args.input_log:2*args.input_log]
    assert tuple(obligation['queries'][1][1]) == final[-1]
    pe = [e for e in events if e['phase'] == 'pcs']
    n = len(proof['opening']['reduction'])
    assert len(proof['opening']['rounds']) == n
    # Reduction and folding both commit a quadratic before each draw.
    cursor = 0
    for stage in ('reduction', 'folding'):
        for _ in range(n):
            assert pe[cursor]['kind'] == 'commit' and pe[cursor+1]['kind'] == 'draw'
            assert pe[cursor+1]['coefficients'] == 4
            cursor += 2
            if stage == 'folding':
                assert pe[cursor]['label'] == 'weighted-joint-next-root'
                cursor += 1
    assert pe[cursor]['label'] == 'disclosed-terminal-before-queries'
    assert all(e['kind'] == 'draw' and e['label'] == 'global-chain-domain-index'
               for e in pe[cursor+1:])
    # Retain event structure, not all sampled values; values above checked the
    # final GKR query coordinates against the actual opening obligation.
    for e in events:
        e.pop('values', None)
    report = dict(status='PASS', fixture=str(args.fixture), trusted_input_log=args.input_log,
        proof_sha256=hashlib.sha256((args.fixture/'proof.json').read_bytes()).hexdigest(),
        row_coordinates=sum(statement['spec']['log_rows']), final_gkr_coordinates=len(final),
        pcs_coordinates=n, joint_coordinates=sum(statement['spec']['log_rows'])+len(final)+n,
        phase_event_counts=dict(Counter(e['phase'] for e in events)), events=events,
        established=['Source roots precede bus challenges; auxiliary roots/finals precede all row coordinates.',
                     'Fixed input cap determines final GKR coordinate count despite earlier challenge-dependent circuit compilation.',
                     'Final GKR draw suffix exactly equals returned left/right/gamma opening obligation.',
                     'PCS reduction follows GKR; each fold root follows its fold challenge; all queries follow terminal disclosure.'],
        limits=['Replay evidence for this retained artifact, not universal implementation refinement.',
                'Actual SHA-384 draws are deterministic; this audit proves no independent uniform or quantum random-oracle claim.',
                'Universal metadata stability and chronological near/far count composition remain open.',
                'Q8/Ext4 diagnostic, not secure full-NEAR parameters.'])
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'events'}))


if __name__ == '__main__':
    main()
