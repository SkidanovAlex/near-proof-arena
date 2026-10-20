"""Lossless codec, canonical encoding, external-input accounting and rejection tests."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import pq384_ext8_rate_shift_codec as c
import pq384_ext8_reusable_codec as baseline


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--verify-only', action='store_true')
    args = ap.parse_args()
    if args.verify_only:
        env = json.loads(args.input.read_text())
        assert set(env) == {'config','root','continuation_queries'}
        assert c.verify(args.output.read_bytes(), env['config'], bytes.fromhex(env['root']), env['continuation_queries'])
        print('PASS fresh binary verifier; no expanded proof input')
        return
    args.output.mkdir(parents=True, exist_ok=True)
    reports, negatives = [], []
    for path in sorted(args.input.glob('d*.json')):
        env = json.loads(path.read_text())
        proof, cfg, root, qc = env['proof'], env['config'], bytes.fromhex(env['root']), env['continuation_queries']
        raw = c.encode(proof, cfg, root, qc)
        decoded = c.decode(raw, cfg, root, qc)
        assert decoded == proof
        assert c.encode(decoded, cfg, root, qc) == raw
        assert c.verify(raw, cfg, root, qc)
        accounting = c.breakdown(proof, cfg, root, qc)
        assert accounting['proof_bytes'] == len(raw)
        binary = args.output/(path.stem+'.bin')
        external = args.output/(path.stem+'-external.json')
        binary.write_bytes(raw)
        external.write_text(json.dumps({k: env[k] for k in ['config','root','continuation_queries']}, separators=(',', ':')))
        subprocess.run([sys.executable, __file__, '--input', str(external), '--output', str(binary), '--verify-only'], check=True)
        accounting.update(case=path.stem, binary_sha256=hashlib.sha256(raw).hexdigest(),
            binary_plus_external_json_bytes=len(raw)+external.stat().st_size,
            exact_expanded_roundtrip=True)
        if cfg['queries'] == 314:
            coeff = [(i*i*541+i*173+11) % c.r.e.P for i in range(cfg['degree'])]
            assert c.p.source_tree(coeff, cfg)['root'] == root
            old_proof = c.p.prove(coeff, cfg, root)
            old_binary = baseline.encode(old_proof, cfg, root)
            assert baseline.verify(old_binary, cfg, root)
            (args.output/(path.stem+'-baseline.bin')).write_bytes(old_binary)
            accounting['same_source_baseline'] = dict(proof_bytes=len(old_binary),
                total_required_input_bytes=len(old_binary)+len(c.p.config_bytes(cfg)),
                rate_shift_minus_baseline_bytes=len(raw)-len(old_binary),
                query_count=cfg['queries'], same_root_point_claim_and_statement=True,
                binary_sha256=hashlib.sha256(old_binary).hexdigest())
        reports.append(accounting)
        if cfg['degree'] == 32 and cfg['queries'] == 4:
            def reject(name, data, config=cfg, expected=root, count=qc):
                try:
                    c.verify(data, config, expected, count)
                except (ValueError, TypeError, KeyError, IndexError):
                    negatives.append(name)
                else:
                    raise AssertionError(name)
            for n in [0, 7, 8, 55, 56, 247, 248, 295, 296, 327, 328, len(raw)//2, len(raw)-1]:
                reject(f'truncated-{n}', raw[:n])
            for i in [0, 8, 56, 152, 248, 296, 328, len(raw)//2, len(raw)-1]:
                bad = bytearray(raw)
                bad[i] ^= 1
                reject(f'mutated-{i}', bytes(bad))
            reject('noncanonical-field', raw[:56]+c.r.e.P.to_bytes(4, 'little')+raw[60:])
            reject('trailing-byte', raw+b'\0')
            reject('oversize', bytes(c.MAX_BYTES+1))
            reject('wrong-root', raw, expected=bytes(48))
            reject('wrong-source-query-count', raw, config={**cfg, 'queries': cfg['queries']+1})
            reject('wrong-continuation-query-count', raw, count=qc+1)
            reject('wrong-statement', raw, config={**cfg, 'statement': '00'})
            reject('wrong-namespace', raw, config={**cfg, 'source_namespace': '00'})
            reject('unexpected-type', bytearray(raw))
    report = dict(status='PASS', cases=reports, negative_checks=negatives,
        limitations=['Lossless encoding only: no stronger security bound or fewer sampled checks.',
            'Degree at most 1024 in the current source implementation.',
            'PCS proof only; no full NEAR/recursive GKR/QROM certification.',
            'Canonical configuration byte accounting and actual external JSON file accounting both reported.'],
        source_sha256={name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
            for name in ['pq384_ext8_rate_shift_codec.py','pq384_ext8_rate_shift_continuation.py',Path(__file__).name]})
    (args.output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(status='PASS', cases=[dict(case=x['case'], proof_bytes=x['proof_bytes'],
        total_required_input_bytes=x['total_required_input_bytes']) for x in reports], negative_checks=len(negatives)), indent=2))


if __name__ == '__main__':
    main()
