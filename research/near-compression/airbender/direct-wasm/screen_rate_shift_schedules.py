"""Screen single-shift schedules using the checked joint ideal error bound.

Geometry simulation is calibrated against every existing actual codec fixture.
Alternate schedules/degrees are not implemented or quantum-security certified.
"""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import random
from estimate_ext8_multiproof_geometry import frontier, measure as baseline_measure
import pq384_ext8_rate_shift_codec as codec

P = codec.r.e.P
ROOT = Path(__file__).resolve().parents[2]


def parameters(degree, skipped, rate):
    n = 4*degree
    d = degree//(2**skipped)
    folded = n//(2**skipped)
    target_domain = rate*d
    assert degree % (2**skipped) == 0 and d >= 2
    assert n <= 2**27 and target_domain <= 2**27
    threshold = (2*n+degree)//3+1
    minimum = (threshold+2**skipped-1)//(2**skipped)
    target_threshold = (2*target_domain+d)//3+1
    radius = target_domain-target_threshold
    assert 2*radius+d <= target_domain
    assert threshold <= 2**skipped*minimum
    source_ratio = F(minimum-1, folded)
    target_ratio = F(target_threshold-1, target_domain)
    qs = qc = 1
    while source_ratio**qs > F(1, 2**130):
        qs += 1
    while target_ratio**qc > F(1, 2**130):
        qc += 1
    prior_error = sum(n//(2**j) for j in range(1, skipped+1))
    continuation_error = target_domain-rate
    algebra = F(prior_error+qs+1+continuation_error, P**8)
    bound = algebra+source_ratio**qs+target_ratio**qc
    assert algebra <= F(1, 2**130) and bound <= F(1, 2**128)
    return dict(degree=degree, skipped=skipped, rate=rate, next_degree=d,
        source_domain=n, folded_domain=folded, next_domain=target_domain,
        threshold=threshold, minimum=minimum, target_threshold=target_threshold,
        radius=radius, source_queries=qs, continuation_queries=qc,
        ideal_error_bound_float=float(bound))


def geometry(degree, skipped, rate, source_samples, continuation_samples):
    next_degree = degree//(2**skipped)
    folded_domain = 4*next_degree
    source_indices = {i+j*folded_domain for i in source_samples for j in range(2**(skipped-1))}
    source_leaf = 8*len(source_indices)
    source_hash = 48*frontier(source_indices, 2*degree)
    leaf_bytes, hash_bytes = 0, 0
    d = next_degree
    while d > 1:
        count = rate*d//2
        indices = {s % count for s in continuation_samples}
        leaf_bytes += 64*len(indices)
        hash_bytes += 48*frontier(indices, count)
        d //= 2
    # Matches NRS8MP01; other schedules would need at least a config binding.
    header = 8+48+96*skipped+48+32+144*(next_degree.bit_length()-1)+32
    return dict(proof_bytes=header+source_leaf+source_hash+leaf_bytes+hash_bytes,
        header_bytes=header, source_leaf_bytes=source_leaf, source_hash_bytes=source_hash,
        continuation_leaf_bytes=leaf_bytes, continuation_hash_bytes=hash_bytes)


def run():
    calibration = []
    for path in sorted((ROOT/'results/rate-shift-continuation').glob('d*.json')):
        env = json.loads(path.read_text())
        proof, cfg, root, qc = env['proof'], env['config'], bytes.fromhex(env['root']), env['continuation_queries']
        prefix = codec.r.prefix_metadata(proof, cfg, root, qc)
        source_samples = prefix[8]
        _, _, _, samples, _ = codec.r.continuation_metadata(proof, cfg, root, qc, prefix)
        measured = codec.breakdown(proof, cfg, root, qc)['proof_bytes']
        predicted = geometry(cfg['degree'], 2, 8, source_samples, samples)['proof_bytes']
        assert predicted == measured
        calibration.append(dict(fixture=path.name, bytes=measured))
    rows, summaries = [], []
    for degree in [1024, 8192, 131072, 1048576]:
        for skipped in [1, 2, 3, 4, 6, 8]:
            for rate in [2, 4, 8, 16, 32]:
                params = parameters(degree, skipped, rate)
                trials = []
                for seed in range(4):
                    srng, crng = random.Random(seed), random.Random(seed+1000)
                    source_samples = [srng.randrange(params['folded_domain']) for _ in range(params['source_queries'])]
                    samples = [crng.randrange(params['next_domain']) for _ in range(params['continuation_queries'])]
                    trials.append(geometry(degree, skipped, rate, source_samples, samples))
                sizes = [t['proof_bytes'] for t in trials]
                rows.append(dict(**params, min_bytes=min(sizes), max_bytes=max(sizes),
                    mean_bytes=sum(sizes)/len(sizes), trials=trials))
        candidates = [r for r in rows if r['degree'] == degree]
        best = min(candidates, key=lambda r: r['mean_bytes'])
        baseline = [baseline_measure(degree, 314, seed)['estimated_payload_bytes']+8 for seed in range(4)]
        summaries.append(dict(degree=degree, best_skipped=best['skipped'], best_rate=best['rate'],
            source_queries=best['source_queries'], continuation_queries=best['continuation_queries'],
            best_min_bytes=best['min_bytes'], best_max_bytes=best['max_bytes'],
            baseline_min_bytes=min(baseline), baseline_max_bytes=max(baseline),
            scalar_coefficients_only_bytes=4*degree,
            best_source_leaf_fraction_min=min(t['source_leaf_bytes']/(16*degree) for t in best['trials']),
            best_source_leaf_fraction_max=max(t['source_leaf_bytes']/(16*degree) for t in best['trials']),
            tested_schedules_below_300000_all_seeds=sum(r['max_bytes'] < 300000 for r in candidates)))
    report = dict(status='CALIBRATED_GEOMETRY_SCREEN_ONLY', calibration=calibration, summaries=summaries,
        schedules=rows, security='Exact rational joint ideal error <= 2^-128; two tails individually <= 2^-130.',
        limitations=['Deterministic simulated independent uniform queries; four seeds, not a distributional theorem.',
            'Only two skipped folds/rate8 up to degree1024 are executable; other schedules are hypothetical.',
            'Framing follows current codec; external config, GKR, recursion, AIR and full NEAR excluded.',
            'Field/root geometry and causal transcript still required; no commitment or QROM certification.',
            'A single rate shift is screened; no lower bound on multishift protocols or other schemes.',
            'Raw scalar coefficient disclosure costs 4D bytes but requires linear-size source reconstruction; small-degree wins are not evidence of succinct scaling.'],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'results/rate-shift-schedule-screen.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(summaries, indent=2))


if __name__ == '__main__':
    run()
