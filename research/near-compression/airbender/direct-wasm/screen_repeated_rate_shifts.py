"""Conditional multi-shift design screen with exact expected Merkle geometry.

The repeated protocol/inductive soundness composition is NOT implemented or
proved here. Arithmetic budgets are conditional on that composition. Every
intermediate source is Ext8, never incorrectly priced as scalar.
"""
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import random
from estimate_ext8_multiproof_geometry import frontier
from pq384_ext8_reference import P

ROOT = Path(__file__).resolve().parents[2]
RATES = (2, 4, 8, 16, 32)
TAIL_BITS = 134  # <=20 stages, with two allocations per stage: 40/64 < 1.


@lru_cache(None)
def expected_geometry(domain, queries):
    """Expected unique leaves and minimal sibling frontier for uniform draws."""
    assert domain >= 2 and domain & (domain-1) == 0 and queries > 0
    leaves = domain*(1-F(domain-1, domain)**queries)
    hashes = F(0)
    span = 1
    while span < domain:
        hashes += (domain//span)*(F(domain-span, domain)**queries-F(domain-2*span, domain)**queries)
        span *= 2
    return leaves, hashes


@lru_cache(None)
def stage(degree, rate, skipped, scalar):
    n = degree*rate
    folded_domain = n//(2**skipped)
    threshold = (2*n+degree)//3+1
    minimum = (threshold+2**skipped-1)//(2**skipped)
    ratio = F(minimum-1, folded_domain)
    assert ratio < 1
    queries = 1
    while ratio**queries > F(1, 2**TAIL_BITS):
        queries += 1
    leaves, hashes = expected_geometry(folded_domain, queries)
    copies = 2**(skipped-1)
    header = 96*skipped+48+32
    width = 8 if scalar else 64
    cost = header+copies*(width*leaves+48*hashes)
    algebra = F(sum(n//(2**i) for i in range(1, skipped+1))+queries+1, P**8)
    assert algebra <= F(1, 2**TAIL_BITS)
    return dict(degree=degree, rate=rate, skipped=skipped, queries=queries,
        threshold=threshold, minimum=minimum, folded_domain=folded_domain,
        scalar=scalar, header=header, copies=copies, width=width,
        cost=cost, error=algebra+ratio**queries)


@lru_cache(None)
def optimize(degree, rate, scalar=False, terminal_cap=None):
    # Direct disclosure reconstructs the whole root and exact functional;
    # verifier work is linear/FFT-size. It is a baseline, not succinct scaling.
    best_cost = F((4 if scalar else 32)*degree) if terminal_cap is None or degree <= terminal_cap else F(2**100)
    best_path = ()
    for skipped in range(1, min(8, degree.bit_length()-1)+1):
        edge = stage(degree, rate, skipped, scalar)
        next_degree = degree//(2**skipped)
        for next_rate in RATES:
            if next_rate*next_degree > 2**27:
                continue
            next_threshold = (2*next_rate*next_degree+next_degree)//3+1
            radius = next_rate*next_degree-next_threshold
            assert 2*radius+next_degree <= next_rate*next_degree
            child_cost, child_path = optimize(next_degree, next_rate, False, terminal_cap)
            cost = edge['cost']+child_cost
            if cost < best_cost:
                best_cost = cost
                best_path = ((degree, rate, skipped, scalar, next_rate),)+child_path
    return best_cost, best_path


def simulate(path, degree, seed):
    rng = random.Random(seed)
    total, rows = 56, []  # version + external root; configuration excluded
    current, scalar = degree, True
    for d, rate, skipped, is_scalar, next_rate in path:
        assert d == current and is_scalar == scalar
        edge = stage(d, rate, skipped, is_scalar)
        domain = edge['folded_domain']
        samples = [rng.randrange(domain) for _ in range(edge['queries'])]
        indices = {i+j*domain for i in samples for j in range(edge['copies'])}
        leaf_bytes = edge['width']*len(indices)
        hash_bytes = 48*frontier(indices, d*rate//2)
        total += edge['header']+leaf_bytes+hash_bytes
        rows.append(dict(degree=d, rate=rate, skipped=skipped, next_rate=next_rate,
            queries=edge['queries'], scalar_source=is_scalar,
            leaf_bytes=leaf_bytes, hash_bytes=hash_bytes, header_bytes=edge['header']))
        current //= 2**skipped
        scalar = False
    terminal_bytes = (4 if scalar else 32)*current
    return dict(bytes=total+terminal_bytes, terminal_degree=current,
        terminal_bytes=terminal_bytes, stages=rows)


def run():
    checked = 0
    # Independent exhaustive expectation checks, including duplicate draws.
    for domain in [2, 4, 8]:
        for queries in range(1, 5):
            tuples = list(itertools.product(range(domain), repeat=queries))
            leaves = F(sum(len(set(t)) for t in tuples), len(tuples))
            hashes = F(sum(frontier(t, domain) for t in tuples), len(tuples))
            assert expected_geometry(domain, queries) == (leaves, hashes)
            # Replicated cosets have no extra frontier above their block roots.
            for copies in [1, 2, 4]:
                for t in tuples[:32]:
                    indices = {i+j*domain for i in t for j in range(copies)}
                    assert frontier(indices, copies*domain) == copies*frontier(t, domain)
                    checked += 1
    rows = []
    for degree, terminal_cap in itertools.product([1024, 8192, 131072, 1048576], [None, 64]):
        cost, path = optimize(degree, 4, True, terminal_cap)
        error = sum((stage(d, rate, skipped, scalar)['error'] for d, rate, skipped, scalar, _ in path), F(0))
        assert len(path) <= 20 and error <= F(1, 2**128)
        trials = [simulate(path, degree, seed) for seed in range(8)]
        rows.append(dict(degree=degree, terminal_degree_cap=terminal_cap, expected_bytes=float(cost+56),
            min_bytes=min(t['bytes'] for t in trials), max_bytes=max(t['bytes'] for t in trials),
            scalar_disclosure_bytes=4*degree+56, conditional_ideal_error=float(error),
            path=[dict(degree=d, rate=b, skipped=k, scalar=scalar, next_rate=nb)
                  for d, b, k, scalar, nb in path], trials=trials))
    report = dict(status='CONDITIONAL_DESIGN_SCREEN_NOT_PROTOCOL_PROOF', rows=rows,
        exhaustive_expectation_cases=12, coset_replication_checks=checked, rates=RATES, maximum_skipped_folds=8,
        per_tail_bits=TAIL_BITS, cache_states=optimize.cache_info().currsize,
        composition_obligation='Prove a rate-shift step preserves absence of a candidate outside its bad event, then induct over adaptively chosen prefix transcripts. Existing CheckedRateShiftComposition ends in a plain fold continuation, not another rate shift.',
        limitations=['Exact expected geometry under independent uniform ideal sampling; eight simulations of selected schedule.',
            'Every post-first-stage leaf is priced as 64 bytes (paired Ext8).',
            'Terminal coefficient disclosure entails source-size verifier reconstruction, not a succinct-verifier claim.',
            'Schedule is selected by minimum expectation over this finite grid, not a protocol lower bound.',
            'External configuration, recursive GKR, NEAR state transitions, commitment/QROM costs excluded.',
            'Ideal error sum is conditional on the still-unproved repeated-step composition and correct transcript binding.'],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'results/repeated-rate-shift-screen.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps([{k: v for k, v in r.items() if k != 'trials'} for r in rows], indent=2))


if __name__ == '__main__':
    run()
