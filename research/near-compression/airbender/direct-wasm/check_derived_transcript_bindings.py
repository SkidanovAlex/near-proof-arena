"""Executable omission counterexamples and scoped contracts for derived hashes.
No protocol changes or cryptographic security claims.
"""
import gzip
import hashlib
import json
from pathlib import Path
import verify_ext8_execution as execution
import ext8_code_switch_stage as stage

ROOT = Path(__file__).resolve().parents[2]


def build():
    base = ROOT/'results/ext8-switch-execution-q309'
    paths = [base/'statement.json.gz', base/'reduction.json.gz',
             ROOT/'results/switch-full-verifier-hash-work.json',
             ROOT/'results/response-transcript-screen.json']
    statement, reduction = [json.loads(gzip.decompress(p.read_bytes())) for p in paths[:2]]
    spec, roots = statement['spec'], statement['roots']
    prefixes = {profile: execution.reduction_prefix(reduction, spec, roots,
                terminal_profile=profile, commitment_profile='phase-pooled-v1')
                for profile in ('baseline', 'affine-v1')}
    a, b = prefixes['baseline'], prefixes['affine-v1']
    assert a[0] == b[0] and a[1].seed == b[1].seed
    layouts = [stage.canonical_json(prefix[-1]) for prefix in (a, b)]
    assert layouts[0] != layouts[1]
    # The existing layout digest distinguishes profiles correctly.
    starts = [execution.gkr.begin(prefix[-1], prefix[1].seed, stage.f.ZERO).seed
              for prefix in (a, b)]
    assert starts[0] != starts[1]
    # Candidate descriptors must at least distinguish the compiler/profile.
    def descriptor(profile):
        return stage.h.hash_parts(b'derived-terminal-binding-CANDIDATE-v1',
            b'compiler-version-required', b'phase-pooled-v1', profile.encode(),
            a[1].seed, stage.extbytes(stage.f.ZERO))
    assert descriptor('baseline') != descriptor('affine-v1')

    cs = [stage.f.ZERO]*4
    namespace = stage.h.hash_parts(b'derivation-audit').hex()
    root = stage.tree(cs, namespace, 2, 1)['root'].hex()
    config = dict(profile=stage.PROFILE, degree=4, blowup=2, fold_bits=1,
                  next_blowup=2, next_fold_bits=0, queries=1,
                  namespace=namespace, parent='00'*48, root=root)
    weights = [[stage.f.ZERO]*4, [stage.f.ONE]*4]
    seeds = [stage.start(config, w, stage.f.ZERO)[0].seed for w in weights]
    assert seeds[0] != seeds[1]
    # Same config, parent and claim; removing external weights collapses them.
    omitted = stage.h.hash_parts(stage.PROFILE.encode(), stage.canonical_json(config),
                                 stage.extbytes(stage.f.ZERO))
    assert stage.algebra.dot([stage.f.ONE]*4, weights[0]) != stage.algebra.dot([stage.f.ONE]*4, weights[1])
    census = json.loads(paths[2].read_text())['measurement']
    response = json.loads(paths[3].read_text())['measurement']['totals']
    targeted = sum(census['tags'][tag]['unique_blocks'] for tag in
                   (stage.PROFILE, execution.gkr.PROFILE.decode()))
    # An intentionally favorable screen: erase all work in these two tags,
    # even scalar/init calls, and also grant shadow response encoding savings.
    remaining = census['totals']['unique_blocks'] - targeted - response['unique_blocks_saved']
    assert remaining > 0
    sources = [Path(__file__), Path(execution.__file__), Path(stage.__file__),
               Path(execution.gkr.__file__),
               Path(__file__).with_name('ext8_terminal_profiles.py'),
               Path(__file__).with_name('ext8_weighted_code_switch.py'),
               Path(__file__).with_name('sha384_call_ext8_pcs.py')]
    return dict(status='OMISSION_COUNTEREXAMPLES_CONFIRMED', protocol_changed=False,
        terminal=dict(same_pre_gkr_seed=a[1].seed.hex(), different_layouts=True,
            layouts=[dict(profile=p, json_bytes=len(raw), sha384=hashlib.sha384(raw).hexdigest())
                     for p, raw in zip(prefixes, layouts)],
            existing_begin_seeds_distinct=True, candidate_profile_descriptors_distinct=True,
            missing_binding='terminal profile / compiler derivation identity'),
        stage=dict(same_config_parent_claim=True, weights_define_distinct_functionals=True,
            existing_start_seeds_distinct=True, omitted_weights_seed=omitted.hex(),
            missing_binding='external initial weights, unless reconstructed inside a closed verifier'),
        optimistic_hash_screen=dict(original_unique_blocks=census['totals']['unique_blocks'],
            erased_layout_and_stage_tag_blocks=targeted,
            granted_response_encoding_savings=response['unique_blocks_saved'],
            remaining_unique_blocks=remaining,
            remaining_dense_gadget_gib=remaining*128*6944*4/2**30,
            scope='All targeted tag work is assumed free, including unrelated small calls. Frozen execution only; new transcript and derivation/routing costs excluded. Not a proof-size bound.'),
        required_contracts=[
            'Terminal: fixed compiler and terminal/commitment profile; spec/public/source roots bound by statement; auxiliary roots/finals bound before local challenges; local rounds bound before terminal derivation; claim bound before GKR challenges.',
            'Call routing: equations derived from bound receipt/calls/spec/use-root and query budget; fixed equation compiler and layerer; standalone GKR API must retain explicit circuit binding.',
            'Weighted adapter: derive initial weights from the input-reduction challenges inside verifier; authenticate responses and bind them before mixers; derive affine folds and injected functional with exact field/shape rules.',
            'Continuations: consume only previous verified derived state; bind schedule, stage geometry, roots, namespace and compiler/profile; never accept a caller-selected replacement weight vector.',
            'Formal consumer: prove each descriptor determines its exact layout/functional for an identical prior transcript, then prove composed acceptance and analyze the new Fiat-Shamir/QROM protocol. Descriptor equality alone is not soundness.'
        ],
        decision='Do not remove hashes at generic GKR/stage APIs. Any new profile must use closed derivation interfaces and retain initial external bindings. Even optimistic removal leaves substantial hash work; require a complete outer-codec byte screen before migration.',
        scope='Concrete implementation dependency counterexamples, not attacks on the unchanged verifier, a new protocol, universal determinism proof, Lean certificate, or PQ128 claim.',
        sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths+sources})


if __name__ == '__main__':
    report = build()
    out = ROOT/'results/derived-transcript-bindings.json'
    out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(status=report['status'], screen=report['optimistic_hash_screen']), indent=2))
