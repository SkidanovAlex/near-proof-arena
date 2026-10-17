"""Reconcile retained evidence and architecture break-even; never certify security."""
import hashlib
import json
from pathlib import Path
from screen_larger_field_code_switch import ledger

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent.parent
TARGET = 300000


def build(root=ROOT):
    evidence = {}
    def read(relative):
        path = root / relative
        raw = path.read_bytes()
        evidence[relative] = hashlib.sha256(raw).hexdigest()
        return json.loads(raw)
    bundle = 'results/ext8-switch-execution-q309/'
    manifest = read(bundle+'manifest.json')
    # Validate the measured bundle and the exact executable sources against its capture.
    for relative, expected in manifest['files'].items():
        raw = (REPO/relative).read_bytes()
        if hashlib.sha256(raw).hexdigest() != expected:
            raise ValueError('capture manifest mismatch: '+relative)
    measured = read(bundle+'report.json')
    prover = read(bundle+'prover-report.json')
    codec = read(bundle+'codec-report.json')
    config = read(bundle+'config.json')
    assert measured['status']=='PASS' and measured['fresh_conjunction_verified']
    assert prover['status']=='PASS' and prover['fresh_execution_verified']
    assert codec['status']=='PASS' and codec['roundtrip']
    sizes = {
        'compression_envelope_bytes': (root/bundle/'compression.bin').stat().st_size,
        'call_proof_bytes': (root/'results/call-ext8-shared-q309/proof.bin').stat().st_size,
        'receipt_bytes': (root/'results/ext8-affine-q309/receipt.json').stat().st_size,
        'calls_bytes': (root/'results/ext8-linked-calls/calls.json').stat().st_size,
    }
    for key, value in sizes.items():
        assert measured[key] == value, key
    total = sum(sizes.values())
    assert total == measured['combined_bytes']
    breakdown = prover['breakdown']
    costs = {'opening_header_terminal': breakdown['header_and_terminal_bytes']}
    for kind, prefix in (('packed-source','source'), ('scalar-coset','continuation')):
        groups = [g for g in breakdown['groups'] if g['kind'] == kind]
        costs[prefix+'_values'] = sum(g['leaf_bytes'] for g in groups)
        costs[prefix+'_authentication'] = sum(g['sibling_bytes'] for g in groups)
    opening = sum(costs.values())
    assert opening == breakdown['total_bytes'] == codec['opening_bytes'] == prover['compression_opening_bytes']
    costs['local_gkr_and_framing'] = sizes['compression_envelope_bytes']-opening
    assert costs['local_gkr_and_framing'] == prover['reduction_and_framing_bytes']
    costs.update({k.removesuffix('_bytes'):v for k,v in sizes.items() if k!='compression_envelope_bytes'})
    assert sum(costs.values()) == total
    removed = {
        'source_values_and_authentication': costs['source_values']+costs['source_authentication'],
        'continuation_values_and_authentication': costs['continuation_values']+costs['continuation_authentication'],
        'all_opening_authentication': costs['source_authentication']+costs['continuation_authentication'],
        'entire_opening': opening,
        'entire_compression_envelope': sizes['compression_envelope_bytes'],
        'entire_bundle': total,
    }
    replacement = []
    for name, size in removed.items():
        fixed = total-size
        allowance = TARGET-1-fixed
        replacement.append(dict(replaced_component=name,removed_bytes=size,
            fixed_remainder_bytes=fixed,maximum_replacement_bytes_for_strict_target=allowance,
            possible_even_with_free_replacement=allowance>=0,
            scope='Accounting only; no ability to delete or securely replace this component is assumed.'))
    screen = read('results/larger-field-code-switch-screen.json')
    candidates = []
    for case in screen['results']:
        recomputed = ledger(case['best']['path'],case['extension'],case['assumed_log2_C'])
        assert recomputed == case['conditional_ledger']
        sizes_screen = [t['bytes']+case['best']['fixed_bytes'] for t in case['trials']]
        assert min(sizes_screen)==case['min_subtotal_bytes'] and max(sizes_screen)==case['max_subtotal_bytes']
        candidates.append(dict(extension=case['extension'],hash_bytes=case['hash_bytes'],
            assumed_log2_C=case['assumed_log2_C'],isolated_query_bits=case['isolated_query_bits'],
            min_projected_subtotal_bytes=min(sizes_screen),max_projected_subtotal_bytes=max(sizes_screen),
            partial_conditional_quantum_bound_passes=recomputed['partial_within_half_success'],
            projected_subtotal_under_target=min(sizes_screen)<TARGET,
            minimum_savings_to_strict_target_before_excluded_costs=max(0,min(sizes_screen)-(TARGET-1))))
    feasible = [c for c in candidates if c['partial_conditional_quantum_bound_passes'] and c['projected_subtotal_under_target']]
    historical_recursive = read('results/recursive-pcs-root/report.json')
    recursive = read('results/recursive-single-root-root/report.json')
    bounded_merkle = read('results/private-merkle-proof-q8/report.json')
    bounded_screen = read('results/bounded-merkle-break-even.json')
    from screen_bounded_merkle_break_even import build as bounded_build
    assert bounded_screen == bounded_build()
    scope = read('scope-report.json')
    hash_work = read('results/switch-full-verifier-hash-work.json')
    assert hash_work['fresh_verifier_passed']
    assert hash_work['compression_envelope_bytes']==sizes['compression_envelope_bytes']
    assert hash_work['call_proof_bytes']==sizes['call_proof_bytes']
    for relative, expected in hash_work['input_sha256'].items():
        assert hashlib.sha256((root/relative).read_bytes()).hexdigest()==expected
    response_screen = read('results/response-transcript-screen.json')
    response_totals = response_screen['measurement']['totals']
    assert response_screen['fresh_verifier_passed']
    assert all(response_totals[k] == value for k, value in hash_work['measurement']['totals'].items())
    assert response_totals['unique_blocks_saved'] == response_totals['unique_blocks'] - response_totals['candidate_unique_blocks']
    for relative, expected in response_screen['input_sha256'].items():
        assert hashlib.sha256((root/relative).read_bytes()).hexdigest() == expected
    assert hashlib.sha256((root/'airbender/direct-wasm/screen_response_transcript.py').read_bytes()).hexdigest() == response_screen['measurement']['encoding_source_sha256']
    derivation = read('results/derived-transcript-bindings.json')
    assert derivation['status'] == 'OMISSION_COUNTEREXAMPLES_CONFIRMED' and not derivation['protocol_changed']
    assert derivation['terminal']['different_layouts'] and derivation['terminal']['existing_begin_seeds_distinct']
    assert derivation['stage']['weights_define_distinct_functionals'] and derivation['stage']['existing_start_seeds_distinct']
    for relative, expected in derivation['sha256'].items():
        assert hashlib.sha256((root/relative).read_bytes()).hexdigest() == expected
    ds = derivation['optimistic_hash_screen']
    assert ds['original_unique_blocks'] == hash_work['measurement']['totals']['unique_blocks']
    assert ds['remaining_unique_blocks'] == ds['original_unique_blocks'] - ds['erased_layout_and_stage_tag_blocks'] - response_totals['unique_blocks_saved']
    nibble = read('results/sha384-nibble-circuit.json')
    assert nibble['status'] == 'COMPLETE_COMPRESSION_RELATION_CHECKED'
    assert nibble['exhaustive_lookup_relation_rows'] == nibble['fixed_lookup_table_rows']
    for relative, expected in nibble['sha256'].items():
        assert hashlib.sha256((REPO/relative).read_bytes()).hexdigest() == expected
    row_plan = read('results/sha384-nibble-row-plan.json')
    assert row_plan['status'] == 'ROW_ROUTING_CHECKED_COSTS_PROJECTED'
    for relative, expected in row_plan['sha256'].items():
        assert hashlib.sha256((root/relative).read_bytes()).hexdigest() == expected
    for case in row_plan['trials']:
        assert case['candidate_cells'] == case['candidate_execution_cells'] + case['fixed_lookup_cells'] + case['fixed_range_cells']
    lookup_air = read('results/sha384-nibble-lookup-air.json')
    assert lookup_air['status'] == 'FIXED_LOOKUP_AIR_FULL_WITNESS_CHECKED'
    fixed_shapes = [s for s in lookup_air['table_shapes'] if s['name'].endswith('/fixed')]
    assert lookup_air['fixed_truth_rows_checked'] == sum(s['rows'] for s in fixed_shapes)
    assert lookup_air['fixed_tables_source_aux_cells'] == sum(s['rows']*(s['source_width']+s['aux_base_width']) for s in fixed_shapes)
    for relative, expected in lookup_air['sha256'].items():
        assert hashlib.sha256((root/relative).read_bytes()).hexdigest() == expected
    phase_air = read('results/sha384-nibble-phase-air.json')
    assert phase_air['status'] == 'COMPLETE_NIBBLE_COMPRESSION_AIR_CHECKED'
    assert phase_air['source_aux_cells'] == sum(s['rows']*(s['source_width']+s['aux_base_width']) for s in phase_air['table_shapes'])
    assert phase_air['compiled_64_block_source_aux_cells'] == sum(s['rows']*(s['source_width']+s['aux_base_width']) for s in phase_air['actual_compiled_64_block_shapes'])
    for relative, expected in phase_air['sha256'].items():
        assert hashlib.sha256((root/relative).read_bytes()).hexdigest() == expected
    nibble64_manifest=read('results/sha384-nibble64/manifest.json')
    for relative, expected in nibble64_manifest['sha256'].items():
        assert hashlib.sha256((root/relative).read_bytes()).hexdigest() == expected
    nibble64=read('results/sha384-nibble64/private-preparation.json')
    assert nibble64['blocks'] == 64 and nibble64['full_witness_verified'] and nibble64['public_field_elements'] == 0
    boundary_test=read('results/sha384-nibble-boundary-air.json')
    for relative, expected in boundary_test['sha256'].items():
        assert hashlib.sha256((root/relative).read_bytes()).hexdigest() == expected
    aux_parity=read('results/ext8-auxiliary-base-parity.json')
    assert aux_parity['status'] == 'EXACT_AUXILIARY_GENERATOR_PARITY' and aux_parity['auxiliary_base_cells_compared'] > 0
    for mapping in ('sha256','input_sha256'):
        for relative, expected in aux_parity[mapping].items():
            assert hashlib.sha256((root/relative).read_bytes()).hexdigest() == expected
    top_hash_tags=sorted(hash_work['measurement']['tags'].items(),key=lambda item:item[1]['unique_blocks'],reverse=True)[:8]
    script_files = [Path(__file__),Path(__file__).with_name('screen_larger_field_code_switch.py'),
        Path(__file__).with_name('screen_weighted_code_switch.py'),Path(__file__).with_name('report_code_switch_algebra.py'),
        Path(__file__).with_name('report_code_switch_qrom.py')]
    for path in script_files: evidence[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return dict(status='NOT_PASSED',purpose='Current decision surface; original full NEAR 1 Pgas/PQ128 objective unchanged.',
        target_bytes_strict=TARGET,measured_fixture=dict(combined_bytes=total,components=costs,
            queries=config['queries'],configuration=config,manifest_pins_checked=len(manifest['files']),
            scope=measured['scope'],security_certified=False,full_near_one_pgas=False,
            verification='Retained conjunction verification evidence pinned by manifest; replay command in source manifest.'),
        replacement_break_even=replacement,counterfactual_candidates=candidates,
        counterfactual_scope=screen['scope'],same_parameters_as_measured_fixture=False,
        screened_candidates_passing_partial_bound_and_size=len(feasible),
        recursion=dict(complete_recursive_proof=recursive['complete_recursive_proof'],
            full_trace_disclosure_needed=recursive['full_trace_required'],
            original_inner_proofs_required=True,prototype_profile=recursive['profile'],
            measured_proof_json_bytes=recursive['proof_json_bytes'],
            original_compact_inner_proof_bytes=recursive['original_compact_inner_proof_bytes'],
            limits=recursive['limits'],
            historical_pcs_only_prototype=dict(full_trace_disclosure_needed=historical_recursive['full_trace_disclosure_needed_for_native_root_link'],
                evidence='results/recursive-pcs-root/report.json')),
        bounded_merkle_verifier_experiment=dict(evidence='results/private-merkle-proof-q8/report.json',
            complete_bounded_merkle_verifier=bounded_merkle['complete_bounded_merkle_verifier'],
            complete_recursive_pcs_verifier=bounded_merkle['complete_recursive_pcs_verifier'],
            quantum_security_certified=bounded_merkle['quantum_security_certified'],queries=bounded_merkle['queries'],
            proof_bytes=bounded_merkle['proof_bytes'],proof_and_public_bytes=bounded_merkle['proof_and_public_bytes'],
            raw_path_bytes=bounded_merkle['original_private_path_bytes'],beats_raw_path_bytes=bounded_merkle['beats_raw_path_bytes'],
            scope=bounded_merkle['scope']),
        bounded_merkle_break_even=bounded_screen,
        latest_verifier_hash_work=dict(totals=hash_work['measurement']['totals'],
            largest_unique_block_tags=dict(top_hash_tags),gadget_accounting=hash_work['current_gadget_accounting'],
            scope=hash_work['scope']),
        response_transcript_screen=dict(totals=response_totals,
            scope=response_screen['measurement']['candidate_scope'],
            decision='Binary response encoding alone saves only 8.94 percent of deduplicated hash blocks. Defer protocol migration; first account for derivation binding of weight vectors and GKR layouts in a complete verifier design.'),
        derived_transcript_binding_audit=dict(evidence='results/derived-transcript-bindings.json',
            required_contracts=derivation['required_contracts'], optimistic_hash_screen=ds,
            decision=derivation['decision'], scope=derivation['scope']),
        nibble_hash_prototype=dict(evidence='results/sha384-nibble-circuit.json',
            witness_cells=nibble['witness_cells'], lookup_requests=nibble['lookup_requests'],
            fixed_lookup_table_rows=nibble['fixed_lookup_table_rows'],
            scope=nibble['scope'], next_gate=nibble['next_gate']),
        nibble_row_plan=dict(evidence='results/sha384-nibble-row-plan.json',
            phase_shapes=row_plan['phase_shapes'],
            candidate_trials=[{k:v for k,v in case.items() if k != 'geometries'} for case in row_plan['trials']],
            scope=row_plan['scope'], decision=row_plan['decision']),
        nibble_fixed_lookup_air=dict(evidence='results/sha384-nibble-lookup-air.json',
            fixed_truth_rows_checked=lookup_air['fixed_truth_rows_checked'],
            source_constraints_evaluated=lookup_air['source_constraints_evaluated'],
            negative_cases=lookup_air['negative_cases'], scope=lookup_air['scope']),
        nibble_composed_air=dict(evidence='results/sha384-nibble-phase-air.json',
            checked_compression_blocks=phase_air['compression_blocks'],
            compiled_64_block_source_aux_cells=phase_air['compiled_64_block_source_aux_cells'],
            compiled_64_block_witness_checked=phase_air['compiled_64_block_witness_checked'],
            scope=phase_air['scope'],
            next_gate='Check a full 64-block witness and generate a proof with complete byte accounting. Replace verbose diagnostic public boundaries with same-root private call binding before evaluating recursive compression.'),
        nibble_64_block_preparation=dict(evidence='results/sha384-nibble64/manifest.json',
            status=nibble64_manifest['status'], full_witness_verified=nibble64['full_witness_verified'],
            source_constraints_evaluated=nibble64['source_constraints_evaluated'],
            source_aux_cells=nibble64['source_aux_cells'],boundary_root=nibble64['boundary_root'],
            scope=nibble64['scope'], proof_captured=False),
        auxiliary_generator_optimization=dict(evidence='results/ext8-auxiliary-base-parity.json',
            cases=aux_parity['cases'],compared_base_cells=aux_parity['auxiliary_base_cells_compared'],
            large_case=aux_parity['large_case'],scope=aux_parity['scope'],
            baseline_prover_changed=False),
        full_near_capacity=dict(target_gas=scope['target_gas'],legacy_cap=scope['legacy_function_call_gas_cap'],
            capacity_ratio=scope['ceil_target_over_legacy_cap'],qualification=scope['capacity_warning']),
        decision=dict(next_experiment=('Implement and measure the surviving projected candidate with all excluded costs and explicit security obligations.' if feasible else 'Stop larger-path proving in the existing 25-block profile: mandatory 416 bytes exceed its at-most-288-byte deduplicated sibling budget. Screen a scalable complete-verifier replacement against the explicit replacement budgets; include transcript/arithmetic and public binding, not authentication alone. Measure a versioned canonical transcript design only with all original bindings accounted for.'),
            standalone_mca_expansion=('REASSESS against the surviving candidate; partial ledger is not certification.' if feasible else 'DEFER pending a named candidate whose complete byte/security ledger makes remaining MCA obligations decisive.'),
            reopen_mca_if='A revised architecture or justified security reduction produces a candidate with explicit full byte headroom and a precise consumer for the missing theorem.',
            do_not_repeat='Same-grid larger-field tuning without changed geometry or security assumptions; latest replay is reproducible but still fails the size screen.',
            limits='Failure of this finite projected family is not an impossibility theorem. Hash-work measurements are not recursive proof-size predictions. Full verifier recursion and PQ128 remain open.'),
        evidence_sha256=evidence)


def main():
    report=build()
    out=ROOT/'results/current-feasibility.json'
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status=report['status'],measured_bytes=report['measured_fixture']['combined_bytes'],
        surviving_screened_candidates=report['screened_candidates_passing_partial_bound_and_size'],
        replacements=report['replacement_break_even']),indent=2))


if __name__=='__main__':main()
