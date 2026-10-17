"""Materialized phase-row/wiring check and optimistic existing-bus cost screen.
Not an AIR: row programs and fixed lookup tables are trusted in this experiment.
"""
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import sha384_nibble_circuit as c
import pq384_ext8_auxiliary as aux
import sha384_nibble_lookup_air as lookup

ROOT = Path(__file__).resolve().parents[2]


def power_rows(n): return 1 << (max(2, n)-1).bit_length()
def bits(n): return max(1, n.bit_length())
def interaction(n): return dict(bus=0, send=True, mult=[['c', 1]]*n, msg=[])
def auxiliary_cells(widths):
    return 8*aux.layout(dict(interactions=[interaction(n) for n in widths]))['aux_columns']


def plan(g):
    constants = set(g.constants.values())
    by_phase = defaultdict(list)
    owner = {}; word_of = {}
    for wi, word in enumerate(g.words):
        for wire in word:
            assert wire not in word_of
            word_of[wire] = wi
    for gate, phase in zip(g.gates, g.gate_phases):
        by_phase[phase].append(gate)
        for wire in gate[2]: owner[wire] = phase
    covered = set(); carries = set()
    for op, ins, outs, _ in g.gates:
        if op == 'add': carries.add(outs[1])
        elif op != 'const': covered.update(ins); covered.update(outs)
    missing = set(range(g.size))-covered-carries-constants
    phases = {}; reads = Counter(); producer = {}
    for phase, gates in by_phase.items():
        external = {w for _, ins, _, _ in gates for w in ins if w not in constants and owner.get(w) != phase}
        word_ids = {word_of[w] for w in external}
        # Route whole words, including any extra nibbles not read by this row.
        imported = {w for wi in word_ids for w in g.words[wi]}
        assert external <= imported
        reads.update(word_ids)
        owned = {w for op, _, outs, _ in gates if op != 'const' for w in outs}
        phases[phase] = dict(wires=sorted(imported|owned), imported_words=sorted(word_ids),
            owned=owned, lookups=sum(op not in ('const','add') for op, _, _, _ in gates), ranges=0, exports=[])
        for wi, word in enumerate(g.words):
            if set(word) <= owned: producer[wi] = phase
    # Assign exactly one range obligation per uncovered wire, on a row holding it.
    for wire in missing:
        phase = next(p for p, r in phases.items() if wire in r['wires'])
        phases[phase]['ranges'] += 1
    for wi, count in reads.items():
        if wi in producer: phases[producer[wi]]['exports'].append((wi, count))
        else: assert all(w < 384 for w in g.words[wi])
    return phases, reads, missing, producer, covered


def materialize(phases, values):
    return {phase: [values[w] for w in row['wires']] for phase, row in phases.items()}


def check_rows(g, phases, source, witness_rows, expected):
    assert len(source) == 384 and set(witness_rows) == set(phases)
    available = {i: tuple(source[w] for w in word) for i, word in enumerate(g.words) if all(w < 384 for w in word)}
    uses = Counter(); constants = {wire: value for value, wire in g.constants.items()}
    gates = defaultdict(list)
    for gate, phase in zip(g.gates, g.gate_phases): gates[phase].append(gate)
    final = None
    for phase, row in phases.items():
        assert len(witness_rows[phase]) == len(row['wires'])
        local = dict(zip(row['wires'], witness_rows[phase])) | constants
        assert all(type(v) is int and 0 <= v < 16 for v in local.values())
        for wi in row['imported_words']:
            assert tuple(local[w] for w in g.words[wi]) == available[wi]
            uses[wi] += 1
        for op, ins, outs, bound in gates[phase]:
            args = [local[w] for w in ins]
            if op == 'const': assert local[outs[0]] == bound
            elif op == 'add':
                assert args[-1] < bound and local[outs[1]] < bound
                assert sum(args) == local[outs[0]]+16*local[outs[1]]
            else: assert local[outs[0]] == c.relation(op, args)
        for wi, _ in row['exports']:
            assert wi not in available
            available[wi] = tuple(local[w] for w in g.words[wi])
        if phase[0] == 'endpoint':
            final = [sum(local[w] << (4*i) for i,w in enumerate(word)) for word in g.outputs]
    assert final == expected
    for row in phases.values():
        for wi, count in row['exports']: assert uses[wi] == count
    return uses


def geometry(rows, width):
    packing = power_rows((width+63)//64) if width > 64 else 1
    while rows*packing < 128: packing *= 2
    return dict(rows=rows, width=width, packing=packing,
                degree=rows*packing, lanes=(width+packing-1)//packing,
                within_current_degree_lane_caps=rows*packing <= 262144 and (width+packing-1)//packing <= 64)


def build():
    g = c.compile_graph(); phases, reads, missing, producers, covered = plan(g)
    source = [i % 16 for i in range(384)]
    values = c.witness(g, source)
    expected = [sum(values[w] << (4*i) for i,w in enumerate(word)) for word in g.outputs]
    rows = materialize(phases, values)
    assert check_rows(g, phases, source, rows, expected) == reads
    rejected = 0
    # Corrupt copies independently, so shared Python storage cannot mask routing errors.
    selected = [next(p for p in phases if p[0] == kind) for kind in ('schedule', 'round', 'endpoint')]
    for phase in selected:
        for index in (0, len(rows[phase])-1):
            old = rows[phase][index]; rows[phase][index] = (old+1) % 16
            try: check_rows(g, phases, source, rows, expected)
            except AssertionError: rejected += 1
            else: raise AssertionError('accepted altered row copy')
            rows[phase][index] = old
    categories = defaultdict(list)
    for phase, row in phases.items():
        categories[phase[0]].append(dict(source=len(row['wires'])+2,
            accumulator=auxiliary_cells([1]*(row['lookups']+row['ranges']+len(row['imported_words'])) + [bits(n) for _,n in row['exports']] + ([1]*8 if phase[0] == 'endpoint' else [])),
            lookup_requests=row['lookups'], range_requests=row['ranges'],
            imported_words=len(row['imported_words']), exported_words=len(row['exports'])))
    shapes = {name:dict(rows_per_block=len(rows), source_width=max(r['source'] for r in rows),
                       aux_base_width=max(r['accumulator'] for r in rows)) for name, rows in categories.items()}
    # Input/output state and message boundary table:24 input words and8 output
    # words;32 cells for two word copies plus identifiers/active. Output-boundary
    # links and profile semantics are not implemented, so charge two interactions.
    shapes['boundary'] = dict(rows_per_block=32, source_width=34,
        aux_base_width=auxiliary_cells([1, bits(max(reads.values()))]))
    trials=[]
    for blocks in (1, 4, 16, 25, 64, 256, 1024):
        execution = sum(power_rows(s['rows_per_block']*blocks)*(s['source_width']+s['aux_base_width']) for s in shapes.values())
        lookup_bits=bits(18688*blocks)
        fixed_tables={op: lookup.fixed_table(op,lookup_bits) for op in (*lookup.OPS,'range')}
        fixed_costs={op:(1<<table['maxLog'])*(table['width']+8*aux.layout(table)['aux_columns']) for op,table in fixed_tables.items()}
        fixed_lookup = sum(value for op,value in fixed_costs.items() if op != 'range')
        fixed_range = fixed_costs['range']
        # Existing core/endpoint source plus existing three/three bus interactions.
        old_core = power_rows(80*blocks)*(5234+auxiliary_cells([1]*3))
        old_endpoint = power_rows(blocks)*(1666+auxiliary_cells([1]*3))
        total=execution+fixed_lookup+fixed_range
        geometries = {name: {kind:geometry(power_rows(s['rows_per_block']*blocks),s[key])
            for kind,key in [('source','source_width'),('auxiliary','aux_base_width')]} for name,s in shapes.items()}
        for op,table in fixed_tables.items():
            geometries['fixed_'+op]=dict(source=geometry(1<<table['maxLog'],table['width']),
                auxiliary=geometry(1<<table['maxLog'],8*aux.layout(table)['aux_columns']))
        trials.append(dict(blocks=blocks, candidate_cells=total, candidate_execution_cells=execution,
            fixed_lookup_cells=fixed_lookup, fixed_range_cells=fixed_range,
            existing_core_endpoint_cells=old_core+old_endpoint,
            candidate_over_existing=total/(old_core+old_endpoint),
            within_current_degree_lane_caps=all(x['within_current_degree_lane_caps'] for pair in geometries.values() for x in pair.values()),
            within_local_row_cap=all(x['rows'] <= 8192 for pair in geometries.values() for x in pair.values()),
            geometries=geometries))
    sources=[Path(__file__),Path(c.__file__),Path(aux.__file__),Path(lookup.__file__)]
    return dict(status='ROW_ROUTING_CHECKED_COSTS_PROJECTED', phase_shapes=shapes,
        routed_word_reads=sum(reads.values()), routed_word_definitions=len(reads),
        maximum_word_fanout=max(reads.values()), extra_range_checks=len(missing),
        lookup_implicit_range_wires=len(covered), independent_row_mutations_rejected=rejected,
        trials=trials, rejected_multiplicity_cases=[dict(blocks=4096,required_bits=bits(18688*4096),maximum_bits=25)],
        scope='Materialized static phase-row wiring with exact word fanout; existing Ext8 bus auxiliary formulas. NOT an AIR or proof. Per-phase schedules and wire addresses are trusted. Fixed lookup table cost now uses the implemented polynomial AIR; its composition with phases is not implemented. Cost excludes phase-program enforcement, public/call routing, lookup soundness, LDE/Merkle/PCS/GKR. Old comparator excludes corresponding call routing too. Dimensions may exceed existing packing/degree limits. No secure-size or runtime prediction.',
        decision='Evaluate the structured phase-row AIR with whole-word routing. Connect phase row programs and requests to the implemented fixed-table AIR before interpreting any projected saving. Keep full NEAR/PQ128/300KB gate NOT_PASSED.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})


if __name__ == '__main__':
    report=build(); (ROOT/'results/sha384-nibble-row-plan.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
