"""Replay the frozen-workload, free-column DAG-layout sensitivity screen."""
import json
from pathlib import Path
from screen_swirl_stacking_geometry import cost

root = Path(__file__).resolve().parents[2]
report = json.loads((root/'results/swirl-security-review/dag-trace/report.json').read_text())
options = []
for height in range(15, 26):
    for rate in range(2, 28-height):
        for fold in range(1, 9):
            for terminal in range(1, 13):
                if height-((height-terminal+fold-1)//fold)*fold < 0:
                    continue
                options.append(cost(report['common_cells'], 0, height, rate, fold,
                    terminal, 9, 52, public_cached=True, remove_columns=True,
                    constraint_fixed=161, framing_base=905))
assert len(options) == report['screened']
assert min(options, key=lambda x: x['expected_frontier_bytes']) == report['best_frozen_free_column_screen']
print('PASS: DAG trace screen replay; not a soundness certificate')
