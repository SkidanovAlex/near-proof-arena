"""Generate the fixed captured-slice Lean geometry certificate (not security)."""
import argparse
import hashlib
import json
from pathlib import Path


def generate(path):
    raw = path.read_bytes()
    meta = json.loads(raw)
    def record(values):
        if any(type(v) is not int or v < 0 for v in values.values()):
            raise ValueError('expected natural metadata')
        return '{ ' + ', '.join(f'{k} := {v}' for k, v in values.items()) + ' }'
    return '''import NearCompression.GKRSlotCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace NearCompression
/-! Fixed captured fixture only. Compiler-export correspondence is checked by
check_heterogeneous_metadata.py, not proved by this numerical certificate.
Metadata SHA256: ''' + hashlib.sha256(raw).hexdigest() + ''' -/
def literal193GKRLayout : GKRJointLayout := ''' + record(meta['layout']) + '''
def literal193GKRTables : List GKRTableMetadata := [
''' + ',\n'.join(record(t) for t in meta['tables']) + ''']
def literal193GKRLanes : List GKRSourceLane := literal193GKRTables.flatMap gkrMetadataLanes

theorem literal193_gkr_lanes_well_formed :
    ∀ lane∈literal193GKRLanes,lane.WellFormed literal193GKRLayout := by
  exact checked_metadata_all_lanes literal193GKRLayout literal193GKRTables (by decide)

theorem literal193_gkr_lane_selectors :
    CanonicalLaneSelectors literal193GKRLayout literal193GKRLanes := by
  exact checked_lane_selectors literal193GKRLayout literal193GKRLanes (by decide)
end NearCompression
'''


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('metadata', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    args.output.write_text(generate(args.metadata))
