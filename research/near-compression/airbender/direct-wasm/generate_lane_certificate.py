"""Generate executable Lean checks from captured canonical metadata.
Evaluation is evidence, not a closed kernel proof of each concrete instance.
"""
import argparse
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('metadata', type=Path)
p.add_argument('output', type=Path)
p.add_argument('--all-slots', action='store_true', help='Also check full current/next support disjointness')
a = p.parse_args()
m = json.loads(a.metadata.read_text())
def record(d, fields):
    assert all(type(d[k]) is int and d[k] >= 0 for k in fields)
    return '{ ' + ', '.join(k + ' := ' + str(d[k]) for k in fields) + ' }'
layout = record(m['layout'], ['rowCoordinates','inputLog','commonLog','privateCapacity'])
tables = ',\n'.join(record(t, ['rowLog','rowOffset','blockOffset','columnCapacity','sourceWidth','auxiliaryWidth','sourcePackingLog','auxiliaryPackingLog']) for t in m['tables'])
lanes = ',\n'.join(record(t, ['rowLog','packingLog','rowOffset','inputStart','nextOffset','width','group']) for t in m['lanes'])
text = '''import NearCompression.GKRSlotCertificate
open NearCompression
'''
text += 'def capturedLayout : GKRJointLayout := ' + layout + '\n'
text += 'def capturedTables : List GKRTableMetadata := [' + tables + ']\n'
text += 'def capturedLanes : List GKRSourceLane := [' + lanes + ']\n'
text += '''def main : IO Unit := do
  let lanes := capturedTables.flatMap gkrMetadataLanes
  if !(capturedTables.all (gkrTableMetadataCheck capturedLayout)) then
    throw (IO.userError "table metadata rejected")
  -- Compare all seven lane fields, not just the number of lanes.
  let encode := fun (x : GKRSourceLane) => [x.rowLog,x.packingLog,x.rowOffset,x.inputStart,x.nextOffset,x.width,x.group]
  if lanes.map encode != capturedLanes.map encode then
    throw (IO.userError "canonical lane enumeration mismatch")
  if !(gkrLaneSelectorsCheck capturedLayout lanes) then
    throw (IO.userError "lane selectors rejected")
  let first := gkrLaneAt lanes 0
  let variants := [lanes ++ [first], { first with nextOffset := 0 } :: lanes.drop 1,
    { first with width := 0 } :: lanes.drop 1]
  for bad in variants do
    if gkrLaneSelectorsCheck capturedLayout bad then
      throw (IO.userError "invalid geometry accepted")
  if gkrLaneSelectorsCheck { capturedLayout with inputLog := 0 } lanes then
    throw (IO.userError "invalid envelope accepted")
  IO.println s!"PASS {lanes.length} canonical lanes; 4 malformed geometries rejected"
'''
if a.all_slots:
    text = text.replace('import NearCompression.GKRSlotCertificate', 'import NearCompression.GKRAllSlotCertificate')
    extra = """  if !(gkrAllSlotsDisjointCheck lanes) then
    throw (IO.userError "overlapping canonical support")
  let overlaps := [lanes ++ [first], { first with nextOffset := 0 } :: lanes.drop 1,
    { first with nextOffset := 1 } :: lanes.drop 1,
    lanes ++ [{ first with inputStart := first.inputStart+1 }]]
  for bad in overlaps do
    if gkrAllSlotsDisjointCheck bad then
      throw (IO.userError "overlap accepted")
  -- The old first-slot condition alone misses this interior overlap.
  let interior : GKRSourceLane := { rowLog := 0, packingLog := 3, rowOffset := 0, inputStart := 0, nextOffset := 7, width := 8, group := 0 }
  let small : GKRJointLayout := { rowCoordinates := 0, inputLog := 4, commonLog := 3, privateCapacity := 16 }
  if !(gkrLaneSelectorsCheck small [interior]) then
    throw (IO.userError "interior counterexample failed old check")
  if gkrAllSlotsDisjointCheck [interior] then
    throw (IO.userError "interior overlap accepted")
  IO.println s!"PASS {lanes.length} canonical lanes; full supports disjoint; 5 overlap geometries rejected"
"""
    text += extra

a.output.write_text(text)
