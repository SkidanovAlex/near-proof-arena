import ZkFormal.NearV3.Render.PaddedMrk
import ZkFormal.NearV3.Assembly.LinkV3
import ZkFormal.NearV3.Render.PaddedSort

/-! Guard the assumptions of the aligned `mrk` (table 23) and `sort` (table 24) generators. -/

/-- info: 'ZkFormal.NearV3.Render.mrk_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.mrk_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.sort_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.sort_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.sort_aligned_complete19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.sort_aligned_complete19

/-- info: 'ZkFormal.NearV3.Render.sort_receipts_aligned_complete19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.sort_receipts_aligned_complete19


/-- info: 'ZkFormal.NearV3.Render.mrk_v3_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.mrk_v3_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.SortV3.sort_v3_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.SortV3.sort_v3_aligned_complete

/-- info: 'ZkFormal.NearV3.Candidates.SortEmpty.sortV3_empty_or_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.SortEmpty.sortV3_empty_or_old

/-- info: 'ZkFormal.NearV3.Assembly.mrkView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.mrkView

/-- info: 'ZkFormal.NearV3.Assembly.v3Records_of_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.v3Records_of_holdsP

/-- info: 'ZkFormal.NearV3.Render.SortV3.sort_v3_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.SortV3.sort_v3_accepted
