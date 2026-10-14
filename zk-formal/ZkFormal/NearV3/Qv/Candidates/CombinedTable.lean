import ZkFormal.NearV3.Qv.Candidates.ValueTable
import ZkFormal.Size.Model
import ZkFormal.NearV3.Qv.Candidates.CombinedTableDefs

/-! Executable combined read/parser candidate, not admitted. Walk rows precede
parser records and reuse raw-empty marker rows. The parser length cell holds the
read mode on walk rows; virtualizing it to zero preserves the marker equations.
Global extraction, honest rendering and native capacity remain obligations. -/
namespace ZkFormal.NearV3.Qv.Candidates.CombinedTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl
open ValueTable

theorem shape_g2 : ZkFormal.Size.shapeOf 2 table = ⟨52,8,6,8,22⟩ := by decide +kernel
theorem table_wf : table.wf ⟨[table],64,30⟩ 6 = true := by decide +kernel

end ZkFormal.NearV3.Qv.Candidates.CombinedTable
