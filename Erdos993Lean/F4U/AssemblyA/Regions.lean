module

public import Erdos993Lean.F4U.AssemblyA.Minimum

/-! The closed light/heavy split in the frozen F4 contract. -/

@[expose] public section

namespace F4Unified.Assembly

 theorem lam_pos_of_inRow {r : Row} {lam : ℝ} (h : InRow r lam) : 0 < lam := by
  cases r <;> norm_num [InRow, rowData] at h <;> linarith

 theorem parentH_le_q_iff_one_le_parentX {lam Y : ℝ} (hlam : 0 < lam) :
    parentH Y ≤ q lam ↔ 1 ≤ parentX lam Y := by
  have hd : 0 < 1 + lam := by linarith
  unfold parentH q parentX
  rw [le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

#print axioms lam_pos_of_inRow
#print axioms parentH_le_q_iff_one_le_parentX

end F4Unified.Assembly
