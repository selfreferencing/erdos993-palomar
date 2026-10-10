module

public import Erdos993Lean.BCFG.Generated.GLightLeft.Shape
public import Erdos993Lean.BCFG.Generated.GLightLeft.NormCheck
public import Erdos993Lean.BCFG.Generated.GLightLeft.LowerCheck
public import Erdos993Lean.BCFG.Generated.GLightLeft.IntervalWhole

/-! Generated transcription of G.light.left
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.GLightLeft

theorem intervals_checked : intervalsCheck M lower intervals = true := by
  simp only [intervalsCheck, intervals, List.all_cons, List.all_nil,
    intervalWhole_checked, Bool.and_self]
theorem cover_checked : coverCheck 0 1 intervals = true := by decide +kernel
theorem row_nonnegative : (0 : Rat) ≤ l := by decide +kernel
theorem row_nondegenerate : l < h := by decide +kernel
theorem chart_width_positive : (0 : Rat) < b := by decide +kernel

end Erdos993Lean.BCFG.CertData.GLightLeft
