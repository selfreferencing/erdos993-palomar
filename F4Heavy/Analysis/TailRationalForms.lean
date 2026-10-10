module

public import F4Heavy.Analysis.TailDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_child_h0_identity (lam : ℝ) (hl : 0 < lam) :
    tailChildH0 lam = 6 * (2 + lam) / (lam ^ 2 + 12 * lam + 12) := by
  have hQ : 12 + lam * 12 + lam ^ 2 ≠ 0 := by positivity
  unfold tailChildH0 q
  field_simp
  <;> ring_nf
  <;> field_simp [hQ]
  <;> ring

end F4Heavy.Analysis
