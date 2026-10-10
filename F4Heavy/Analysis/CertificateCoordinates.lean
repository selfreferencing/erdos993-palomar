module

public import F4Heavy.Analysis.MatrixSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem activity_projective_interval (a b lam : ℝ) (ha : 0 < 1+a)
    (hlam : a ≤ lam ∧ lam ≤ b) :
    a/(1+a) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ b/(1+b) := by
  have hlamd : 0 < 1+lam := by linarith only [ha, hlam.1]
  have hbd : 0 < 1+b := by linarith only [hlamd, hlam.2]
  constructor
  · apply (div_le_div_iff₀ ha hlamd).mpr
    nlinarith only [hlam.1]
  · apply (div_le_div_iff₀ hlamd hbd).mpr
    nlinarith only [hlam.2]

theorem activity_projective_inverse (lam : ℝ) (hd : 1+lam ≠ 0) :
    (lam/(1+lam))/(1-lam/(1+lam)) = lam := by
  field_simp
  ring

theorem parent_interval_parameter (l x : ℝ) (hl : l < 1) (hx : l ≤ x ∧ x ≤ 1) :
    0 ≤ (x-l)/(1-l) ∧ (x-l)/(1-l) ≤ 1 ∧ l+(1-l)*((x-l)/(1-l)) = x := by
  have hd : 0 < 1-l := sub_pos.mpr hl
  refine ⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le, (div_le_one hd).mpr ?_, ?_⟩
  · linarith only [hx.2]
  · field_simp
    ring

end F4Heavy.Analysis
