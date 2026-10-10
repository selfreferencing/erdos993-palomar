module

public import F4Heavy.Analysis.ScaledPayment
public import F4Heavy.Analysis.ParentBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dhParentBase (r : Row) (lam Y : ℝ) : ℝ :=
  gamma r lam*(1-p lam Y/2-(p lam Y)^2/12)

noncomputable def dhParentUpper (r : Row) (lam Y rho : ℝ) : ℝ :=
  dhParentBase r lam Y+(1-p lam Y)*rho

noncomputable def dhTangent (r : Row) (lam Y : ℝ) : ℝ :=
  match r with
  | .D => 33/40
  | .H => 1-parentX lam Y/8
  | _ => 3/4

theorem dh_parent_base_positive (r : Row) (lam Y : ℝ) (hr : InRow r lam) :
    0 < dhParentBase r lam Y := by
  have hp := p_pos lam Y (inRow_activity_pos r lam hr)
  have hp1 := p_lt_one lam Y (inRow_activity_pos r lam hr)
  have hs : (p lam Y)^2 < 1 := by nlinarith only [hp, hp1, sq_nonneg (1-p lam Y)]
  unfold dhParentBase
  exact mul_pos (row_gamma_pos r lam hr) (by linarith only [hp1, hs])

theorem dh_parent_upper_positive (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hrho : 0 ≤ rho) : 0 < dhParentUpper r lam Y rho := by
  exact add_pos_of_pos_of_nonneg (dh_parent_base_positive r lam Y hr)
    (mul_nonneg (sub_pos.mpr (p_lt_one lam Y (inRow_activity_pos r lam hr))).le hrho)

theorem dh_parent_upper_bound (r : Row) (lam Y rho : ℝ) (hr : InRow r lam) :
    parentP r lam Y rho ≤ dhParentUpper r lam Y rho := by
  simpa only [dhParentUpper, dhParentBase, add_comm, mul_comm] using
    parentP_quadratic_upper r lam Y rho hr

theorem lowerVacancy_nonnegative (lam Y : ℝ) (hlam : 0 < lam) :
    0 ≤ lowerVacancy lam Y := by
  have hp1 := p_lt_one lam Y hlam
  unfold lowerVacancy
  positivity

-- A reduction of the unchanged target. The four corner premises still require
-- the original D/H rational certificates; they are not asserted here.
theorem dh_compactHeavy_of_scaled_corners (r : Row)
    (hcorners : ∀ lam Y u y : ℝ, InRow r lam → 0 < Y →
      (rowData r).xMin ≤ parentX lam Y → parentX lam Y ≤ 1 →
      0 ≤ u → u ≤ q lam → Admissible lam u y →
      ∀ rho : ℝ, (rho = lowerVacancy lam Y ∨ rho = 1) →
      ∀ z : ℝ, (z = parentLogLower r lam (parentX lam Y) ∨
        z = parentLogUpper r lam (parentX lam Y)) →
      0 < scaledPayment r lam Y rho u y (dhTangent r lam Y) (dhParentUpper r lam Y rho) z) :
    CompactHeavy r := by
  intro lam Y rho u y hdom hx0 hx1
  rcases hdom with ⟨hr, hY, hrho, hu0, hcap, hadm⟩
  have huq : u ≤ q lam := hcap.trans (min_le_left _ _)
  have hlog := original_parent_log_enclosure r lam Y hr hx0 hx1
  have hcorner := hcorners lam Y u y hr hY hx0 hx1 hu0 huq hadm
  apply payment_positive_of_scaled_corners r lam Y rho u y (dhTangent r lam Y)
    (dhParentBase r lam Y) (1-p lam Y) (lowerVacancy lam Y) 1
    (parentLogLower r lam (parentX lam Y)) (parentLogUpper r lam (parentX lam Y))
    hr hY hrho hx1 (dh_parent_upper_bound r lam Y rho hr)
  · exact (dh_parent_upper_positive r lam Y (lowerVacancy lam Y) hr
      (lowerVacancy_nonnegative lam Y (inRow_activity_pos r lam hr))).le
  · exact (dh_parent_upper_positive r lam Y 1 hr (by norm_num)).le
  · exact hrho.1
  · exact hrho.2
  · exact hlog.2.1
  · exact hlog.2.2
  · exact hcorner _ (Or.inl rfl) _ (Or.inl rfl)
  · exact hcorner _ (Or.inl rfl) _ (Or.inr rfl)
  · exact hcorner _ (Or.inr rfl) _ (Or.inl rfl)
  · exact hcorner _ (Or.inr rfl) _ (Or.inr rfl)

end F4Heavy.Analysis
