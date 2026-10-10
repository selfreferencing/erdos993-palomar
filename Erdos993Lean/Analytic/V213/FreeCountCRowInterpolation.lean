module

public import Erdos993Lean.Analytic.V213.FreeCountEllBandsFinite
public import Erdos993Lean.Analytic.V213.FreeCountChildlessFinite
public import Erdos993Lean.Analytic.V213.FreeCountCAEllCurvature
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates

/-! This supplies the formerly explicit C-row ell
interpolation premise from actual point bounds, the proved parent curvature,
and all six checked activity bands. The four local row-coordinate guards are
read from cRowOK; no omitted or inferred interval guard is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

open Real Set Certificates
open Erdos993Lean.ExactComparisons.F3All

theorem cap_gamma_upper_gt (c : Cap) : (2/5 : ℝ) < gamma c.value c.upper := by
  have hu : (263/200 : ℝ) ≤ c.upper := by cases c <;> norm_num [Cap.upper]
  have hl : log (463/200 : ℝ) ≤ logActivity c.upper := by
    unfold logActivity
    apply Real.log_le_log (by norm_num)
    linarith
  have hb := log_463_200_gt.trans_le hl
  have hD : (6/5 : ℝ) ≤ c.value := by cases c <;> norm_num [Cap.value]
  have hm := mul_le_mul_of_nonneg_right hD (show 0 ≤ logActivity c.upper by linarith)
  unfold gamma
  nlinarith only [hb,hm]

theorem cap_upper_curvature_parameters (c : Cap) :
    (5/4 : ℝ) < c.upper ∧ q c.upper ≤ 7/10 := by
  have hu : (5/4 : ℝ) < c.upper := by cases c <;> norm_num [Cap.upper]
  have hl : (1/3 : ℝ) ≤ c.upper := by linarith
  have hh : c.upper ≤ (7/3 : ℝ) := by cases c <;> norm_num [Cap.upper]
  exact ⟨hu,(q_closed_domain hl hh).2⟩

theorem faceEll_lower_on_cap {c : Cap} {r : CRow} {lam y : ℝ}
    (hr : CRowFacts r) (hc : c.Contains lam)
    (hd : (r.D : ℝ) = c.value) (hu : (r.left.b.lam : ℝ) = c.upper)
    (hy : y ∈ Icc (r.left.e.y : ℝ) (r.right.e.y : ℝ)) :
    faceEllR r ≤ ell c.value lam y := by
  rcases cRowOK_domain_real hr.checked with ⟨hlams,hc0,hcd,hd5⟩
  have hDR : (0 : ℝ) < r.D := by rw [hd]; exact c.value_pos
  have hDQ : (0 : Rat) < r.D := by exact_mod_cast hDR
  have hleft := hr.left.ell_lower r.D hDQ
  have hright := hr.right.ell_lower r.D hDQ
  rw [hd,hu] at hleft
  rw [hd,←hlams,hu] at hright
  have hpoint := sub_le_sub_right (min_le_min hleft hright)
    ((9/16 : ℝ)*((r.right.e.y : ℝ)-(r.left.e.y : ℝ))^2)
  have hpars := cap_upper_curvature_parameters c
  have hcurve := ell_parent_cell_lower c.value_pos hpars.1 (cap_gamma_upper_gt c)
    hpars.2 exp_five_fourths_lt_four hc0 hcd hd5 hy
  have hactivity := ell_upper_le_on_cap hc (hc0.trans hy.1)
  exact hpoint.trans (hcurve.trans hactivity)

end Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_gamma_upper_gt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_gamma_upper_gt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_upper_curvature_parameters
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_upper_curvature_parameters
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.faceEll_lower_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.faceEll_lower_on_cap
