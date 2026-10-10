module

public import Mathlib

/-!
The lower side of current Lemma 5.15.
The finite partial sum is literal; the derivative uses Mathlib's generic
half-log gap identity, not a fixed numerical log comparison.

-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic

open Set Finset

/-- The printed finite lower sum, also defined at n=0. -/
noncomputable def logLower (n : ℕ) (z : ℝ) : ℝ :=
  2 * ∑ j ∈ range n, z ^ (2*j+1) / (2*j+1)

/-- The exact positive derivative of the lower gap. -/
theorem logLower_gap_hasDerivAt (n : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    HasDerivAt (fun x => Real.log ((1+x)/(1-x)) - logLower n x)
      (2*z^(2*n)/(1-z^2)) z := by
  have h := (Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
    n (by linarith : -1 < z) hz1).const_mul 2
  have he : 2*((z^2)^n/(1-z^2)) = 2*z^(2*n)/(1-z^2) := by
    rw [← pow_mul]
    ring
  apply (h.congr_deriv he).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun x => by dsimp [logLower]; ring)

/-- A generic comparison on a closed interval; strictness is needed only inside it. -/
theorem gap_pos_of_hasDerivAt_pos {f f' : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hzero : f 0 = 0)
    (hd : ∀ x ∈ Icc 0 z, HasDerivAt f (f' x) x)
    (hp : ∀ x ∈ Ioo 0 z, 0 < f' x) : 0 < f z := by
  have hm : StrictMonoOn f (Icc 0 z) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 z)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact hp x (by simpa only [interior_Icc] using hx)
  have h := hm (show (0 : ℝ) ∈ Icc 0 z from ⟨le_rfl, hz.le⟩)
    (show z ∈ Icc 0 z from ⟨hz.le, le_rfl⟩) hz
  simpa only [hzero] using h

/-- Strictness holds even for the empty partial sum n=0. -/
theorem logLower_lt (n : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    logLower n z < Real.log ((1+z)/(1-z)) := by
  have h := gap_pos_of_hasDerivAt_pos
    (f := fun x => Real.log ((1+x)/(1-x)) - logLower n x)
    (f' := fun x => 2*x^(2*n)/(1-x^2)) hz
    (by simp [logLower])
    (fun x hx => logLower_gap_hasDerivAt n hx.1 (hx.2.trans_lt hz1))
    (by
      intro x hx
      have hx1 : x < 1 := hx.2.trans hz1
      have hden : 0 < 1-x^2 := by
        have hm : 0 < (1-x)*(1+x) :=
          mul_pos (sub_pos.mpr hx1) (by linarith [hx.1])
        nlinarith
      exact div_pos (mul_pos (by norm_num) (pow_pos hx.1 _)) hden)
  exact sub_pos.mp h

/-- The lower half of printed Lemma 5.15, with its exact closed zero endpoint. -/
theorem logLower_le (n : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    logLower n z ≤ Real.log ((1+z)/(1-z)) := by
  rcases eq_or_lt_of_le hz with hzero | hpos
  · subst z
    simp [logLower]
  · exact (logLower_lt n hpos hz1).le

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.logLower
#print axioms Erdos993Lean.BCFG.Analytic.logLower
#check Erdos993Lean.BCFG.Analytic.logLower_gap_hasDerivAt
#print axioms Erdos993Lean.BCFG.Analytic.logLower_gap_hasDerivAt
#check Erdos993Lean.BCFG.Analytic.gap_pos_of_hasDerivAt_pos
#print axioms Erdos993Lean.BCFG.Analytic.gap_pos_of_hasDerivAt_pos
#check Erdos993Lean.BCFG.Analytic.logLower_lt
#print axioms Erdos993Lean.BCFG.Analytic.logLower_lt
#check Erdos993Lean.BCFG.Analytic.logLower_le
#print axioms Erdos993Lean.BCFG.Analytic.logLower_le
#check Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
#print axioms Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
#check strictMonoOn_of_hasDerivWithinAt_pos
#print axioms strictMonoOn_of_hasDerivWithinAt_pos
