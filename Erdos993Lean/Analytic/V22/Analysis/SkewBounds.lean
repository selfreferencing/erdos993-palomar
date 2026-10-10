module

public import Erdos993Lean.Analytic.V22.Analysis.GaussianCalculus

/-!
# Section 4: the exact quartic skew bound

Source: the proof of frozen note Lemma 4.9(b). The derivative of `c_r`
is bounded using the actual `artanh-r`, and the quartic bound is obtained
on the original activity domain. Consumer: `MonotoneBounds`' upper error
estimate. No additional analytic premise is imposed on the final bound.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem hasDerivAt_sharedCr {x : ℝ} (hxL : -1 < x) (hxR : x < 1) :
    HasDerivAt Erdos993Lean.Analytic.V22.cr
      (Erdos993Lean.Analytic.V22.aHat x / (1 - x ^ 2)) x := by
  have hs := (shared_one_sub_sq_pos hxL hxR).ne'
  convert (((hasDerivAt_sharedArtanh hxL hxR).pow 2).add
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).log hs)).div_const 2 using 1
  · funext y
    dsimp [Erdos993Lean.Analytic.V22.cr] <;> ring
  · dsimp [Erdos993Lean.Analytic.V22.aHat]
    field_simp [hs] <;> ring

theorem shared_cr_quartic_bound_general {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Erdos993Lean.Analytic.V22.cr r ≤ r ^ 4 / (12 * (1 - r ^ 2) ^ 2) := by
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  let f : ℝ → ℝ := fun x => x ^ 4 / (12 * (1 - r ^ 2) ^ 2) - Erdos993Lean.Analytic.V22.cr x
  have hd : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt f
      (x ^ 3 / (3 * (1 - r ^ 2) ^ 2) - Erdos993Lean.Analytic.V22.aHat x / (1 - x ^ 2)) x := by
    intro x hx
    convert ((hasDerivAt_pow 4 x).div_const (12 * (1 - r ^ 2) ^ 2)).sub
      (hasDerivAt_sharedCr (by linarith [hx.1]) (by linarith [hx.2])) using 1
    all_goals field_simp [hdr.ne'] <;> ring
  have hc : ContinuousOn f (Icc (0 : ℝ) r) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc (0 : ℝ) r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) r := interior_subset hx
        have hx1 : x < 1 := by linarith [hx'.2]
        have hdx := shared_one_sub_sq_pos (by linarith [hx'.1] : -1 < x) hx1
        have hAHat := (sharedAHat_bounds hx'.1 hx1).2
        have hfirst := div_le_div_of_nonneg_right hAHat hdx.le
        have heq : (x ^ 3 / (3 * (1 - x ^ 2))) / (1 - x ^ 2) =
            x ^ 3 / (3 * (1 - x ^ 2) ^ 2) := by
          field_simp [hdx.ne'] <;> ring
        rw [heq] at hfirst
        have hden : 3 * (1 - r ^ 2) ^ 2 ≤ 3 * (1 - x ^ 2) ^ 2 := by
          have hsmall : 1 - r ^ 2 ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
          nlinarith
        have hsecond : x ^ 3 / (3 * (1 - x ^ 2) ^ 2) ≤ x ^ 3 / (3 * (1 - r ^ 2) ^ 2) :=
          div_le_div_of_nonneg_left (pow_nonneg hx'.1 3) (by positivity) hden
        exact sub_nonneg.mpr (hfirst.trans hsecond))
  have h := hm ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  have hf0 : f 0 = 0 := by
    norm_num [f, Erdos993Lean.Analytic.V22.cr, sharedArtanh_zero]
  rw [hf0] at h
  dsimp only [f] at h
  linarith

/-- The source activity interval is included without any extra assumption. -/
theorem shared_cr_quartic_bound {r : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    Erdos993Lean.Analytic.V22.cr r ≤ r ^ 4 / (12 * (1 - r ^ 2) ^ 2) :=
  shared_cr_quartic_bound_general hr0 (by linarith)

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedCr
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedCr
#check Erdos993Lean.Analytic.V22.Analysis.shared_cr_quartic_bound_general
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_cr_quartic_bound_general
#check Erdos993Lean.Analytic.V22.Analysis.shared_cr_quartic_bound
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_cr_quartic_bound
