module

public import Mathlib

/-!
The actual Real logarithm enclosures in current
T1, Section 3.4. No finite data file is evaluated here. The positive artanh
remainder has its printed factor 1/7; a coarser geometric remainder is not
substituted.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

open Real Set Finset

/-- Generic closed-interval derivative comparison, including x=0. -/
theorem zero_le_value_of_nonneg_deriv {f f' : ℝ → ℝ} {x : ℝ}
    (hx : 0 ≤ x) (hzero : 0 ≤ f 0)
    (hd : ∀ t ∈ Icc 0 x, HasDerivAt f (f' t) t)
    (hn : ∀ t ∈ Icc 0 x, 0 ≤ f' t) : 0 ≤ f x := by
  have hm : MonotoneOn f (Icc 0 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact hn t (interior_subset ht)
  exact hzero.trans (hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx)

noncomputable def seriesS (w : ℝ) : ℝ := 2 * (w + w ^ 3 / 3 + w ^ 5 / 5)
noncomputable def seriesT (w : ℝ) : ℝ := seriesS w + 2 * w ^ 7 / (7 * (1 - w ^ 2))
noncomputable def logRatio (w : ℝ) : ℝ := log (1 + w) - log (1 - w)

theorem logRatio_eq {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    logRatio w = log ((1 + w) / (1 - w)) := by
  exact (Real.log_div (by positivity) (by linarith)).symm

theorem hasDerivAt_seriesS (w : ℝ) :
    HasDerivAt seriesS (2 * (1 + w ^ 2 + w ^ 4)) w := by
  convert ((((hasDerivAt_id w).add ((hasDerivAt_pow 3 w).div_const 3)).add
    ((hasDerivAt_pow 5 w).div_const 5)).const_mul 2) using 1 <;>
    (try funext t) <;> dsimp [seriesS] <;>
    ring

theorem hasDerivAt_logRatio {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    HasDerivAt logRatio (2 / (1 - w ^ 2)) w := by
  have hp : 1 + w ≠ 0 := by positivity
  have hm : 1 - w ≠ 0 := by linarith
  have hs : 1 - w ^ 2 ≠ 0 := by nlinarith
  convert (((hasDerivAt_id w).const_add 1).log hp).sub
    (((hasDerivAt_id w).const_sub 1).log hm) using 1
  all_goals
    (try funext t) <;> dsimp [logRatio] <;>
      field_simp [hp, hm, hs] <;> ring

/-- The derivative of the exact printed upper remainder. -/
theorem hasDerivAt_upper_gap {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    HasDerivAt (fun t => seriesT t - logRatio t)
      (4 * w ^ 8 / (7 * (1 - w ^ 2) ^ 2)) w := by
  have hs : 1 - w ^ 2 ≠ 0 := by nlinarith
  have hd : 7 * (1 - w ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hs
  have hden := ((hasDerivAt_pow 2 w).const_sub 1).const_mul 7
  have hrem := ((hasDerivAt_pow 7 w).const_mul 2).div hden hd
  convert ((hasDerivAt_seriesS w).add hrem).sub (hasDerivAt_logRatio hw0 hw1) using 1
  all_goals
    (try funext t) <;> dsimp [seriesT] <;>
      field_simp [hs] <;> ring

theorem seriesS_le_logRatio {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    seriesS w ≤ logRatio w := by
  have h := Real.sum_range_le_log_div hw0 hw1 3
  rw [← logRatio_eq hw0 hw1] at h
  norm_num [Finset.sum_range_succ] at h
  dsimp [seriesS]
  linarith

theorem logRatio_le_seriesT {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    logRatio w ≤ seriesT w := by
  have h := zero_le_value_of_nonneg_deriv (f := fun t => seriesT t - logRatio t)
    (f' := fun t => 4 * t ^ 8 / (7 * (1 - t ^ 2) ^ 2)) hw0
    (by norm_num [seriesT, seriesS, logRatio])
    (fun t ht => hasDerivAt_upper_gap ht.1 (lt_of_le_of_lt ht.2 hw1))
    (fun t ht => by positivity)
  linarith

theorem artanh_brackets {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    seriesS w ≤ log ((1 + w) / (1 - w)) ∧
      log ((1 + w) / (1 - w)) ≤ seriesT w := by
  rw [← logRatio_eq hw0 hw1]
  exact ⟨seriesS_le_logRatio hw0 hw1, logRatio_le_seriesT hw0 hw1⟩

theorem log_five_fourths_brackets :
    (2231434 / 10000000 : ℝ) ≤ log (5 / 4) ∧ log (5 / 4) ≤ 2231436 / 10000000 := by
  have h := artanh_brackets (w := 1/9) (by norm_num) (by norm_num)
  norm_num [seriesS, seriesT] at h
  constructor <;> linarith [h.1, h.2]

theorem log_three_halves_brackets :
    (4054650 / 10000000 : ℝ) ≤ log (3 / 2) ∧ log (3 / 2) ≤ 4054652 / 10000000 := by
  have h1 := artanh_brackets (w := 1/9) (by norm_num) (by norm_num)
  have h2 := artanh_brackets (w := 1/11) (by norm_num) (by norm_num)
  have he : log (3/2 : ℝ) = log (5/4 : ℝ) + log (6/5 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (5/4 : ℝ) ≠ 0) (by norm_num : (6/5 : ℝ) ≠ 0)]
    norm_num
  norm_num [seriesS, seriesT] at h1 h2
  rw [he]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem log_two_brackets :
    (6931467 / 10000000 : ℝ) ≤ log 2 ∧ log 2 ≤ 6931472 / 10000000 := by
  have h1 := artanh_brackets (w := 1/9) (by norm_num) (by norm_num)
  have h2 := artanh_brackets (w := 1/11) (by norm_num) (by norm_num)
  have h3 := artanh_brackets (w := 1/7) (by norm_num) (by norm_num)
  have he : log (2 : ℝ) = log (5/4 : ℝ) + log (6/5 : ℝ) + log (4/3 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (5/4 : ℝ) ≠ 0) (by norm_num : (6/5 : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : (5/4 : ℝ)*(6/5) ≠ 0) (by norm_num : (4/3 : ℝ) ≠ 0)]
    norm_num
  norm_num [seriesS, seriesT] at h1 h2 h3
  rw [he]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- Actual dyadic/anchor factorization with explicit bracket hypotheses.
The finite worksheet's branch arithmetic is a separate later consumer. -/
theorem log_factor_brackets {z c v lo2 hi2 loc hic : ℝ} (k : ℕ)
    (hc : 0 < c) (hv : 1 ≤ v) (hv4 : v < 4/3)
    (hz : z = (2 : ℝ)^k * c * v)
    (h2 : lo2 ≤ log 2 ∧ log 2 ≤ hi2)
    (hanchor : loc ≤ log c ∧ log c ≤ hic) :
    (k : ℝ)*lo2 + loc + seriesS ((v-1)/(v+1)) ≤ log z ∧
      log z ≤ (k : ℝ)*hi2 + hic + seriesT ((v-1)/(v+1)) := by
  have hv0 : 0 < v := by linarith
  have hvp : 0 < v+1 := by linarith
  have hw0 : 0 ≤ (v-1)/(v+1) := div_nonneg (by linarith) hvp.le
  have hw1 : (v-1)/(v+1) < 1 := (div_lt_one hvp).2 (by linarith)
  have hid : (1+(v-1)/(v+1))/(1-(v-1)/(v+1)) = v := by
    have hden : 1-(v-1)/(v+1) ≠ 0 := by linarith
    field_simp [hvp.ne', hden] <;> ring
  have hw := artanh_brackets hw0 hw1
  rw [hid] at hw
  have hl : log z = (k : ℝ)*log 2 + log c + log v := by
    rw [hz, Real.log_mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc.ne') hv0.ne',
      Real.log_mul (pow_ne_zero _ (by norm_num)) hc.ne', Real.log_pow]
  have hk : (0 : ℝ) ≤ k := by positivity
  have hkl := mul_le_mul_of_nonneg_left h2.1 hk
  have hku := mul_le_mul_of_nonneg_left h2.2 hk
  rw [hl]
  constructor <;> linarith [hanchor.1, hanchor.2, hw.1, hw.2]

end Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.zero_le_value_of_nonneg_deriv
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.zero_le_value_of_nonneg_deriv
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.logRatio_eq
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.logRatio_eq
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_seriesS
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_seriesS
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_logRatio
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_logRatio
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_upper_gap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_upper_gap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.seriesS_le_logRatio
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.seriesS_le_logRatio
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.logRatio_le_seriesT
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.logRatio_le_seriesT
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.artanh_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.artanh_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_five_fourths_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_five_fourths_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_three_halves_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_three_halves_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_two_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_two_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_factor_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_factor_brackets
