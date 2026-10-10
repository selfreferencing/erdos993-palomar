module

public import Erdos993Lean.Analytic.V22.Analysis.SkewBounds
public import Erdos993Lean.Analytic.V22.Analysis.GaussianExponents
public import Erdos993Lean.Analytic.V22.Analysis.BonusBounds

/-!
# Section 4: exact bounds in the variable nu

Source: repaired frozen note Lemma 4.9(b). In particular `N_a` is an
arbitrary real number satisfying `nu^2<N_a<=N`; it is not silently replaced
by `N`, and it need not be at least one. Both bonus comparisons come from
`BonusBounds`, and all square-root denominators are proved positive here.
Consumer: Lemma 4.10's linearized coefficients.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def monotoneDeltaA (r N Na : ℝ) : ℝ := activityNu r N ^ 2 * (1 - 1 / Na)
noncomputable def monotoneDeltaBar (r N Na : ℝ) : ℝ := activityNu r N ^ 2 / (1 - activityNu r N ^ 2 / Na)
noncomputable def monotoneEpsilonBound (r N : ℝ) : ℝ :=
  2 * activityNu r N / (N + 1) + activityNu r N ^ 3 / (3 * (N - activityNu r N ^ 2))
noncomputable def monotoneScaledEpsilonBound (r N : ℝ) : ℝ :=
  2 * activityNu r N + activityNu r N ^ 3 / (3 * (1 - activityNu r N ^ 2 / N))

theorem activityNu_nonneg {r N : ℝ} (hr0 : 0 ≤ r) : 0 ≤ activityNu r N :=
  mul_nonneg hr0 (Real.sqrt_nonneg N)

theorem activityNu_quotient {r N : ℝ} (hN : 0 < N) : activityNu r N ^ 2 / N = r ^ 2 := by
  rw [activityNu_sq hN.le]
  field_simp [hN.ne']

theorem activityNu_gap {r N : ℝ} (hN : 0 < N) :
    N - activityNu r N ^ 2 = N * (1 - r ^ 2) := by
  rw [activityNu_sq hN.le]
  ring

theorem monotone_sqrt_domains {r N Na : ℝ} (hN : 10 ≤ N)
    (ha : activityNu r N ^ 2 < Na) (haN : Na ≤ N) :
    0 < 1 + monotoneDeltaA r N Na ∧ 0 < 1 + monotoneDeltaBar r N Na ∧
      0 < V22.gamma r N := by
  obtain ⟨hNa, hr, hdNa, _⟩ := bonus_comparison_domains hN ha haN
  have hDelta := delta_nonneg (by linarith : 1 ≤ N) hr
  have hquot : activityNu r N ^ 2 / Na < 1 := (div_lt_one hNa).2 ha
  have hA : monotoneDeltaA r N Na = activityNu r N ^ 2 - activityNu r N ^ 2 / Na := by
    unfold monotoneDeltaA
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]
    linarith [sq_nonneg (activityNu r N)]
  · unfold monotoneDeltaBar
    have h := div_nonneg (sq_nonneg (activityNu r N)) hdNa.le
    linarith
  · unfold V22.gamma
    linarith

theorem monotone_sqrt_gamma_bounds {r N Na : ℝ} (hN : 10 ≤ N)
    (ha : activityNu r N ^ 2 < Na) (haN : Na ≤ N) :
    Real.sqrt (1 + monotoneDeltaA r N Na) ≤ Real.sqrt (V22.gamma r N) ∧
      Real.sqrt (V22.gamma r N) ≤ Real.sqrt (1 + monotoneDeltaBar r N Na) := by
  have hDelta := delta_two_comparisons hN ha haN
  constructor
  · apply Real.sqrt_le_sqrt
    dsimp [V22.gamma, monotoneDeltaA]
    linarith [hDelta.1]
  · apply Real.sqrt_le_sqrt
    dsimp [V22.gamma, monotoneDeltaBar]
    linarith [hDelta.2]

theorem monotone_aHat_scaled {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    V22.aHat r * Real.sqrt N ≤ activityNu r N ^ 3 / (3 * (N - activityNu r N ^ 2)) := by
  have hn : 0 < N := by linarith
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hs3 : Real.sqrt N ^ 3 = N * Real.sqrt N := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, Real.sq_sqrt hn.le]
  have h := mul_le_mul_of_nonneg_right (sharedAHat_bounds hr0 (by linarith : r < 1)).2
    (Real.sqrt_nonneg N)
  apply h.trans_eq
  rw [activityNu_gap hn]
  unfold activityNu
  rw [mul_pow, hs3]
  field_simp [hn.ne', hdr.ne'] <;> ring

theorem monotone_epsilonPrime_bound {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    V22.epsilonPrime r N ≤ monotoneEpsilonBound r N := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hr1 : r < 1 := by linarith
  have hy := shared_yTilde_nonneg hr0 hr1 hn
  have hs := shared_sN_le_half_sqrt hr0 hr1 hn
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hy)) hn1.le
  have heq : (4 * V22.yTilde r N * (Real.sqrt N / 2)) / (N + 1) =
      2 * activityNu r N / (N + 1) + V22.aHat r * Real.sqrt N := by
    unfold V22.yTilde activityNu
    field_simp [hn1.ne'] <;> ring
  change V22.epsilonPrime r N ≤ (4 * V22.yTilde r N * (Real.sqrt N / 2)) / (N + 1) at h
  rw [heq] at h
  have ha := monotone_aHat_scaled hr0 hrh hN
  unfold monotoneEpsilonBound
  linarith

theorem monotone_epsilon_bound_nonneg {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) : 0 ≤ monotoneEpsilonBound r N := by
  have hn : 0 < N := by linarith
  have hnu := activityNu_nonneg (N := N) hr0
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  unfold monotoneEpsilonBound
  rw [activityNu_gap hn]
  positivity

theorem monotone_epsilon_over_gamma {r N Na : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N)
    (ha : activityNu r N ^ 2 < Na) (haN : Na ≤ N) :
    V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ≤
      monotoneEpsilonBound r N / Real.sqrt (1 + monotoneDeltaA r N Na) := by
  obtain ⟨hA, _, hgamma⟩ := monotone_sqrt_domains hN ha haN
  have hs := (monotone_sqrt_gamma_bounds hN ha haN).1
  calc
    _ ≤ monotoneEpsilonBound r N / Real.sqrt (V22.gamma r N) :=
      div_le_div_of_nonneg_right (monotone_epsilonPrime_bound hr0 hrh hN) (Real.sqrt_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (monotone_epsilon_bound_nonneg hr0 hrh hN)
      (Real.sqrt_pos.2 hA) hs

/-- Lemma 4.9(b), the exact lower bound for `rho_U` at every admissible real `N_a`. -/
theorem monotone_rhoU_lower {r N Na : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N)
    (ha : activityNu r N ^ 2 < Na) (haN : Na ≤ N) :
    (1 - activityNu r N ^ 2 / N) * V22.rho N -
      (2 * activityNu r N / (N + 1) + activityNu r N ^ 3 / (3 * (N - activityNu r N ^ 2))) /
        Real.sqrt (1 + activityNu r N ^ 2 * (1 - 1 / Na)) ≤ V22.rhoU r N := by
  have hn : 0 < N := by linarith
  have h := monotone_epsilon_over_gamma hr0 hrh hN ha haN
  rw [activityNu_quotient hn]
  unfold V22.rhoU monotoneEpsilonBound monotoneDeltaA at *
  linarith

/-- Lemma 4.9(b), the source's stated (possibly loose) scaled rho error. -/
theorem monotone_rho_error_upper {r N Na : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N)
    (ha : activityNu r N ^ 2 < Na) (haN : Na ≤ N) :
    2 * (N + 1) * (V22.rho N - V22.rhoU r N) ≤
      2 * (N + 1) * activityNu r N ^ 2 / N +
        2 * (2 * activityNu r N + (N + 1) * activityNu r N ^ 3 /
          (3 * (N - activityNu r N ^ 2))) / Real.sqrt (1 + activityNu r N ^ 2 * (1 - 1 / Na)) := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hgap : N - activityNu r N ^ 2 ≠ 0 := by
    rw [activityNu_gap hn]
    exact (mul_pos hn (shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1))).ne'
  have hrho : V22.rho N ≤ 1 := by
    unfold V22.rho
    exact (div_le_one hn1).2 (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left (monotone_epsilon_over_gamma hr0 hrh hN ha haN)
    (by linarith : 0 ≤ 2 * (N + 1))
  have hbas : r ^ 2 * V22.rho N ≤ r ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hrho (sq_nonneg r)
  have hbasScaled := mul_le_mul_of_nonneg_left hbas (by linarith : 0 ≤ 2 * (N + 1))
  have hnum : 2 * (N + 1) * monotoneEpsilonBound r N =
      2 * (2 * activityNu r N + (N + 1) * activityNu r N ^ 3 / (3 * (N - activityNu r N ^ 2))) := by
    unfold monotoneEpsilonBound
    field_simp [hn1.ne', hgap] <;> ring
  simp only [← mul_div_assoc] at hscaled
  rw [hnum] at hscaled
  have hnuTerm : 2 * (N + 1) * activityNu r N ^ 2 / N = 2 * (N + 1) * r ^ 2 := by
    rw [activityNu_sq hn.le]
    field_simp [hn.ne'] <;> ring
  rw [hnuTerm]
  unfold V22.rhoU monotoneDeltaA at *
  convert (add_le_add hbasScaled hscaled) using 1 <;> ring

theorem monotone_scaled_epsilonPrime_bound {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    N * V22.epsilonPrime r N ≤ monotoneScaledEpsilonBound r N := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hnu := activityNu_nonneg (N := N) hr0
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have h := mul_le_mul_of_nonneg_left (monotone_epsilonPrime_bound hr0 hrh hN) hn.le
  apply h.trans
  unfold monotoneEpsilonBound monotoneScaledEpsilonBound
  rw [activityNu_gap hn, activityNu_quotient hn]
  have heq : N * (2 * activityNu r N / (N + 1) + activityNu r N ^ 3 / (3 * (N * (1 - r ^ 2)))) =
      2 * activityNu r N * (N / (N + 1)) + activityNu r N ^ 3 / (3 * (1 - r ^ 2)) := by
    field_simp [hn.ne', hn1.ne', hdr.ne'] <;> ring
  rw [heq]
  have hratio : N / (N + 1) ≤ 1 := (div_le_one hn1).2 (by linarith)
  have hfirst := mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnu)
  linarith

/-- Lemma 4.9(b), the complete upper-error bound with the `-c0Prime` term
dropped only by its proved nonnegativity. -/
theorem monotone_eU_upper {r N Na : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N)
    (ha : activityNu r N ^ 2 < Na) (haN : Na ≤ N) :
    N * V22.eU r N ≤ activityNu r N ^ 2 / 2 +
      (1 / 2 : ℝ) * (2 * activityNu r N + activityNu r N ^ 3 / (3 * (1 - activityNu r N ^ 2 / N))) *
        (Real.sqrt (1 + monotoneDeltaBar r N Na) + 1 / Real.sqrt (1 + monotoneDeltaA r N Na)) +
      (N + 1) * activityNu r N ^ 4 / (12 * N * (1 - activityNu r N ^ 2 / N) ^ 2) := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hr1 : r < 1 := by linarith
  obtain ⟨hA, hB, hgamma⟩ := monotone_sqrt_domains hN ha haN
  obtain ⟨hrootA, hrootB⟩ := monotone_sqrt_gamma_bounds hN ha haN
  have hsum : Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N) ≤
      Real.sqrt (1 + monotoneDeltaBar r N Na) + 1 / Real.sqrt (1 + monotoneDeltaA r N Na) :=
    add_le_add hrootB (one_div_le_one_div_of_le (Real.sqrt_pos.2 hA) hrootA)
  have hsumnonneg : 0 ≤ Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N) := by positivity
  have heps := shared_epsilonPrime_nonneg hr0 hr1 hn
  have hepsScaled := monotone_scaled_epsilonPrime_bound hr0 hrh hN
  have hprod := mul_le_mul hepsScaled hsum hsumnonneg
    ((mul_nonneg hn.le heps).trans hepsScaled)
  have hcr := mul_le_mul_of_nonneg_left (shared_cr_quartic_bound hr0 hrh)
    (mul_pos hn hn1).le
  have hcrEq : N * (N + 1) * (r ^ 4 / (12 * (1 - r ^ 2) ^ 2)) =
      (N + 1) * activityNu r N ^ 4 / (12 * N * (1 - activityNu r N ^ 2 / N) ^ 2) := by
    rw [activityNu_quotient hn]
    unfold activityNu
    have hs4 : Real.sqrt N ^ 4 = N ^ 2 := by
      calc
        Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 := by ring
        _ = N ^ 2 := by rw [Real.sq_sqrt hn.le]
    rw [mul_pow, hs4]
    field_simp [hn.ne', (shared_one_sub_sq_pos (by linarith : -1 < r) hr1).ne'] <;> ring
  rw [hcrEq] at hcr
  have hc0 : 0 ≤ V22.c0Prime r N := by
    unfold V22.c0Prime
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hn1.le
  have hdrop := mul_nonneg hn.le hc0
  have hrho : V22.rho N ≤ 1 := by
    unfold V22.rho
    exact (div_le_one hn1).2 (by linarith)
  have hfirst := mul_le_mul_of_nonneg_left hrho (sq_nonneg r)
  have hfirstScaled := mul_le_mul_of_nonneg_left hfirst hn.le
  have hnuSq := activityNu_sq (r := r) hn.le
  unfold V22.eU monotoneScaledEpsilonBound at *
  nlinarith

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.monotoneDeltaA
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotoneDeltaA
#check Erdos993Lean.Analytic.V22.Analysis.monotoneDeltaBar
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotoneDeltaBar
#check Erdos993Lean.Analytic.V22.Analysis.monotoneEpsilonBound
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotoneEpsilonBound
#check Erdos993Lean.Analytic.V22.Analysis.monotoneScaledEpsilonBound
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotoneScaledEpsilonBound
#check Erdos993Lean.Analytic.V22.Analysis.activityNu_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.activityNu_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.activityNu_quotient
#print axioms Erdos993Lean.Analytic.V22.Analysis.activityNu_quotient
#check Erdos993Lean.Analytic.V22.Analysis.activityNu_gap
#print axioms Erdos993Lean.Analytic.V22.Analysis.activityNu_gap
#check Erdos993Lean.Analytic.V22.Analysis.monotone_sqrt_domains
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_sqrt_domains
#check Erdos993Lean.Analytic.V22.Analysis.monotone_sqrt_gamma_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_sqrt_gamma_bounds
#check Erdos993Lean.Analytic.V22.Analysis.monotone_aHat_scaled
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_aHat_scaled
#check Erdos993Lean.Analytic.V22.Analysis.monotone_epsilonPrime_bound
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_epsilonPrime_bound
#check Erdos993Lean.Analytic.V22.Analysis.monotone_epsilon_bound_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_epsilon_bound_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.monotone_epsilon_over_gamma
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_epsilon_over_gamma
#check Erdos993Lean.Analytic.V22.Analysis.monotone_rhoU_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_rhoU_lower
#check Erdos993Lean.Analytic.V22.Analysis.monotone_rho_error_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_rho_error_upper
#check Erdos993Lean.Analytic.V22.Analysis.monotone_scaled_epsilonPrime_bound
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_scaled_epsilonPrime_bound
#check Erdos993Lean.Analytic.V22.Analysis.monotone_eU_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_eU_upper
