module

public import Erdos993Lean.Analytic.V22.Functions
public import Mathlib.Tactic

/-!
# Exact bonus comparisons

Source: repaired note Lemma 4.9(b), including both comparisons and its
`nu^2 < N_a <= N` domain, and Lemma 4.10(e). These lemmas retain the actual
activity displacement and trial count. They certify scalar steps in the
analytic fiber route and create no process or forest data.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real

noncomputable def activityNu (r N : ℝ) : ℝ := r * Real.sqrt N

theorem activityNu_sq {r N : ℝ} (hN : 0 ≤ N) :
    activityNu r N ^ 2 = r ^ 2 * N := by
  unfold activityNu
  rw [mul_pow, Real.sq_sqrt hN]

theorem delta_nonneg {r N : ℝ} (hN : 1 ≤ N) (hr : r ^ 2 < 1) :
    0 ≤ V22.Delta r N := by
  have hN0 : 0 < N := by linarith
  have hn : 0 ≤ N ^ 2 - N + 1 := by nlinarith [sq_nonneg (N - 1)]
  unfold V22.Delta
  exact div_nonneg (mul_nonneg (sq_nonneg r) hn)
    (mul_nonneg (by linarith) hN0.le)

/-- The stronger lower estimate appearing in the proof of Lemma 4.9(b). -/
theorem delta_lower_sharp {r N : ℝ} (hN : 1 ≤ N) (hr : r ^ 2 < 1) :
    r ^ 2 * (N - 1) / (1 - r ^ 2) ≤ V22.Delta r N := by
  have hN0 : 0 < N := by linarith
  have hd : 0 < 1 - r ^ 2 := by linarith
  unfold V22.Delta
  apply (div_le_div_iff₀ hd (mul_pos hd hN0)).2
  nlinarith [sq_nonneg r]

theorem delta_upper_sharp {r N : ℝ} (hN : 1 ≤ N) (hr : r ^ 2 < 1) :
    V22.Delta r N ≤ r ^ 2 * N / (1 - r ^ 2) := by
  have hN0 : 0 < N := by linarith
  have hd : 0 < 1 - r ^ 2 := by linarith
  unfold V22.Delta
  apply (div_le_div_iff₀ (mul_pos hd hN0) hd).2
  nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hN)]

/-- The actual `nu` domain implies all denominators are positive. -/
theorem bonus_comparison_domains {r N Na : ℝ} (hN : 10 ≤ N)
    (ha : activityNu r N ^ 2 < Na) (haN : Na ≤ N) :
    0 < Na ∧ r ^ 2 < 1 ∧ 0 < 1 - activityNu r N ^ 2 / Na ∧
      0 < 1 - activityNu r N ^ 2 / N := by
  have hN0 : 0 < N := by linarith
  have hNa : 0 < Na := lt_of_le_of_lt (sq_nonneg _) ha
  have hsq := activityNu_sq (r := r) hN0.le
  have hr : r ^ 2 < 1 := by nlinarith
  refine ⟨hNa, hr, ?_, ?_⟩
  · exact sub_pos.mpr ((div_lt_one hNa).2 ha)
  · exact sub_pos.mpr ((div_lt_one hN0).2 (ha.trans_le haN))

/-- Repaired Lemma 4.9(b): both lower and upper comparisons, for every
admissible real `N_a`. There is no extra asserted comparison premise. -/
theorem delta_two_comparisons {r N Na : ℝ} (hN : 10 ≤ N)
    (ha : activityNu r N ^ 2 < Na) (haN : Na ≤ N) :
    activityNu r N ^ 2 * (1 - 1 / Na) ≤ V22.Delta r N ∧
      V22.Delta r N ≤ activityNu r N ^ 2 / (1 - activityNu r N ^ 2 / Na) := by
  obtain ⟨hNa, hr, hdNa, hdN⟩ := bonus_comparison_domains hN ha haN
  have hN0 : 0 < N := by linarith
  have hn1 : 1 ≤ N := by linarith
  have hd : 0 < 1 - r ^ 2 := by linarith
  have hsq := activityNu_sq (r := r) hN0.le
  have hbasic : activityNu r N ^ 2 * (1 - 1 / N) ≤ V22.Delta r N := by
    calc
      activityNu r N ^ 2 * (1 - 1 / N) = r ^ 2 * (N - 1) := by
        rw [hsq]
        field_simp [hN0.ne']
      _ ≤ r ^ 2 * (N - 1) / (1 - r ^ 2) := by
        apply (le_div_iff₀ hd).2
        nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hn1),
          mul_nonneg (sq_nonneg r) (sq_nonneg r)]
      _ ≤ V22.Delta r N := delta_lower_sharp hn1 hr
  constructor
  · apply le_trans _ hbasic
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hinv : 1 / N ≤ 1 / Na := one_div_le_one_div_of_le hNa haN
    linarith
  · calc
      V22.Delta r N ≤ r ^ 2 * N / (1 - r ^ 2) := delta_upper_sharp hn1 hr
      _ = activityNu r N ^ 2 / (1 - activityNu r N ^ 2 / N) := by
        rw [hsq]
        congr 1
        field_simp [hN0.ne']
      _ ≤ activityNu r N ^ 2 / (1 - activityNu r N ^ 2 / Na) := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) hdNa
        have hquot : activityNu r N ^ 2 / N ≤ activityNu r N ^ 2 / Na :=
          div_le_div_of_nonneg_left (sq_nonneg _) hNa haN
        linarith

/-- Lemma 4.10(e), first estimate. -/
theorem scaled_delta_lower {r N : ℝ} (hN : 10 ≤ N) (hr : r ^ 2 < 1) :
    (N - 1) * activityNu r N ^ 2 ≤ N * V22.Delta r N := by
  have hN0 : 0 < N := by linarith
  have hn1 : 1 ≤ N := by linarith
  have h := delta_lower_sharp hn1 hr
  have hd : 0 < 1 - r ^ 2 := by linarith
  rw [activityNu_sq hN0.le]
  have hl : r ^ 2 * (N - 1) ≤ r ^ 2 * (N - 1) / (1 - r ^ 2) := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hn1),
      mul_nonneg (sq_nonneg r) (sq_nonneg r)]
  nlinarith [mul_le_mul_of_nonneg_left (hl.trans h) hN0.le]

/-- Lemma 4.10(e), retaining the improved denominator when `r>=r_a>=0`. -/
theorem scaled_delta_lower_activity {r ra N : ℝ} (hN : 10 ≤ N)
    (ha : 0 ≤ ra) (har : ra ≤ r) (hr : r ^ 2 < 1) :
    (N - 1) * activityNu r N ^ 2 / (1 - ra ^ 2) ≤ N * V22.Delta r N := by
  have hN0 : 0 < N := by linarith
  have hn1 : 1 ≤ N := by linarith
  have hr0 : 0 ≤ r := ha.trans har
  have hs : ra ^ 2 ≤ r ^ 2 := (sq_le_sq₀ ha hr0).2 har
  have hd : 0 < 1 - r ^ 2 := by linarith
  have hda : 0 < 1 - ra ^ 2 := by linarith
  have hn : 0 ≤ r ^ 2 * (N - 1) := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hn1)
  have hcomp : r ^ 2 * (N - 1) / (1 - ra ^ 2) ≤ r ^ 2 * (N - 1) / (1 - r ^ 2) :=
    div_le_div_of_nonneg_left hn hd (by linarith)
  have h := mul_le_mul_of_nonneg_left (hcomp.trans (delta_lower_sharp hn1 hr)) hN0.le
  rw [activityNu_sq hN0.le]
  convert h using 1 <;> ring

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.activityNu
#print axioms Erdos993Lean.Analytic.V22.Analysis.activityNu
#check Erdos993Lean.Analytic.V22.Analysis.activityNu_sq
#print axioms Erdos993Lean.Analytic.V22.Analysis.activityNu_sq
#check Erdos993Lean.Analytic.V22.Analysis.delta_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.delta_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.delta_lower_sharp
#print axioms Erdos993Lean.Analytic.V22.Analysis.delta_lower_sharp
#check Erdos993Lean.Analytic.V22.Analysis.delta_upper_sharp
#print axioms Erdos993Lean.Analytic.V22.Analysis.delta_upper_sharp
#check Erdos993Lean.Analytic.V22.Analysis.bonus_comparison_domains
#print axioms Erdos993Lean.Analytic.V22.Analysis.bonus_comparison_domains
#check Erdos993Lean.Analytic.V22.Analysis.delta_two_comparisons
#print axioms Erdos993Lean.Analytic.V22.Analysis.delta_two_comparisons
#check Erdos993Lean.Analytic.V22.Analysis.scaled_delta_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.scaled_delta_lower
#check Erdos993Lean.Analytic.V22.Analysis.scaled_delta_lower_activity
#print axioms Erdos993Lean.Analytic.V22.Analysis.scaled_delta_lower_activity
