module

public import Erdos993Lean.Analytic.V213.FreeCountRationalTransfer

/-!
This connects the existing, unchanged F3All rational
logarithm worksheet to the actual Real logarithm on its checked use-domain.
All three dyadic cases and all three anchor cases are explicit. No data list
is accepted here, and no continuous face/cell conclusion is asserted.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

open Real Erdos993Lean.ExactComparisons

theorem logReduced_bounds {z : Rat} (hz : 1 ≤ z) (hz8 : z < 8) :
    1 ≤ F3All.logReduced z ∧ F3All.logReduced z < 2 := by
  by_cases h2 : z < 2
  · simpa [F3All.logReduced, F3All.logIndex, h2] using And.intro hz h2
  · by_cases h4 : z < 4
    · simp only [F3All.logReduced, F3All.logIndex, if_neg h2, if_pos h4]
      norm_num only [pow_one]
      constructor
      · apply (le_div_iff₀ (by norm_num : (0 : Rat) < 2)).2
        linarith
      · apply (div_lt_iff₀ (by norm_num : (0 : Rat) < 2)).2
        linarith
    · simp only [F3All.logReduced, F3All.logIndex, if_neg h2, if_neg h4]
      norm_num only [show (2 : Rat)^2 = 4 by norm_num]
      constructor
      · apply (le_div_iff₀ (by norm_num : (0 : Rat) < 4)).2
        linarith
      · apply (div_lt_iff₀ (by norm_num : (0 : Rat) < 4)).2
        linarith

theorem log_anchor_chart {z : Rat} (hz : 1 ≤ z) (hz8 : z < 8) :
    0 < F3All.logAnchor z ∧
    F3All.logAnchor z ≤ F3All.logReduced z ∧
    F3All.logReduced z < (4/3) * F3All.logAnchor z ∧
    (F3All.logAnchor z = 1 ∨ F3All.logAnchor z = 5/4 ∨
      F3All.logAnchor z = 3/2) := by
  have hr := logReduced_bounds hz hz8
  by_cases h1 : F3All.logReduced z < 5/4
  · simp only [F3All.logAnchor, if_pos h1]
    refine ⟨by norm_num, hr.1, ?_, Or.inl True.intro⟩
    linarith
  · by_cases h2 : F3All.logReduced z < 3/2
    · simp only [F3All.logAnchor, if_neg h1, if_pos h2]
      refine ⟨by norm_num, le_of_not_gt h1, ?_, Or.inr (Or.inl True.intro)⟩
      linarith
    · simp only [F3All.logAnchor, if_neg h1, if_neg h2]
      refine ⟨by norm_num, le_of_not_gt h2, ?_, Or.inr (Or.inr True.intro)⟩
      linarith [hr.2]

theorem log_anchor_brackets {z : Rat} (hz : 1 ≤ z) (hz8 : z < 8) :
    (F3All.anchorLower (F3All.logAnchor z) : ℝ) ≤ log (F3All.logAnchor z : ℝ) ∧
    log (F3All.logAnchor z : ℝ) ≤ (F3All.anchorUpper (F3All.logAnchor z) : ℝ) := by
  rcases (log_anchor_chart hz hz8).2.2.2 with h | h | h
  · rw [h]
    norm_num [F3All.anchorLower, F3All.anchorUpper]
  · rw [h]
    convert log_five_fourths_brackets using 1 <;>
      norm_num [F3All.anchorLower, F3All.anchorUpper]
  · rw [h]
    convert log_three_halves_brackets using 1 <;>
      norm_num [F3All.anchorLower, F3All.anchorUpper]

/-- Includes the strict w<1/7 bound actually printed in the reduction. -/
theorem log_chart_bounds {z : Rat} (hz : 1 ≤ z) (hz8 : z < 8) :
    1 ≤ F3All.logReduced z / F3All.logAnchor z ∧
    F3All.logReduced z / F3All.logAnchor z < 4/3 ∧
    0 ≤ F3All.logW z ∧ F3All.logW z < 1/7 := by
  have hc := log_anchor_chart hz hz8
  have hv : 1 ≤ F3All.logReduced z / F3All.logAnchor z :=
    (le_div_iff₀ hc.1).2 (by simpa using hc.2.1)
  have hv4 : F3All.logReduced z / F3All.logAnchor z < 4/3 :=
    (div_lt_iff₀ hc.1).2 hc.2.2.1
  refine ⟨hv, hv4, ?_, ?_⟩
  · dsimp [F3All.logW]
    exact div_nonneg (by linarith) (by linarith)
  · dsimp [F3All.logW]
    apply (div_lt_iff₀ (by linarith :
      0 < F3All.logReduced z / F3All.logAnchor z + 1)).2
    linarith

theorem log_chart_factorization {z : Rat} (hz : 1 ≤ z) (hz8 : z < 8) :
    z = (2 : Rat) ^ F3All.logIndex z * F3All.logAnchor z *
      (F3All.logReduced z / F3All.logAnchor z) := by
  have hc := (log_anchor_chart hz hz8).1.ne'
  have hp : (2 : Rat) ^ F3All.logIndex z ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold F3All.logReduced
  field_simp [hc, hp] <;> ring

theorem logW_cast (z : Rat) :
    (F3All.logW z : ℝ) =
      (((F3All.logReduced z : ℝ) / (F3All.logAnchor z : ℝ) - 1) /
       ((F3All.logReduced z : ℝ) / (F3All.logAnchor z : ℝ) + 1)) := by
  simp [F3All.logW]

/-- The literal executable rational oracle bounds the actual Real logarithm. -/
theorem log_envelopes {z : Rat} (hz : 1 ≤ z) (hz8 : z < 8) :
    (F3All.logLower z : ℝ) ≤ log (z : ℝ) ∧
      log (z : ℝ) ≤ (F3All.logUpper z : ℝ) := by
  have hc := log_anchor_chart hz hz8
  have hv := log_chart_bounds hz hz8
  have hcR : (0 : ℝ) < F3All.logAnchor z := by exact_mod_cast hc.1
  have hvR : (1 : ℝ) ≤ (F3All.logReduced z : ℝ) / (F3All.logAnchor z : ℝ) := by
    exact_mod_cast hv.1
  have hv4R : (F3All.logReduced z : ℝ) / (F3All.logAnchor z : ℝ) < (4/3 : ℝ) := by
    have hh : ((F3All.logReduced z / F3All.logAnchor z : Rat) : ℝ) <
        ((4/3 : Rat) : ℝ) := by exact_mod_cast hv.2.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hh
  have hidR : (z : ℝ) = (2 : ℝ) ^ F3All.logIndex z * (F3All.logAnchor z : ℝ) *
      ((F3All.logReduced z : ℝ) / (F3All.logAnchor z : ℝ)) := by
    exact_mod_cast log_chart_factorization hz hz8
  have h := log_factor_brackets (F3All.logIndex z) hcR hvR hv4R hidR
    log_two_brackets (log_anchor_brackets hz hz8)
  simpa [F3All.logLower, F3All.logUpper, seriesS_cast, seriesT_cast, logW_cast] using h

theorem log_envelopes_of_useOK {z : Rat} (h : F3All.logUseOK z = true) :
    (F3All.logLower z : ℝ) ≤ log (z : ℝ) ∧
      log (z : ℝ) ≤ (F3All.logUpper z : ℝ) := by
  have hz : 1 ≤ z ∧ z < 8 := of_decide_eq_true h
  exact log_envelopes hz.1 hz.2

/-- Strict endpoint comparisons are transferred only after the use-domain guard. -/
theorem log_point_of_checks {z lo hi : Rat} (hz : F3All.logUseOK z = true)
    (hl : (Comparison.ofRats lo (F3All.logLower z) .lt).check = true)
    (hu : (Comparison.ofRats (F3All.logUpper z) hi .lt).check = true) :
    (lo : ℝ) < log (z : ℝ) ∧ log (z : ℝ) < (hi : ℝ) := by
  have he := log_envelopes_of_useOK hz
  exact ⟨(ofRats_lt_real hl).trans_le he.1, he.2.trans_lt (ofRats_lt_real hu)⟩

end Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.logReduced_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.logReduced_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_anchor_chart
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_anchor_chart
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_anchor_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_anchor_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_chart_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_chart_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_chart_factorization
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_chart_factorization
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.logW_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.logW_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_envelopes
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_envelopes
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_envelopes_of_useOK
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_envelopes_of_useOK
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_point_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_point_of_checks
