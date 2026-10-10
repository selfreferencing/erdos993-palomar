module

public import Erdos993Lean.Analytic.V213.FreeCountRealExpEnvelopes
public import Erdos993Lean.ExactComparisons.F3All.Formulas

/-!
Exact checker-to-Real transport. The old rational
worksheet is not changed. Only explicit accepted Boolean hypotheses are
consumed; this file does not accept any data list by itself. Log branch
selection and the continuous cell conclusions remain separate obligations.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

open Real Erdos993Lean.ExactComparisons

def comparisonRealHolds (c : Comparison) : Prop :=
  0 < c.leftDen ∧ 0 < c.rightDen ∧
    match c.relation with
    | .lt => (c.leftNum : ℝ)/(c.leftDen : ℝ) < (c.rightNum : ℝ)/(c.rightDen : ℝ)
    | .le => (c.leftNum : ℝ)/(c.leftDen : ℝ) ≤ (c.rightNum : ℝ)/(c.rightDen : ℝ)
    | .eq => (c.leftNum : ℝ)/(c.leftDen : ℝ) = (c.rightNum : ℝ)/(c.rightDen : ℝ)

theorem comparison_check_real_sound (c : Comparison) (h : c.check = true) :
    comparisonRealHolds c := by
  have hr : 0 < c.leftDen ∧ 0 < c.rightDen ∧ c.crossHolds := of_decide_eq_true h
  have hl : (0 : ℝ) < c.leftDen := by exact_mod_cast hr.1
  have hh : (0 : ℝ) < c.rightDen := by exact_mod_cast hr.2.1
  refine ⟨hr.1, hr.2.1, ?_⟩
  cases he : c.relation with
  | lt =>
    apply (div_lt_div_iff₀ hl hh).2
    have hz : c.leftNum*c.rightDen < c.rightNum*c.leftDen := by
      simpa [Comparison.crossHolds, he] using hr.2.2
    exact_mod_cast hz
  | le =>
    apply (div_le_div_iff₀ hl hh).2
    have hz : c.leftNum*c.rightDen ≤ c.rightNum*c.leftDen := by
      simpa [Comparison.crossHolds, he] using hr.2.2
    exact_mod_cast hz
  | eq =>
    apply (div_eq_div_iff hl.ne' hh.ne').2
    have hz : c.leftNum*c.rightDen = c.rightNum*c.leftDen := by
      simpa [Comparison.crossHolds, he] using hr.2.2
    exact_mod_cast hz

theorem list_check_real_sound (records : List Comparison) (h : check records = true) :
    ∀ c ∈ records, comparisonRealHolds c := by
  intro c hc
  apply comparison_check_real_sound c
  exact (List.all_eq_true.mp h) c hc

theorem ofRats_lt_real {a b : Rat} (h : (Comparison.ofRats a b .lt).check = true) :
    (a : ℝ) < (b : ℝ) := by
  have hr : a < b := Comparison.ofRats_sound a b .lt h
  exact_mod_cast hr

theorem ofRats_le_real {a b : Rat} (h : (Comparison.ofRats a b .le).check = true) :
    (a : ℝ) ≤ (b : ℝ) := by
  have hr : a ≤ b := Comparison.ofRats_sound a b .le h
  exact_mod_cast hr

theorem ofRats_eq_real {a b : Rat} (h : (Comparison.ofRats a b .eq).check = true) :
    (a : ℝ) = (b : ℝ) := by
  have hr : a = b := Comparison.ofRats_sound a b .eq h
  exact_mod_cast hr

theorem seriesS_cast (w : Rat) : (F3All.seriesS w : ℝ) = seriesS (w : ℝ) := by
  simp [F3All.seriesS, seriesS]

theorem seriesT_cast (w : Rat) : (F3All.seriesT w : ℝ) = seriesT (w : ℝ) := by
  simp [F3All.seriesT, seriesT, seriesS_cast]

theorem polyP3_cast (x : Rat) : (F3All.polyP3 x : ℝ) = polyP3 (x : ℝ) := by
  simp [F3All.polyP3, polyP3]

theorem polyP4_cast (x : Rat) : (F3All.polyP4 x : ℝ) = polyP4 (x : ℝ) := by
  simp [F3All.polyP4, polyP4]

theorem expLower_cast (y : Rat) : (F3All.expLower y : ℝ) = expLower (y : ℝ) := by
  simp [F3All.expLower, expLower, polyQ4, polyP4_cast, neg_div]

theorem expUpper_cast (y : Rat) : (F3All.expUpper y : ℝ) = expUpper (y : ℝ) := by
  simp [F3All.expUpper, expUpper, polyQ3, polyP3_cast, neg_div]

/-- Two actual strict E-side checks, not a precomputed Real enclosure premise. -/
theorem exp_point_of_checks {y lo hi : Rat} (hy : 0 ≤ y) (hy3 : y ≤ 3)
    (hl : (Comparison.ofRats lo (F3All.expLower y) .lt).check = true)
    (hu : (Comparison.ofRats (F3All.expUpper y) hi .lt).check = true) :
    (lo : ℝ) < exp (y : ℝ) ∧ exp (y : ℝ) < (hi : ℝ) := by
  have hl' := ofRats_lt_real hl
  have hu' := ofRats_lt_real hu
  rw [expLower_cast] at hl'
  rw [expUpper_cast] at hu'
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hy3' : (y : ℝ) ≤ 3 := by exact_mod_cast hy3
  have he := exp_envelopes hy' hy3'
  exact ⟨hl'.trans_le he.1, he.2.trans_lt hu'⟩

/-- A generic strict rational-side check can cross a proved weak Real envelope. -/
theorem strict_lower_transfer {a b : Rat} {x : ℝ}
    (h : (Comparison.ofRats a b .lt).check = true) (hb : (b : ℝ) ≤ x) :
    (a : ℝ) < x := (ofRats_lt_real h).trans_le hb

theorem strict_upper_transfer {a b : Rat} {x : ℝ}
    (h : (Comparison.ofRats a b .lt).check = true) (ha : x ≤ (a : ℝ)) :
    x < (b : ℝ) := ha.trans_lt (ofRats_lt_real h)

end Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.comparison_check_real_sound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.comparison_check_real_sound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.list_check_real_sound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.list_check_real_sound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.ofRats_lt_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.ofRats_lt_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.ofRats_le_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.ofRats_le_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.ofRats_eq_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.ofRats_eq_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.seriesS_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.seriesS_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.seriesT_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.seriesT_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyP3_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyP3_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyP4_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyP4_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.expLower_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.expLower_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.expUpper_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.expUpper_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_point_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_point_of_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.strict_lower_transfer
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.strict_lower_transfer
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.strict_upper_transfer
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.strict_upper_transfer
