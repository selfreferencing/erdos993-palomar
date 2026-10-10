module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetChecker
public import Erdos993Lean.Analytic.V213.LowMeanIntegerOrder

/-!
Explicit source anchor binding. The result-erased formula
contains every integer leaf from the budget input. The fourth anchor is
admitted only at M>0, exactly as in the printed finite set.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanBudgetAnchorShape (r : LowMeanBudgetInput) (tag : ℕ) : LowMeanIntegerShape :=
  if tag = 0 then .atom r.L
  else if tag = 1 then .atom r.H
  else if tag = 2 then .div (.add (.atom r.L) (.atom r.H)) (lowMeanShapeInt 2)
  else .maximum (.atom r.L) (.minimum (.atom r.H)
    (.div (.add (lowMeanShapeInt r.j) (.div (.atom r.xi) (.mul (lowMeanShapeInt 2) (.atom r.eta))))
      (lowMeanShapeInt r.M)))

noncomputable def lowMeanBudgetAnchorValue (r : LowMeanBudgetInput) (tag : ℕ) : ℝ :=
  if tag = 0 then lowMeanFractionReal r.L
  else if tag = 1 then lowMeanFractionReal r.H
  else if tag = 2 then (lowMeanFractionReal r.L + lowMeanFractionReal r.H) / 2
  else max (lowMeanFractionReal r.L) (min (lowMeanFractionReal r.H)
    (((r.j : ℝ) + lowMeanFractionReal r.xi / (2 * lowMeanFractionReal r.eta)) / r.M))

@[simp] theorem lowMean_budgetAnchor_shape_real (r : LowMeanBudgetInput) (tag : ℕ) :
    lowMeanIntegerShapeReal (lowMeanBudgetAnchorShape r tag) = lowMeanBudgetAnchorValue r tag := by
  unfold lowMeanBudgetAnchorShape lowMeanBudgetAnchorValue
  split_ifs <;> simp [lowMeanIntegerShapeReal]

def lowMeanBudgetAnchorCheck (r : LowMeanBudgetRecord) : Bool :=
  decide (r.anchorTag ≤ 3 ∧ (r.anchorTag = 3 → 0 < r.input.M)) &&
    lowMeanIntegerEqualityCheck r.anchorExpression (lowMeanBudgetAnchorShape r.input r.anchorTag) r.input.tau

theorem lowMean_budgetAnchor_member (r : LowMeanBudgetRecord)
    (h : lowMeanBudgetAnchorCheck r = true) :
    lowMeanFractionReal r.input.tau ∈ lowMeanAnchors r.input.M r.input.j
      (lowMeanFractionReal r.input.xi) (lowMeanFractionReal r.input.eta)
      (lowMeanFractionReal r.input.L) (lowMeanFractionReal r.input.H) := by
  classical
  simp only [lowMeanBudgetAnchorCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have he := lowMean_integerEquality_sound h.2
  rw [lowMean_budgetAnchor_shape_real] at he
  rw [← he]
  have htag : r.anchorTag ≤ 3 := h.1.1
  interval_cases ht : r.anchorTag
  · simp [lowMeanBudgetAnchorValue, lowMeanAnchors]
  · simp [lowMeanBudgetAnchorValue, lowMeanAnchors]
  · simp [lowMeanBudgetAnchorValue, lowMeanAnchors]
  · have hM : r.input.M ≠ 0 := by have hp := h.1.2 rfl; omega
    simp [lowMeanBudgetAnchorValue, lowMeanAnchors, hM]

def lowMeanBudgetMidpoint (c : LowMeanCertificateInput) : lowMeanFraction :=
  lowMeanFractionMul (lowMeanFractionAdd c.l c.h) (1, 2)
def lowMeanBudgetExpectedL (c : LowMeanCertificateInput) (kind : ℕ) : lowMeanFraction :=
  if kind = 2 then lowMeanBudgetMidpoint c else c.l
def lowMeanBudgetExpectedH (c : LowMeanCertificateInput) (kind : ℕ) : lowMeanFraction :=
  if kind = 1 then lowMeanBudgetMidpoint c else c.h
def lowMeanBudgetIntervalCheck (c : LowMeanCertificateInput) (r : LowMeanBudgetRecord) : Bool :=
  decide (lowMeanFractionValid c.l ∧ lowMeanFractionValid c.h ∧
    lowMeanFractionEq r.input.L (lowMeanBudgetExpectedL c r.kind) ∧
    lowMeanFractionEq r.input.H (lowMeanBudgetExpectedH c r.kind))

@[simp] theorem lowMean_budgetMidpoint_real (c : LowMeanCertificateInput)
    (hl : lowMeanFractionValid c.l) (hh : lowMeanFractionValid c.h) :
    lowMeanFractionReal (lowMeanBudgetMidpoint c) = (lowMeanFractionReal c.l + lowMeanFractionReal c.h) / 2 := by
  rw [lowMeanBudgetMidpoint, lowMean_fraction_mul, lowMean_fraction_add hl hh]
  norm_num [lowMeanFractionReal]
  ring

theorem lowMean_budgetInterval_endpoints (c : LowMeanCertificateInput) (r : LowMeanBudgetRecord)
    (hinput : lowMeanBudgetInputCheck c r.input = true)
    (h : lowMeanBudgetIntervalCheck c r = true) :
    lowMeanFractionReal r.input.L = (if r.kind = 2 then (lowMeanFractionReal c.l + lowMeanFractionReal c.h) / 2 else lowMeanFractionReal c.l) ∧
    lowMeanFractionReal r.input.H = (if r.kind = 1 then (lowMeanFractionReal c.l + lowMeanFractionReal c.h) / 2 else lowMeanFractionReal c.h) := by
  simp only [lowMeanBudgetIntervalCheck, decide_eq_true_eq] at h
  have hm : lowMeanFractionValid (lowMeanBudgetMidpoint c) := Nat.mul_pos (Nat.mul_pos h.1 h.2.1) (by decide)
  have hvL : lowMeanFractionValid (lowMeanBudgetExpectedL c r.kind) := by
    unfold lowMeanBudgetExpectedL
    split_ifs
    · exact hm
    · exact h.1
  have hvH : lowMeanFractionValid (lowMeanBudgetExpectedH c r.kind) := by
    unfold lowMeanBudgetExpectedH
    split_ifs
    · exact hm
    · exact h.2.1
  have hl := lowMean_budgetInput_valid c r.input hinput r.input.L (by simp [lowMeanBudgetInputFractions])
  have hh := lowMean_budgetInput_valid c r.input hinput r.input.H (by simp [lowMeanBudgetInputFractions])
  constructor
  · have he := (lowMean_fraction_eq_iff hl hvL).mp h.2.2.1
    unfold lowMeanBudgetExpectedL at he
    split_ifs with hk
    · simpa only [hk, ite_true, lowMean_budgetMidpoint_real c h.1 h.2.1] using he
    · simpa only [hk, ite_false] using he
  · have he := (lowMean_fraction_eq_iff hh hvH).mp h.2.2.2
    unfold lowMeanBudgetExpectedH at he
    split_ifs with hk
    · simpa only [hk, ite_true, lowMean_budgetMidpoint_real c h.1 h.2.1] using he
    · simpa only [hk, ite_false] using he

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetAnchor_member
