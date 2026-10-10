module

public import Erdos993Lean.LowMeanFast.FastCheck
public import Erdos993Lean.Analytic.V213.LowMeanBudgetFamily

/-!
The same replacement for the low-mean budget family: the two formula checks inside
`lowMeanBudgetFamilyCheck` (the budget expression against `lowMeanBudgetShapeMinimum`, the anchor
expression against `lowMeanBudgetAnchorShape`) go through `fastShapeCheck`; everything else is the
original code.  `fastBudgetGroup_sound` gives the original group statements.
-/

@[expose] public section

namespace Erdos993Lean.LowMeanFast
open Erdos993Lean.Analytic.V213

noncomputable def fastBudgetRecordCheck (c : LowMeanCertificateInput) (r : LowMeanBudgetRecord) : Bool :=
  lowMeanBudgetInputCheck c r.input &&
    decide (lowMeanFractionValid r.bound ∧ 0 ≤ r.bound.1) &&
    fastPositiveCheck r.expression (lowMeanBudgetShapeMinimum r.input) r.bound

theorem fastBudgetRecordCheck_sound (c : LowMeanCertificateInput) (r : LowMeanBudgetRecord)
    (h : fastBudgetRecordCheck c r = true) : lowMeanBudgetRecordCheck c r = true := by
  simp only [fastBudgetRecordCheck, Bool.and_eq_true] at h
  simp only [lowMeanBudgetRecordCheck, Bool.and_eq_true]
  exact ⟨⟨h.1.1, h.1.2⟩, fastPositiveCheck_sound h.2⟩

noncomputable def fastBudgetAnchorCheck (r : LowMeanBudgetRecord) : Bool :=
  decide (r.anchorTag ≤ 3 ∧ (r.anchorTag = 3 → 0 < r.input.M)) &&
    fastEqualityCheck r.anchorExpression (lowMeanBudgetAnchorShape r.input r.anchorTag) r.input.tau

theorem fastBudgetAnchorCheck_sound (r : LowMeanBudgetRecord)
    (h : fastBudgetAnchorCheck r = true) : lowMeanBudgetAnchorCheck r = true := by
  simp only [fastBudgetAnchorCheck, Bool.and_eq_true] at h
  simp only [lowMeanBudgetAnchorCheck, Bool.and_eq_true]
  exact ⟨h.1, fastEqualityCheck_sound h.2⟩

noncomputable def fastBudgetFamilyCheck (r : LowMeanBudgetRecord) : Bool :=
  decide (0 < r.certificate ∧ r.certificate ≤ 28 ∧ r.kind ≤ 3 ∧
    (r.kind = 3 → r.certificate = 1 ∧ 0 < (lowMeanSpecialBudgetBound r.input.M r.input.j).1) ∧
    r.bound = lowMeanBudgetExpectedBound r) &&
  fastBudgetRecordCheck (lowMeanCertificateAt (r.certificate - 1)) r &&
  lowMeanBudgetIntervalCheck (lowMeanCertificateAt (r.certificate - 1)) r &&
  (if r.kind = 3 then decide (r.input.tau = lowMeanSpecialBudgetTau r.input.M r.input.j)
    else fastBudgetAnchorCheck r)

theorem fastBudgetFamilyCheck_sound (r : LowMeanBudgetRecord)
    (h : fastBudgetFamilyCheck r = true) : lowMeanBudgetFamilyCheck r = true := by
  simp only [fastBudgetFamilyCheck, Bool.and_eq_true] at h
  simp only [lowMeanBudgetFamilyCheck, Bool.and_eq_true]
  refine ⟨⟨⟨h.1.1.1, fastBudgetRecordCheck_sound _ r h.1.1.2⟩, h.1.2⟩, ?_⟩
  have h2 := h.2
  by_cases hk : r.kind = 3
  · rw [ite_eq_left hk] at h2 ⊢
    exact h2
  · rw [ite_eq_right hk] at h2 ⊢
    exact fastBudgetAnchorCheck_sound r h2

/-- A budget group that passes the fast check passes the original check. -/
theorem fastBudgetGroup_sound (g : List LowMeanBudgetRecord) (h : g.all fastBudgetFamilyCheck = true) :
    g.all lowMeanBudgetFamilyCheck = true := by
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => fastBudgetFamilyCheck_sound r (h r hr)

end Erdos993Lean.LowMeanFast

#print axioms Erdos993Lean.LowMeanFast.fastBudgetGroup_sound
