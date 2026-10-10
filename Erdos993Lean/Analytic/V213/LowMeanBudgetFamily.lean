module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetAnchor
public import Erdos993Lean.Analytic.V213.LowMeanScalarChecker

/-!
Budget family checks. The printed special targets and the
ordinary strict 1/50000 target are retained, and record keys are explicit.
This module proves generic consumption soundness without defining a family.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanSpecialBudgetBound (M : ℕ) (j : ℤ) : lowMeanFraction :=
  if M = 13 ∧ j = 0 then (1342, 1000000)
  else if M = 15 ∧ j = 0 then (958, 1000000)
  else if M = 15 ∧ j = 1 then (1477, 1000000)
  else if M = 17 ∧ j = 0 then (1975, 1000000)
  else if M = 17 ∧ j = 1 then (3138, 1000000)
  else if M = 18 ∧ j = 2 then (4193, 1000000)
  else if M = 19 ∧ j = 1 then (6098, 1000000)
  else (0, 1)

def lowMeanSpecialBudgetTau (M : ℕ) (j : ℤ) : lowMeanFraction :=
  if M = 13 ∧ j = 0 then (21, 64)
  else if M = 15 ∧ j = 0 then (19, 64)
  else if M = 15 ∧ j = 1 then (23, 64)
  else if M = 17 ∧ j = 0 then (17, 64)
  else if M = 17 ∧ j = 1 then (21, 64)
  else if M = 18 ∧ j = 2 then (23, 64)
  else if M = 19 ∧ j = 1 then (19, 64)
  else (0, 1)


def lowMeanBudgetExpectedBound (r : LowMeanBudgetRecord) : lowMeanFraction :=
  if r.kind = 3 then lowMeanSpecialBudgetBound r.input.M r.input.j else (1, 50000)

def lowMeanBudgetFamilyCheck (r : LowMeanBudgetRecord) : Bool :=
  decide (0 < r.certificate ∧ r.certificate ≤ 28 ∧ r.kind ≤ 3 ∧
    (r.kind = 3 → r.certificate = 1 ∧ 0 < (lowMeanSpecialBudgetBound r.input.M r.input.j).1) ∧
    r.bound = lowMeanBudgetExpectedBound r) &&
  lowMeanBudgetRecordCheck (lowMeanCertificateAt (r.certificate - 1)) r &&
  lowMeanBudgetIntervalCheck (lowMeanCertificateAt (r.certificate - 1)) r &&
  (if r.kind = 3 then decide (r.input.tau = lowMeanSpecialBudgetTau r.input.M r.input.j)
    else lowMeanBudgetAnchorCheck r)

theorem lowMean_budgetFamily_slack (r : LowMeanBudgetRecord)
    (h : lowMeanBudgetFamilyCheck r = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal r.input.L) (lowMeanFractionReal r.input.H)) :
    lowMeanFractionReal r.input.zeta <
      lowMeanH q (lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).wL)
        (lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).wR)
        (lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).xi)
        (lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).eta) r.input.M r.input.j -
      lowMeanPsi (lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).alpha)
        (lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).beta)
        (lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).gamma)
        (lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).m0) r.input.M +
      lowMeanFractionReal (lowMeanCertificateAt (r.certificate - 1)).z * (1 - q) ^ r.input.M := by
  simp only [lowMeanBudgetFamilyCheck, Bool.and_eq_true] at h
  exact lowMean_budgetRecord_slack _ r h.1.1.2 hq

theorem lowMean_budgetFamily_minimum (r : LowMeanBudgetRecord)
    (h : lowMeanBudgetFamilyCheck r = true) :
    lowMeanFractionReal (lowMeanBudgetExpectedBound r) <
      lowMeanBudgetMinimumAt (lowMeanBudgetInputTerms r.input) r.input.M r.input.j
        (lowMeanFractionReal r.input.eta) (lowMeanFractionReal r.input.xi) (lowMeanFractionReal r.input.alpha)
        (lowMeanFractionReal r.input.beta) (lowMeanFractionReal r.input.gamma) (lowMeanFractionReal r.input.m0)
        (lowMeanFractionReal r.input.zeta) (lowMeanFractionReal r.input.L) (lowMeanFractionReal r.input.H)
        (lowMeanFractionReal r.input.tau) := by
  simp only [lowMeanBudgetFamilyCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hp := lowMean_budgetRecord_minimum _ r h.1.1.2
  rw [h.1.1.1.2.2.2.2] at hp
  exact hp


theorem lowMean_budgetFamily_endpoints (r : LowMeanBudgetRecord)
    (h : lowMeanBudgetFamilyCheck r = true) :
    let c := lowMeanCertificateAt (r.certificate - 1)
    lowMeanFractionReal r.input.L = (if r.kind = 2 then (lowMeanFractionReal c.l + lowMeanFractionReal c.h) / 2 else lowMeanFractionReal c.l) ∧
    lowMeanFractionReal r.input.H = (if r.kind = 1 then (lowMeanFractionReal c.l + lowMeanFractionReal c.h) / 2 else lowMeanFractionReal c.h) := by
  simp only [lowMeanBudgetFamilyCheck, Bool.and_eq_true] at h
  have hc := h.1.1.2
  simp only [lowMeanBudgetRecordCheck, Bool.and_eq_true] at hc
  exact lowMean_budgetInterval_endpoints _ r hc.1.1 h.1.2

/-- Each ordinary selected anchor belongs to the exact printed finite set.
The seven additional anchors are handled by their separate printed rule. -/
theorem lowMean_budgetFamily_anchor (r : LowMeanBudgetRecord)
    (h : lowMeanBudgetFamilyCheck r = true) (hnormal : r.kind ≠ 3) :
    lowMeanFractionReal r.input.tau ∈ lowMeanAnchors r.input.M r.input.j
      (lowMeanFractionReal r.input.xi) (lowMeanFractionReal r.input.eta)
      (lowMeanFractionReal r.input.L) (lowMeanFractionReal r.input.H) := by
  simp only [lowMeanBudgetFamilyCheck, Bool.and_eq_true, hnormal, ite_false] at h
  exact lowMean_budgetAnchor_member r h.2

/-- The printed ordinary R(I) comparison follows from a checked exact
anchor budget, rather than merely from a positive root expression. -/
theorem lowMean_budgetFamily_R (r : LowMeanBudgetRecord)
    (h : lowMeanBudgetFamilyCheck r = true) (hnormal : r.kind ≠ 3) :
    lowMeanFractionReal (lowMeanBudgetExpectedBound r) <
      lowMeanBestBudget (lowMeanBudgetInputTerms r.input) r.input.M r.input.j
        (lowMeanFractionReal r.input.eta) (lowMeanFractionReal r.input.xi) (lowMeanFractionReal r.input.alpha)
        (lowMeanFractionReal r.input.beta) (lowMeanFractionReal r.input.gamma) (lowMeanFractionReal r.input.m0)
        (lowMeanFractionReal r.input.zeta) (lowMeanFractionReal r.input.L) (lowMeanFractionReal r.input.H) := by
  exact lt_of_lt_of_le (lowMean_budgetFamily_minimum r h)
    (lowMean_anchorMaximum_le _ _ _ _ _ _ _ (lowMean_budgetFamily_anchor r h hnormal))

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetFamily_slack
