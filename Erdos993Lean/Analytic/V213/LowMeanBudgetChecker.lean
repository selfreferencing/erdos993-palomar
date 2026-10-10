module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetShape
public import Erdos993Lean.Analytic.V213.LowMeanCanonicalInteger
public import Erdos993Lean.Analytic.V213.LowMeanAnchorBudget
public import Erdos993Lean.Analytic.V213.LowMeanScalarShape

/-!
Semantic checker for reviewed budget records. It checks the
certificate leaves, probability/anchor domain, every retained monomial,
the exhaustive canonical coefficient binding, and the full formula shape.
A successful check proves strict actual slack throughout the interval.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

structure LowMeanBudgetRecord where
  record : ℕ
  kind : ℕ
  certificate : ℕ
  input : LowMeanBudgetInput
  expression : LowMeanIntegerExpr
  anchorTag : ℕ
  anchorExpression : LowMeanIntegerExpr
  bound : lowMeanFraction

def lowMeanBudgetInputFractions (r : LowMeanBudgetInput) : List lowMeanFraction :=
  [r.eta, r.xi, r.alpha, r.beta, r.gamma, r.m0, r.zeta, r.L, r.H, r.tau]
def lowMeanBudgetInputCheck (c : LowMeanCertificateInput) (r : LowMeanBudgetInput) : Bool :=
  (lowMeanBudgetInputFractions r).all (fun f => decide (lowMeanFractionValid f)) &&
    decide (r.eta = c.eta ∧ r.xi = c.xi ∧ r.alpha = c.alpha ∧ r.beta = c.beta ∧ r.gamma = c.gamma ∧ r.m0 = c.m0 ∧
      0 < r.L.1 ∧ lowMeanFractionLT r.H (1, 1) ∧ lowMeanFractionLT r.L r.H ∧
      lowMeanFractionLE r.L r.tau ∧ lowMeanFractionLE r.tau r.H) &&
    r.terms.all (fun t => decide (t.1.1 ≠ 0 ∧ 0 ≤ t.2.1 + t.2.2)) &&
    lowMeanIntegerBindingCheck (lowMeanCanonicalIntegerTerms r.M r.j c.wL c.wR c.z) r.terms

def lowMeanBudgetRecordCheck (c : LowMeanCertificateInput) (r : LowMeanBudgetRecord) : Bool :=
  lowMeanBudgetInputCheck c r.input &&
    decide (lowMeanFractionValid r.bound ∧ 0 ≤ r.bound.1) &&
    lowMeanIntegerPositiveCheck r.expression (lowMeanBudgetShapeMinimum r.input) r.bound

theorem lowMean_budgetInput_valid (c : LowMeanCertificateInput) (r : LowMeanBudgetInput)
    (h : lowMeanBudgetInputCheck c r = true) (f : lowMeanFraction) (hf : f ∈ lowMeanBudgetInputFractions r) :
    lowMeanFractionValid f := by
  simp only [lowMeanBudgetInputCheck, Bool.and_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.mp h.1.1.1 f hf)

theorem lowMean_budgetInput_domain (c : LowMeanCertificateInput) (r : LowMeanBudgetInput)
    (h : lowMeanBudgetInputCheck c r = true) :
    0 < lowMeanFractionReal r.L ∧ lowMeanFractionReal r.H < 1 ∧
      lowMeanFractionReal r.L < lowMeanFractionReal r.H ∧
      lowMeanFractionReal r.tau ∈ Set.Icc (lowMeanFractionReal r.L) (lowMeanFractionReal r.H) := by
  have hvalid f (hf : f ∈ lowMeanBudgetInputFractions r) := lowMean_budgetInput_valid c r h f hf
  have hL := hvalid r.L (by simp [lowMeanBudgetInputFractions])
  have hH := hvalid r.H (by simp [lowMeanBudgetInputFractions])
  have ht := hvalid r.tau (by simp [lowMeanBudgetInputFractions])
  simp only [lowMeanBudgetInputCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hk := h.1.1.2.2.2.2.2.2.2
  refine ⟨div_pos (by exact_mod_cast hk.1) (lowMean_fraction_den_pos hL), ?_,
    (lowMean_fraction_lt_iff hL hH).mp hk.2.2.1,
    (lowMean_fraction_le_iff hL ht).mp hk.2.2.2.1,
    (lowMean_fraction_le_iff ht hH).mp hk.2.2.2.2⟩
  simpa [lowMeanFractionReal] using (lowMean_fraction_lt_iff hH (show lowMeanFractionValid (1, 1) by decide)).mp hk.2.1

theorem lowMean_budgetInput_terms (c : LowMeanCertificateInput) (r : LowMeanBudgetInput)
    (h : lowMeanBudgetInputCheck c r = true) :
    ∀ t ∈ lowMeanBudgetInputTerms r, t.1 ≠ 0 ∧ 0 ≤ t.2.1 + t.2.2 := by
  simp only [lowMeanBudgetInputCheck, Bool.and_eq_true] at h
  have hb := h.2
  simp only [lowMeanIntegerBindingCheck, Bool.and_eq_true] at hb
  have hv := lowMean_integerTerms_valid hb.1.2
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hn : u.1.1 ≠ 0 ∧ 0 ≤ u.2.1 + u.2.2 := of_decide_eq_true (List.all_eq_true.mp h.1.2 u hu)
  exact ⟨div_ne_zero (by exact_mod_cast hn.1) (lowMean_fraction_den_pos (hv u hu)).ne', hn.2⟩

/-- The complete integer check implies the printed exact minimum bound. -/
theorem lowMean_budgetRecord_minimum (c : LowMeanCertificateInput) (r : LowMeanBudgetRecord)
    (h : lowMeanBudgetRecordCheck c r = true) :
    lowMeanFractionReal r.bound < lowMeanBudgetMinimumAt (lowMeanBudgetInputTerms r.input) r.input.M r.input.j
      (lowMeanFractionReal r.input.eta) (lowMeanFractionReal r.input.xi) (lowMeanFractionReal r.input.alpha)
      (lowMeanFractionReal r.input.beta) (lowMeanFractionReal r.input.gamma) (lowMeanFractionReal r.input.m0)
      (lowMeanFractionReal r.input.zeta) (lowMeanFractionReal r.input.L) (lowMeanFractionReal r.input.H)
      (lowMeanFractionReal r.input.tau) := by
  simp only [lowMeanBudgetRecordCheck, Bool.and_eq_true] at h
  simpa only [lowMeanBudgetShapeMinimum, lowMean_shape_quadMin, lowMean_budgetShape_A, lowMean_budgetShape_B,
    lowMean_budgetShape_C, lowMeanIntegerShapeReal, lowMeanBudgetMinimumAt] using lowMean_integerPositive_sound h.2

/-- Shape positivity cannot certify unrelated numbers: the coefficient
binding and certificate leaves are checked before deriving actual slack. -/
theorem lowMean_budgetRecord_slack (c : LowMeanCertificateInput) (r : LowMeanBudgetRecord)
    (h : lowMeanBudgetRecordCheck c r = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal r.input.L) (lowMeanFractionReal r.input.H)) :
    lowMeanFractionReal r.input.zeta <
      lowMeanH q (lowMeanFractionReal c.wL) (lowMeanFractionReal c.wR)
        (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta) r.input.M r.input.j -
      lowMeanPsi (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
        (lowMeanFractionReal c.m0) r.input.M + lowMeanFractionReal c.z * (1 - q) ^ r.input.M := by
  have hmin := lowMean_budgetRecord_minimum c r h
  simp only [lowMeanBudgetRecordCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hL, hH, hLH, ht⟩ := lowMean_budgetInput_domain c r.input h.1.1
  have hterms := lowMean_budgetInput_terms c r.input h.1.1
  have hk := h.1.1
  simp only [lowMeanBudgetInputCheck, Bool.and_eq_true, decide_eq_true_eq] at hk
  have hf := hk.1.1.2
  have hb : 0 ≤ lowMeanFractionReal r.bound :=
    div_nonneg (by exact_mod_cast h.1.2.2) (lowMean_fraction_den_pos h.1.2.1).le
  have hp : 0 < lowMeanBudgetMinimumAt (lowMeanBudgetInputTerms r.input) r.input.M r.input.j
      (lowMeanFractionReal r.input.eta) (lowMeanFractionReal r.input.xi) (lowMeanFractionReal r.input.alpha)
      (lowMeanFractionReal r.input.beta) (lowMeanFractionReal r.input.gamma) (lowMeanFractionReal r.input.m0)
      (lowMeanFractionReal r.input.zeta) (lowMeanFractionReal r.input.L) (lowMeanFractionReal r.input.H)
      (lowMeanFractionReal r.input.tau) := lt_of_le_of_lt hb hmin
  rw [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1] at hp
  apply lowMean_slack_positive_of_quadratic hLH hp ?_ hq
  intro p hpp
  rw [← lowMean_budget_coefficients]
  have hi := lowMean_canonicalInteger_binding r.input.M r.input.j c.wL c.wR c.z r.input.terms hk.2
    (lt_of_lt_of_le hL hpp.1) (lt_of_le_of_lt hpp.2 hH)
  simpa only [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1] using
    lowMean_slack_support (lowMeanBudgetInputTerms r.input) hL hH hLH ht hpp hterms hi

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetRecord_slack
