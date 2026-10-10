module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetTerms
public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanHalfCoverage

/-!
Complete direct seeds from exact cores and reviewed interval budgets.
Each core position has either one whole/special budget or both closed
half budgets, with identical certificate, width, rank and target keys.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCertificateSlack (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  lowMeanH q (lowMeanFractionReal c.wL) (lowMeanFractionReal c.wR)
    (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta) M j -
  lowMeanPsi (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta)
    (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0) M +
  lowMeanFractionReal c.z * (1 - q) ^ M

structure LowMeanSeedBudgetChoice where
  j : ℤ
  mode : ℕ
  left : ℕ
  right : ℕ
structure LowMeanFiberBudgetInput where
  fiber : LowMeanFiberInput
  positions : List LowMeanSeedBudgetChoice

noncomputable def lowMeanSeedBudgetKeyCheck (f : LowMeanFiberInput) (j : ℤ) (i kind : ℕ) : Bool :=
  let r := lowMeanBudgetAt i
  decide (i < 1114 ∧ r.certificate = f.certificate ∧ r.input.M = f.M ∧ r.input.j = j ∧
    r.input.zeta = f.zeta ∧ r.kind = kind)
noncomputable def lowMeanSeedChoiceCheck (f : LowMeanFiberInput) (w : LowMeanSeedBudgetChoice) : Bool :=
  decide (w.mode ≤ 2) &&
  lowMeanSeedBudgetKeyCheck f w.j w.left (if w.mode = 1 then 1 else if w.mode = 2 then 3 else 0) &&
  (if w.mode = 1 then lowMeanSeedBudgetKeyCheck f w.j w.right 2 &&
    decide ((lowMeanBudgetAt w.right).input.terms = (lowMeanBudgetAt w.left).input.terms) else true)
noncomputable def lowMeanFiberBudgetCheck (b : LowMeanFiberBudgetInput) : Bool :=
  decide (b.positions.map LowMeanSeedBudgetChoice.j = b.fiber.core) &&
    b.positions.all (lowMeanSeedChoiceCheck b.fiber)

theorem lowMean_budgetAt_checked (i : ℕ) (hi : i < 1114) :
    lowMeanBudgetFamilyCheck (lowMeanBudgetAt i) = true := by
  apply lowMean_budgets_checked
  exact lowMean_list_getD_mem _ _ i (by simpa only [lowMean_budgets_length] using hi)

theorem lowMean_seedBudget_endpoints (f : LowMeanFiberInput) (j : ℤ) (i kind : ℕ)
    (h : lowMeanSeedBudgetKeyCheck f j i kind = true) :
    lowMeanFractionReal (lowMeanBudgetAt i).input.L =
      (if kind = 2 then (lowMeanFractionReal (lowMeanFiberCertificate f).l + lowMeanFractionReal (lowMeanFiberCertificate f).h) / 2
        else lowMeanFractionReal (lowMeanFiberCertificate f).l) ∧
    lowMeanFractionReal (lowMeanBudgetAt i).input.H =
      (if kind = 1 then (lowMeanFractionReal (lowMeanFiberCertificate f).l + lowMeanFractionReal (lowMeanFiberCertificate f).h) / 2
        else lowMeanFractionReal (lowMeanFiberCertificate f).h) := by
  simp only [lowMeanSeedBudgetKeyCheck, decide_eq_true_eq] at h
  rcases h with ⟨hi, hc, _, _, _, hk⟩
  simpa only [hc, hk, lowMeanFiberCertificate] using lowMean_budgetFamily_endpoints _ (lowMean_budgetAt_checked i hi)

theorem lowMean_seedBudget_slack (f : LowMeanFiberInput) (j : ℤ) (i kind : ℕ)
    (h : lowMeanSeedBudgetKeyCheck f j i kind = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanBudgetAt i).input.L) (lowMeanFractionReal (lowMeanBudgetAt i).input.H)) :
    lowMeanFractionReal f.zeta < lowMeanCertificateSlack (lowMeanFiberCertificate f) f.M j q := by
  simp only [lowMeanSeedBudgetKeyCheck, decide_eq_true_eq] at h
  rcases h with ⟨hi, hc, hM, hj, hz, _⟩
  simpa only [hc, hM, hj, hz, lowMeanFiberCertificate, lowMeanCertificateSlack] using
    lowMean_budgetFamily_slack _ (lowMean_budgetAt_checked i hi) hq

theorem lowMean_seedChoice_slack (f : LowMeanFiberInput) (w : LowMeanSeedBudgetChoice)
    (h : lowMeanSeedChoiceCheck f w = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanFiberCertificate f).l) (lowMeanFractionReal (lowMeanFiberCertificate f).h)) :
    lowMeanFractionReal f.zeta < lowMeanCertificateSlack (lowMeanFiberCertificate f) f.M w.j q := by
  simp only [lowMeanSeedChoiceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hm : w.mode ≤ 2 := h.1.1
  interval_cases hw : w.mode
  · simp only [show ¬ (0 : ℕ) = 1 by decide, show ¬ (0 : ℕ) = 2 by decide, ite_false] at h
    have he := lowMean_seedBudget_endpoints f w.j w.left 0 h.1.2
    simp only [show ¬ (0 : ℕ) = 2 by decide, show ¬ (0 : ℕ) = 1 by decide, ite_false] at he
    apply lowMean_seedBudget_slack f w.j w.left 0 h.1.2
    simpa only [he.1, he.2] using hq
  · simp only [show (1 : ℕ) = 1 by rfl, ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases lowMean_closed_halves hq with hql | hqr
    · have he := lowMean_seedBudget_endpoints f w.j w.left 1 h.1.2
      simp only [show ¬ (1 : ℕ) = 2 by decide, ite_false, ite_true] at he
      apply lowMean_seedBudget_slack f w.j w.left 1 h.1.2
      simpa only [he.1, he.2] using hql
    · have he := lowMean_seedBudget_endpoints f w.j w.right 2 h.2.1
      simp only [show ¬ (2 : ℕ) = 1 by decide, ite_false, ite_true] at he
      apply lowMean_seedBudget_slack f w.j w.right 2 h.2.1
      simpa only [he.1, he.2] using hqr
  · simp only [show ¬ (2 : ℕ) = 1 by decide, ite_false, ite_true] at h
    have he := lowMean_seedBudget_endpoints f w.j w.left 3 h.1.2
    simp only [show ¬ (3 : ℕ) = 2 by decide, show ¬ (3 : ℕ) = 1 by decide, ite_false] at he
    apply lowMean_seedBudget_slack f w.j w.left 3 h.1.2
    simpa only [he.1, he.2] using hq

theorem lowMean_fiber_budget_slack (b : LowMeanFiberBudgetInput)
    (h : lowMeanFiberBudgetCheck b = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanFiberCertificate b.fiber).l) (lowMeanFractionReal (lowMeanFiberCertificate b.fiber).h))
    {j : ℤ} (hj : j ∈ b.fiber.core) :
    lowMeanFractionReal b.fiber.zeta < lowMeanCertificateSlack (lowMeanFiberCertificate b.fiber) b.fiber.M j q := by
  simp only [lowMeanFiberBudgetCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hjmap : j ∈ b.positions.map LowMeanSeedBudgetChoice.j := by rw [h.1]; exact hj
  obtain ⟨w, hw, hjw⟩ := List.mem_map.mp hjmap
  have hs := lowMean_seedChoice_slack b.fiber w (List.all_eq_true.mp h.2 w hw) hq
  simpa only [hjw] using hs

theorem lowMean_fiber_seed (b : LowMeanFiberBudgetInput)
    (hcore : lowMeanFiberCheck b.fiber = true) (hbudget : lowMeanFiberBudgetCheck b = true)
    {q : ℝ} (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanFiberCertificate b.fiber).l) (lowMeanFractionReal (lowMeanFiberCertificate b.fiber).h)) (j : ℤ) :
    lowMeanFractionReal b.fiber.zeta ≤ lowMeanCertificateSlack (lowMeanFiberCertificate b.fiber) b.fiber.M j q := by
  classical
  by_cases hj : j ∈ lowMeanFiberCore b.fiber
  · exact (lowMean_fiber_budget_slack b hbudget hq ((lowMean_fiber_core_exact _ hcore j).mp hj)).le
  · have hm := hcore
    simp only [lowMeanFiberCheck, Bool.and_eq_true] at hm
    have hi := hm.1.1
    simp only [lowMeanFiberMetaCheck, Bool.and_eq_true, decide_eq_true_eq] at hi
    have hci : b.fiber.certificate - 1 < 28 := by omega
    have hs := lowMean_certificate_signs _ hci
    change 0 ≤ lowMeanFractionReal (lowMeanFiberCertificate b.fiber).wL ∧
      0 ≤ lowMeanFractionReal (lowMeanFiberCertificate b.fiber).wR ∧
      0 < lowMeanFractionReal (lowMeanFiberCertificate b.fiber).eta ∧ _ at hs
    obtain ⟨hl, hh, _⟩ := lowMean_fiber_probability_domain b.fiber hm.1.1
    exact lowMean_outside_core b.fiber.M j hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.1 hl hh hq hj

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_fiber_seed
