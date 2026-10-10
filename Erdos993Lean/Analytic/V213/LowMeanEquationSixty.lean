module

public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed

/-!
Literal equation-60 consumer: the maximum of the whole-interval budget
and the minimum of both half budgets, using one canonical term list.
The seven extra anchors retain their separate single-anchor route.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_seedBudget_fields (f : LowMeanFiberInput) (j : ℤ) (i kind : ℕ)
    (h : lowMeanSeedBudgetKeyCheck f j i kind = true) :
    (lowMeanBudgetAt i).input.eta = (lowMeanFiberCertificate f).eta ∧
    (lowMeanBudgetAt i).input.xi = (lowMeanFiberCertificate f).xi ∧
    (lowMeanBudgetAt i).input.alpha = (lowMeanFiberCertificate f).alpha ∧
    (lowMeanBudgetAt i).input.beta = (lowMeanFiberCertificate f).beta ∧
    (lowMeanBudgetAt i).input.gamma = (lowMeanFiberCertificate f).gamma ∧
    (lowMeanBudgetAt i).input.m0 = (lowMeanFiberCertificate f).m0 := by
  simp only [lowMeanSeedBudgetKeyCheck, decide_eq_true_eq] at h
  have hc := lowMean_budgetAt_checked i h.1
  simp only [lowMeanBudgetFamilyCheck, Bool.and_eq_true] at hc
  have hr := hc.1.1.2
  simp only [lowMeanBudgetRecordCheck, Bool.and_eq_true] at hr
  have hi := hr.1.1
  simp only [lowMeanBudgetInputCheck, Bool.and_eq_true, decide_eq_true_eq] at hi
  have hf := hi.1.1.2
  simpa only [h.2.1, lowMeanFiberCertificate] using
    And.intro hf.1 (And.intro hf.2.1 (And.intro hf.2.2.1
      (And.intro hf.2.2.2.1 (And.intro hf.2.2.2.2.1 hf.2.2.2.2.2.1))))

theorem lowMean_seedBudget_R (f : LowMeanFiberInput) (j : ℤ) (i kind : ℕ)
    (h : lowMeanSeedBudgetKeyCheck f j i kind = true) (hn : kind ≠ 3) :
    (1 / 50000 : ℝ) <
      lowMeanBestBudget (lowMeanBudgetInputTerms (lowMeanBudgetAt i).input) f.M j
        (lowMeanFractionReal (lowMeanFiberCertificate f).eta) (lowMeanFractionReal (lowMeanFiberCertificate f).xi)
        (lowMeanFractionReal (lowMeanFiberCertificate f).alpha) (lowMeanFractionReal (lowMeanFiberCertificate f).beta)
        (lowMeanFractionReal (lowMeanFiberCertificate f).gamma) (lowMeanFractionReal (lowMeanFiberCertificate f).m0)
        (lowMeanFractionReal f.zeta)
        (if kind = 2 then (lowMeanFractionReal (lowMeanFiberCertificate f).l + lowMeanFractionReal (lowMeanFiberCertificate f).h) / 2 else lowMeanFractionReal (lowMeanFiberCertificate f).l)
        (if kind = 1 then (lowMeanFractionReal (lowMeanFiberCertificate f).l + lowMeanFractionReal (lowMeanFiberCertificate f).h) / 2 else lowMeanFractionReal (lowMeanFiberCertificate f).h) := by
  have hf := lowMean_seedBudget_fields f j i kind h
  have he := lowMean_seedBudget_endpoints f j i kind h
  simp only [lowMeanSeedBudgetKeyCheck, decide_eq_true_eq] at h
  rcases h with ⟨hi, _, hM, hj, hz, hk⟩
  have hp := lowMean_budgetFamily_R (lowMeanBudgetAt i) (lowMean_budgetAt_checked i hi) (by omega)
  have hb : lowMeanFractionReal (1, 50000) = (1 / 50000 : ℝ) := by norm_num [lowMeanFractionReal]
  simpa only [lowMeanBudgetExpectedBound, hk, hn, ite_false, hb,
    hM, hj, hz, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2, he.1, he.2] using hp

noncomputable def lowMeanPositionR (f : LowMeanFiberInput) (w : LowMeanSeedBudgetChoice) (L H : ℝ) : ℝ :=
  let c := lowMeanFiberCertificate f
  lowMeanBestBudget (lowMeanBudgetInputTerms (lowMeanBudgetAt w.left).input) f.M w.j
    (lowMeanFractionReal c.eta) (lowMeanFractionReal c.xi) (lowMeanFractionReal c.alpha)
    (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
    (lowMeanFractionReal f.zeta) L H

theorem lowMean_seedChoice_eq60 (f : LowMeanFiberInput) (w : LowMeanSeedBudgetChoice)
    (h : lowMeanSeedChoiceCheck f w = true) (hn : w.mode ≠ 2) :
    let l := lowMeanFractionReal (lowMeanFiberCertificate f).l
    let h := lowMeanFractionReal (lowMeanFiberCertificate f).h
    (1 / 50000 : ℝ) < max (lowMeanPositionR f w l h)
      (min (lowMeanPositionR f w l ((l + h) / 2)) (lowMeanPositionR f w ((l + h) / 2) h)) := by
  dsimp only
  simp only [lowMeanSeedChoiceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hm : w.mode ≤ 2 := h.1.1
  interval_cases hw : w.mode
  · simp only [show ¬ (0 : ℕ) = 1 by decide, show ¬ (0 : ℕ) = 2 by decide, ite_false] at h
    have hp := lowMean_seedBudget_R f w.j w.left 0 h.1.2 (by decide)
    simp only [show ¬ (0 : ℕ) = 2 by decide, show ¬ (0 : ℕ) = 1 by decide, ite_false] at hp
    exact lt_of_lt_of_le hp (le_max_left _ _)
  · simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := lowMean_seedBudget_R f w.j w.left 1 h.1.2 (by decide)
    have hr := lowMean_seedBudget_R f w.j w.right 2 h.2.1 (by decide)
    simp only [show ¬ (1 : ℕ) = 2 by decide, show ¬ (2 : ℕ) = 1 by decide, ite_true, ite_false] at hl hr
    simp only [lowMeanBudgetInputTerms, h.2.2] at hr
    exact lt_of_lt_of_le (lt_min hl hr) (le_max_right _ _)
  · exact (hn rfl).elim

theorem lowMean_seedChoice_special_minimum (f : LowMeanFiberInput) (w : LowMeanSeedBudgetChoice)
    (h : lowMeanSeedChoiceCheck f w = true) (hm : w.mode = 2) :
    let c := lowMeanFiberCertificate f
    let tau := lowMeanFractionReal (lowMeanSpecialBudgetTau f.M w.j)
    lowMeanFractionReal (lowMeanSpecialBudgetBound f.M w.j) <
      lowMeanBudgetMinimumAt (lowMeanBudgetInputTerms (lowMeanBudgetAt w.left).input) f.M w.j
        (lowMeanFractionReal c.eta) (lowMeanFractionReal c.xi) (lowMeanFractionReal c.alpha)
        (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
        (lowMeanFractionReal f.zeta) (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) tau ∧
      tau ∈ Set.Icc (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) := by
  dsimp only
  simp only [lowMeanSeedChoiceCheck, hm, Bool.and_eq_true, decide_eq_true_eq,
    show ¬ (2 : ℕ) = 1 by decide, ite_false, ite_true] at h
  have hk := h.1.2
  have hf := lowMean_seedBudget_fields f w.j w.left 3 hk
  have he := lowMean_seedBudget_endpoints f w.j w.left 3 hk
  simp only [show ¬ (3 : ℕ) = 2 by decide, show ¬ (3 : ℕ) = 1 by decide, ite_false] at he
  simp only [lowMeanSeedBudgetKeyCheck, decide_eq_true_eq] at hk
  rcases hk with ⟨hi, _, hM, hj, hz, hkind⟩
  have hc := lowMean_budgetAt_checked w.left hi
  have hp := lowMean_budgetFamily_minimum _ hc
  simp only [lowMeanBudgetFamilyCheck, Bool.and_eq_true, hkind, ite_true, decide_eq_true_eq] at hc
  have htau := hc.2
  have hr := hc.1.1.2
  simp only [lowMeanBudgetRecordCheck, Bool.and_eq_true] at hr
  have hd := (lowMean_budgetInput_domain _ _ hr.1.1).2.2.2
  constructor
  · simpa only [lowMeanBudgetExpectedBound, hkind, ite_true, hM, hj, hz,
      hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2, he.1, he.2, htau] using hp
  · simpa only [htau, hM, hj, he.1, he.2] using hd

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_seedChoice_eq60
