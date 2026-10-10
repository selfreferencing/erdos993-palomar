module

public import Erdos993Lean.BCFG.ChartGeometry

/-! Actual feasible-rho path infrastructure for the heavy continuity consumer.
These lemmas prove domain preservation; they do not assume or claim continuity
of the diagonal or positivity away from the already-treated base. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem rhoZero_mono_omega {lam omega1 omega2 : ℝ}
    (hl : 0 < lam) (hw1 : 0 < omega1) (hw2 : 0 < omega2) (hw : omega1 ≤ omega2) :
    rhoZero lam omega1 ≤ rhoZero lam omega2 := by
  have hd1 : 0 < 1+lam+lam*omega1 := by positivity
  have hd2 : 0 < 1+lam+lam*omega2 := by positivity
  unfold rhoZero
  apply (div_le_div_iff₀ hd1 hd2).2
  have hm := mul_nonneg (sq_nonneg lam) (sub_nonneg.mpr hw)
  nlinarith only [hm]

theorem heavyOmega_mono {r : AnalyticRow} {lam w v : ℝ}
    (hl : 0 < lam) (hw : 0 ≤ w) (hwv : w ≤ v) :
    heavyOmega r lam w ≤ heavyOmega r lam v := by
  unfold heavyOmega
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hw hwv (heavyExponent r))
    (show 0 ≤ 1+lam by linarith)

theorem heavyOmega_lt_one_onDomain {r : AnalyticRow} {lam v : ℝ}
    (h : HeavyDomain r lam v) : heavyOmega r lam v < 1 := by
  have hl := activity_pos h.1
  have hhalf : (0 : ℝ) < 1/2 := div_pos zero_lt_one
    (by exact_mod_cast (by decide +kernel : 0 < (2 : ℕ)))
  have hv : 0 ≤ v := (hhalf.trans_le h.2.1).le
  unfold heavyOmega
  apply (div_lt_one (show 0 < 1+lam by linarith)).2
  exact (pow_le_one₀ hv h.2.2).trans_lt (show (1 : ℝ) < 1+lam by linarith)

/-- Holding actual rho fixed preserves feasibility throughout the path from 1/2. -/
theorem heavy_feasible_along_path {r : AnalyticRow} {lam v w rho : ℝ}
    (h : HeavyDomain r lam v) (hw0 : 1/2 ≤ w) (hwv : w ≤ v)
    (hr : rhoZero lam (heavyOmega r lam v) ≤ rho) (hr1 : rho ≤ 1) :
    HeavyDomain r lam w ∧ Feasible r lam (heavyOmega r lam w) rho := by
  have hl := activity_pos h.1
  have hhalf : (0 : ℝ) < 1/2 := div_pos zero_lt_one
    (by exact_mod_cast (by decide +kernel : 0 < (2 : ℕ)))
  have hw : 0 < w := hhalf.trans_le hw0
  have hv : 0 < v := hhalf.trans_le h.2.1
  have hdomain : HeavyDomain r lam w := ⟨h.1,hw0,hwv.trans h.2.2⟩
  have homega := heavyOmega_mono (r := r) hl hw.le hwv
  have hwb := heavyOmega_pos (r := r) hl hw
  have hvb := heavyOmega_pos (r := r) hl hv
  have hrho := (rhoZero_mono_omega hl hwb hvb homega).trans hr
  exact ⟨hdomain,h.1,hwb,(heavyOmega_lt_one_onDomain hdomain).le,hrho,hr1⟩

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.rhoZero_mono_omega
#print axioms Erdos993Lean.BCFG.Analytic.rhoZero_mono_omega
#check Erdos993Lean.BCFG.Analytic.heavyOmega_mono
#print axioms Erdos993Lean.BCFG.Analytic.heavyOmega_mono
#check Erdos993Lean.BCFG.Analytic.heavyOmega_lt_one_onDomain
#print axioms Erdos993Lean.BCFG.Analytic.heavyOmega_lt_one_onDomain
#check Erdos993Lean.BCFG.Analytic.heavy_feasible_along_path
#print axioms Erdos993Lean.BCFG.Analytic.heavy_feasible_along_path
