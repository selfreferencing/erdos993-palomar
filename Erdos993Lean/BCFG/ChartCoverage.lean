module

public import Erdos993Lean.BCFG.ChartGeometry

/-! Closed inverse charts and their overlap with the original small-vacancy tails.
These geometric statements make no source, determinant or payment assertion. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem exists_light_parameter {lam omega : ℝ} (hl : 0 < lam)
    (hw0 : 1/(1+lam) ≤ omega) (hw1 : omega ≤ 1) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ lightOmega lam x = omega := by
  have hd : 0 < 1+lam := by linarith
  have hq := (q_bounds hl).1
  have hleft : 1-q lam ≤ omega := by
    simpa only [one_sub_q lam hd.ne'] using hw0
  refine ⟨(1-omega)/q lam, div_nonneg (by linarith) hq.le, ?_, ?_⟩
  · apply (div_le_iff₀ hq).2
    nlinarith
  · dsimp [lightOmega]
    field_simp [hq.ne']
    ring

theorem exists_heavy_parameter {r : AnalyticRow} {lam omega : ℝ}
    (hl : 0 < lam)
    (hw0 : (1/2 : ℝ)^(heavyExponent r)/(1+lam) ≤ omega)
    (hw1 : omega ≤ 1/(1+lam)) :
    ∃ v : ℝ, 1/2 ≤ v ∧ v ≤ 1 ∧ heavyOmega r lam v = omega := by
  have hd : 0 < 1+lam := by linarith
  have hlo : (1/2 : ℝ)^(heavyExponent r) ≤ (1+lam)*omega := by
    simpa only [mul_comm] using (div_le_iff₀ hd).1 hw0
  have hhi : (1+lam)*omega ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ hd).1 hw1
  have hc : ContinuousOn (fun v : ℝ => v^(heavyExponent r)) (Set.Icc (1/2) 1) :=
    (continuous_id.pow (heavyExponent r)).continuousOn
  have hm : (1+lam)*omega ∈ Set.Icc
      ((1/2 : ℝ)^(heavyExponent r)) ((1 : ℝ)^(heavyExponent r)) :=
    ⟨hlo, by simpa only [one_pow] using hhi⟩
  obtain ⟨v, hv, heq⟩ := (intermediate_value_Icc (by norm_num : (1/2 : ℝ) ≤ 1) hc) hm
  refine ⟨v, hv.1, hv.2, ?_⟩
  unfold heavyOmega
  apply (div_eq_iff hd.ne').2
  simpa only [mul_comm] using heq

theorem exists_heavy_parameter_above_tail {r : AnalyticRow} {lam omega : ℝ}
    (hl : 0 < lam) (hw : 0 < omega)
    (hcut : (1/2 : ℝ)^(heavyExponent r) ≤ omega)
    (hheavy : omega ≤ 1/(1+lam)) :
    ∃ v : ℝ, 1/2 ≤ v ∧ v ≤ 1 ∧ heavyOmega r lam v = omega := by
  apply exists_heavy_parameter hl ?_ hheavy
  apply (div_le_iff₀ (by linarith : 0 < 1+lam)).2
  nlinarith [mul_nonneg hw.le hl.le]

theorem chart_or_tail_coverage {r : AnalyticRow} {lam omega : ℝ}
    (hrow : InRow r lam) (hw : 0 < omega) (hw1 : omega ≤ 1) :
    (∃ x : ℝ, LightDomain r lam x ∧ lightOmega lam x = omega) ∨
    omega ≤ (1/2 : ℝ)^(heavyExponent r) ∨
    (∃ v : ℝ, HeavyDomain r lam v ∧ heavyOmega r lam v = omega) := by
  have hl := activity_pos hrow
  by_cases hlight : 1/(1+lam) ≤ omega
  · obtain ⟨x, hx0, hx1, heq⟩ := exists_light_parameter hl hlight hw1
    exact Or.inl ⟨x, ⟨hrow, hx0, hx1⟩, heq⟩
  · by_cases htail : omega ≤ (1/2 : ℝ)^(heavyExponent r)
    · exact Or.inr (Or.inl htail)
    · obtain ⟨v, hv0, hv1, heq⟩ := exists_heavy_parameter_above_tail hl hw
        (le_of_not_ge htail) (le_of_not_ge hlight)
      exact Or.inr (Or.inr ⟨v, ⟨hrow, hv0, hv1⟩, heq⟩)

theorem tail_cutoff_BC :
    (1/2 : ℝ)^(heavyExponent .B) = 1/16 ∧
    (1/2 : ℝ)^(heavyExponent .C) = 1/16 := by
  norm_num [heavyExponent]

theorem tail_cutoff_FG :
    (1/2 : ℝ)^(heavyExponent .F) = 1/64 ∧
    (1/2 : ℝ)^(heavyExponent .G) = 1/64 := by
  norm_num [heavyExponent]

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.exists_light_parameter
#print axioms Erdos993Lean.BCFG.Analytic.exists_light_parameter
#check Erdos993Lean.BCFG.Analytic.exists_heavy_parameter
#print axioms Erdos993Lean.BCFG.Analytic.exists_heavy_parameter
#check Erdos993Lean.BCFG.Analytic.exists_heavy_parameter_above_tail
#print axioms Erdos993Lean.BCFG.Analytic.exists_heavy_parameter_above_tail
#check Erdos993Lean.BCFG.Analytic.chart_or_tail_coverage
#print axioms Erdos993Lean.BCFG.Analytic.chart_or_tail_coverage
#check Erdos993Lean.BCFG.Analytic.tail_cutoff_BC
#print axioms Erdos993Lean.BCFG.Analytic.tail_cutoff_BC
#check Erdos993Lean.BCFG.Analytic.tail_cutoff_FG
#print axioms Erdos993Lean.BCFG.Analytic.tail_cutoff_FG
