module

public import Mathlib

/-!
# The assigned endpoint and the literal integral in current Lemma 5.3

Version 2.13 of the manuscript, f4:lem2.2. The zero value is one, not the value of
Lean's totalized raw quotient. The integral is an ordinary real interval
integral. Its monotonicity includes the assigned zero endpoint.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set

noncomputable def messageRatio (u : ℝ) : ℝ :=
  if u = 0 then 1 else u / (-Real.log (1 - u))

theorem messageRatio_zero : messageRatio 0 = 1 := by
  simp [messageRatio]

theorem messageRatio_of_ne_zero {u : ℝ} (hu : u ≠ 0) :
    messageRatio u = u / (-Real.log (1 - u)) := by
  simp only [messageRatio, if_neg hu]

theorem power_kernel_continuous {u : ℝ} (hu : u < 1) :
    Continuous (fun t : ℝ => (1 - u) ^ t) := by
  have hb : 0 < 1 - u := by linarith
  simp_rw [Real.rpow_def_of_pos hb]
  fun_prop

theorem messageRatio_integral {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    messageRatio u = ∫ t : ℝ in (0 : ℝ)..1, (1 - u) ^ t := by
  by_cases hu : u = 0
  · subst u
    norm_num [messageRatio]
  have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  have hb : 0 < 1 - u := by linarith
  have hlog : Real.log (1 - u) ≠ 0 :=
    (Real.log_neg hb (by linarith)).ne
  rw [messageRatio_of_ne_zero hu]
  simp_rw [Real.rpow_def_of_pos hb]
  rw [intervalIntegral.integral_comp_mul_left _ hlog]
  simp only [mul_zero, mul_one, integral_exp, Real.exp_zero, Real.exp_log hb,
    smul_eq_mul]
  field_simp [hlog] <;> ring

theorem messageRatio_strictAntiOn : StrictAntiOn messageRatio (Ico 0 1) := by
  intro u hu v hv huv
  rw [messageRatio_integral hv.1 hv.2, messageRatio_integral hu.1 hu.2]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1)
    (power_kernel_continuous hv.2).continuousOn
    (power_kernel_continuous hu.2).continuousOn
  · intro t ht
    rw [Real.rpow_def_of_pos (show 0 < 1 - v by linarith [hv.2]),
      Real.rpow_def_of_pos (show 0 < 1 - u by linarith [hu.2])]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (by linarith [hv.2]) (by linarith)) ht.1.le
  · refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
    simp only [Real.rpow_one]
    linarith

theorem messageRatio_antitoneOn : AntitoneOn messageRatio (Ico 0 1) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with heq | hlt
  · subst v
    exact le_rfl
  · exact (messageRatio_strictAntiOn hu hv hlt).le

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_of_ne_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_of_ne_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.power_kernel_continuous
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.power_kernel_continuous
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_integral
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_integral
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_strictAntiOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_strictAntiOn
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_antitoneOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_antitoneOn
