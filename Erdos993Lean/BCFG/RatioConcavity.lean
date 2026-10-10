module

public import Erdos993Lean.Analytic.V213.ResponseRatioIntegral

/-! The concavity used by the BCFG mass constants.
It uses the exact integral representation including the assigned endpoint.
No numerical endpoint logarithm gate is assumed to be proved here. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic

open Set MeasureTheory
open Erdos993Lean.Analytic.V213.VarianceResponse

/-- The printed mass ratio is concave on its full assigned domain [0,1). -/
theorem messageRatio_concaveOn : ConcaveOn ℝ (Ico 0 1) messageRatio := by
  refine ⟨convex_Ico 0 1,?_⟩
  intro u hu v hv a b ha hb hab
  simp only [smul_eq_mul]
  have hm : a*u+b*v ∈ Ico (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using
      (convex_Ico (0 : ℝ) 1 : Convex ℝ (Ico (0 : ℝ) 1)) hu hv ha hb hab
  have hiu : IntervalIntegrable (fun t : ℝ => a*(1-u)^t) volume 0 1 :=
    ((power_kernel_continuous hu.2).const_mul a).intervalIntegrable 0 1
  have hiv : IntervalIntegrable (fun t : ℝ => b*(1-v)^t) volume 0 1 :=
    ((power_kernel_continuous hv.2).const_mul b).intervalIntegrable 0 1
  have him : IntervalIntegrable (fun t : ℝ => (1-(a*u+b*v))^t) volume 0 1 :=
    (power_kernel_continuous hm.2).intervalIntegrable 0 1
  rw [messageRatio_integral hu.1 hu.2,messageRatio_integral hv.1 hv.2,
    messageRatio_integral hm.1 hm.2]
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hiu hiv]
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) (hiu.add hiv) him
  intro t ht
  have hc := (Real.concaveOn_rpow ht.1 ht.2).2
    (show 1-u ∈ Ici (0 : ℝ) from by change 0 ≤ 1-u; linarith [hu.2])
    (show 1-v ∈ Ici (0 : ℝ) from by change 0 ≤ 1-v; linarith [hv.2]) ha hb hab
  have he : a*(1-u)+b*(1-v) = 1-(a*u+b*v) := by nlinarith [hab]
  simpa only [smul_eq_mul,he] using hc

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.messageRatio_concaveOn
#print axioms Erdos993Lean.BCFG.Analytic.messageRatio_concaveOn
#check Real.concaveOn_rpow
#print axioms Real.concaveOn_rpow
