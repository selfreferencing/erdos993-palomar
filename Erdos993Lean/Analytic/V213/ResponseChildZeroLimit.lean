module

public import Erdos993Lean.Analytic.V213.ResponseChildTangents
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
Right continuity of the actual child curve at its assigned zero endpoint.
The logarithmic singularity is absorbed by the continuous function u * log u.
No endpoint value or continuity premise is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set

theorem childJ_log_product {lam u : ℝ} (hl : 0 < lam)
    (hu : 0 ≤ u) (hu1 : u < 1) :
    childJ lam u = messageRatio u *
      (u * Real.log lam + u * Real.log (1-u) - u * Real.log u) := by
  by_cases hz : u = 0
  · subst u
    simp [childJ]
  · have hp : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have hsub : 0 < 1-u := by linarith
    unfold childJ childLog
    rw [Real.log_div (mul_pos hl hsub).ne' hp.ne',
      Real.log_mul hl.ne' hsub.ne']
    ring

/-- The assigned child endpoint J(0)=0 is continuous from the right. -/
theorem childJ_continuousWithinAt_zero {lam : ℝ} (hl : 0 < lam) :
    ContinuousWithinAt (childJ lam) (Ici 0) 0 := by
  have hlog : ContinuousAt (fun u : ℝ => Real.log (1-u)) 0 :=
    ((continuous_const.sub continuous_id).continuousAt).log (by norm_num)
  have hcore : ContinuousAt
      (fun u : ℝ => u * Real.log lam + u * Real.log (1-u) -
        u * Real.log u) 0 :=
    ((continuous_id.continuousAt.mul continuous_const.continuousAt).add
      (continuous_id.continuousAt.mul hlog)).sub Real.continuous_mul_log.continuousAt
  have hc : ContinuousWithinAt (childJ lam) (Ico 0 1) 0 := by
    apply (messageRatio_continuousWithinAt_zero.mul hcore.continuousWithinAt).congr
    · intro u hu
      exact childJ_log_product hl hu.1 hu.2
    · exact childJ_log_product hl le_rfl (by norm_num)
  exact (continuousWithinAt_Ico_iff_Ici (show (0 : ℝ) < 1 by norm_num)).mp hc

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.childJ_log_product
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childJ_log_product
#check Erdos993Lean.Analytic.V213.VarianceResponse.childJ_continuousWithinAt_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childJ_continuousWithinAt_zero
#check Real.continuous_mul_log
#print axioms Real.continuous_mul_log
