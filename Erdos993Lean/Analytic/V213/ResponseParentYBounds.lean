module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightDefs

/-! Current T7 Section5.4: the four uniform parent log-mass bounds.
The rational third-order upper remainder is proved by a derivative comparison;
only literal row endpoints are substituted, inside Lean. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows
open Set FreeCountVariance.Envelopes

noncomputable def parentLogUpper (H : ℝ) : ℝ := H+H^2/2+H^3/(3*(1-H))

theorem parentLogUpper_gap_hasDerivAt {H : ℝ} (hH1 : H < 1) :
    HasDerivAt (fun x => parentLogUpper x-scalarLog x)
      (H^3/(3*(1-H)^2)) H := by
  have hn : 1-H ≠ 0 := by linarith
  have hd : 3*(1-H) ≠ 0 := mul_ne_zero (by norm_num) hn
  convert (((hasDerivAt_id H).add ((hasDerivAt_pow 2 H).div_const 2)).add
    ((hasDerivAt_pow 3 H).div
      (((hasDerivAt_id H).const_sub 1).const_mul 3) hd)).sub
    (hasDerivAt_scalarLog hH1) using 1
  all_goals
    first
    | (funext x <;> (try dsimp [parentLogUpper]) <;>
        (try simp only [id_eq, mul_one, one_mul]) <;> ring)
    | ((try simp only [id_eq, Nat.reduceSub, pow_one, mul_one, one_mul]) <;>
        field_simp [hn] <;> ring)

theorem parentY_le_logUpper {H : ℝ} (hH : 0 ≤ H) (hH1 : H < 1) :
    parentY H ≤ parentLogUpper H := by
  have hh := zero_le_value_of_nonneg_deriv
    (f := fun x => parentLogUpper x-scalarLog x)
    (f' := fun x => x^3/(3*(1-x)^2)) hH
    (by norm_num [parentLogUpper,scalarLog])
    (fun x hx => parentLogUpper_gap_hasDerivAt (hx.2.trans_lt hH1))
    (fun x hx => by have hx0 := hx.1; positivity)
  change scalarLog H ≤ parentLogUpper H
  linarith

theorem parentY_upper_from_cap {H K : ℝ} (hH : 0 ≤ H)
    (hcap : H ≤ K) (hK : K < 1) : parentY H ≤ parentLogUpper K := by
  have hK0 : 0 ≤ K := hH.trans hcap
  have h2 : H^2 ≤ K^2 := pow_le_pow_left₀ hH hcap 2
  have h3 : H^3 ≤ K^3 := pow_le_pow_left₀ hH hcap 3
  have hterm : H^3/(3*(1-H)) ≤ K^3/(3*(1-K)) :=
    div_le_div₀ (pow_nonneg hK0 _) h3 (by linarith) (by linarith)
  have hh := parentY_le_logUpper hH (hcap.trans_lt hK)
  unfold parentLogUpper at *
  linarith

theorem half_child_cap_from_activity {lam M H : ℝ} (hl : 0 < lam)
    (hM : lam ≤ M) (hH : H ≤ childQ lam/2) :
    H ≤ (M/(1+M))/2 := by
  have hd : 0 < 1+lam := by linarith
  have hMd : 0 < 1+M := by linarith
  have hq : childQ lam ≤ M/(1+M) := by
    unfold childQ
    apply (div_le_div_iff₀ hd hMd).2
    nlinarith
  linarith

theorem parentY_D_upper {lam H : ℝ} (hrow : inRow 0 lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) : parentY H < 1/3 := by
  have hb : 4/5 ≤ lam ∧ lam ≤ 13/10 := by simpa [inRow,rowData] using hrow
  have hc := half_child_cap_from_activity (by linarith : 0 < lam) hb.2 hcap
  norm_num at hc
  have hy := parentY_upper_from_cap hH.le hc (by norm_num)
  norm_num [parentLogUpper] at hy
  linarith

theorem parentY_E1_upper {lam H : ℝ} (hrow : inRow 1 lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) : parentY H < 9/25 := by
  have hb : 13/10 ≤ lam ∧ lam ≤ 29/20 := by simpa [inRow,rowData] using hrow
  have hc := half_child_cap_from_activity (by linarith : 0 < lam) hb.2 hcap
  norm_num at hc
  have hy := parentY_upper_from_cap hH.le hc (by norm_num)
  norm_num [parentLogUpper] at hy
  linarith

theorem parentY_E2_upper {lam H : ℝ} (hrow : inRow 2 lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) : parentY H < 3/8 := by
  have hb : 29/20 ≤ lam ∧ lam ≤ 8/5 := by simpa [inRow,rowData] using hrow
  have hc := half_child_cap_from_activity (by linarith : 0 < lam) hb.2 hcap
  norm_num at hc
  have hy := parentY_upper_from_cap hH.le hc (by norm_num)
  norm_num [parentLogUpper] at hy
  linarith

theorem parentY_H_upper {lam H : ℝ} (hrow : inRow 3 lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) : parentY H < 7/16 := by
  have hb : 7/4 ≤ lam ∧ lam ≤ 7/3 := by simpa [inRow,rowData] using hrow
  have hc := half_child_cap_from_activity (by linarith : 0 < lam) hb.2 hcap
  norm_num at hc
  have hy := parentY_upper_from_cap hH.le hc (by norm_num)
  norm_num [parentLogUpper] at hy
  linarith

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLogUpper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLogUpper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLogUpper_gap_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLogUpper_gap_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_le_logUpper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_le_logUpper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_upper_from_cap
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_upper_from_cap
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_child_cap_from_activity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_child_cap_from_activity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_D_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_D_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_E1_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_E1_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_E2_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_E2_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_H_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY_H_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.zero_le_value_of_nonneg_deriv
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.zero_le_value_of_nonneg_deriv
