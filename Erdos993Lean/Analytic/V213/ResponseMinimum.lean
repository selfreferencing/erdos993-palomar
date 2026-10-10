module

public import Mathlib

/-!
Current printed Lemma 5.20 (f4:lem4.2).
The response quadratic and minimum are literal formulas. The coefficient d is
unrestricted: only delta > 0, J > 0 and delta + d*J > 0 are used. The leaf
convention at J=0 evaluates y=h and is not an unconstrained minimum assertion.

No numerical record family or reduction oracle.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

noncomputable def responseQuadratic (a b c d delta h J y : ℝ) : ℝ :=
  a + b*h + c*y + d*y^2 + delta*(h-y)^2/J

noncomputable def responseMinimum (a b c d delta h J : ℝ) : ℝ :=
  a + (b+c)*h + d*h^2 - J*(c+2*d*h)^2/(4*(delta+d*J))

noncomputable def responseMinimizer (c d delta h J : ℝ) : ℝ :=
  (2*delta*h-c*J)/(2*(delta+d*J))

theorem response_square (a b c d delta h J y : ℝ)
    (hJ : 0 < J) (hG : 0 < delta+d*J) :
    responseQuadratic a b c d delta h J y =
      ((delta+d*J)/J)*(y-responseMinimizer c d delta h J)^2 +
      responseMinimum a b c d delta h J := by
  unfold responseQuadratic responseMinimizer responseMinimum
  field_simp [ne_of_gt hJ, ne_of_gt hG]
  <;> ring

theorem responseMinimum_le (a b c d delta h J y : ℝ)
    (hdelta : 0 < delta) (hJ : 0 < J) (hG : 0 < delta+d*J) :
    responseMinimum a b c d delta h J ≤ responseQuadratic a b c d delta h J y := by
  rw [response_square a b c d delta h J y hJ hG]
  exact le_add_of_nonneg_left (mul_nonneg (div_nonneg hG.le hJ.le) (sq_nonneg _))

theorem responseMinimum_attained (a b c d delta h J : ℝ)
    (hdelta : 0 < delta) (hJ : 0 < J) (hG : 0 < delta+d*J) :
    responseQuadratic a b c d delta h J (responseMinimizer c d delta h J) =
      responseMinimum a b c d delta h J := by
  rw [response_square a b c d delta h J (responseMinimizer c d delta h J) hJ hG]
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]

theorem response_minimum (a b c d delta h J : ℝ)
    (hdelta : 0 < delta) (hJ : 0 < J) (hG : 0 < delta+d*J) :
    (∀ y : ℝ, responseMinimum a b c d delta h J ≤ responseQuadratic a b c d delta h J y) ∧
    responseQuadratic a b c d delta h J (responseMinimizer c d delta h J) =
      responseMinimum a b c d delta h J :=
  ⟨fun y => responseMinimum_le a b c d delta h J y hdelta hJ hG,
    responseMinimum_attained a b c d delta h J hdelta hJ hG⟩

theorem responseMinimum_deriv_h_core (a b c d delta h J : ℝ)
    (hG : delta+d*J ≠ 0) :
    HasDerivAt (fun x : ℝ => responseMinimum a b c d delta x J)
      (b+delta*(c+2*d*h)/(delta+d*J)) h := by
  have hc : HasDerivAt (fun x : ℝ => c+2*d*x) (2*d) h := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id h).const_mul (2*d)).const_add c
  have hp := ((hasDerivAt_const h a).add
    ((hasDerivAt_id h).const_mul (b+c))).add
    (((hasDerivAt_id h).fun_pow 2).const_mul d)
  have hn := ((hc.fun_pow 2).const_mul J).div_const (4*(delta+d*J))
  convert hp.sub hn using 1 <;> (try funext x) <;>
    (try dsimp [responseMinimum]) <;>
    (try simp only [id_eq, Nat.reduceSub, zero_add, mul_one, one_mul, pow_one]) <;>
    (try ring)
  <;> field_simp [hG] <;> ring

theorem responseMinimum_deriv_J_core (a b c d delta h J : ℝ)
    (hG : delta+d*J ≠ 0) :
    HasDerivAt (fun x : ℝ => responseMinimum a b c d delta h x)
      (-delta*(c+2*d*h)^2/(4*(delta+d*J)^2)) J := by
  have hn := (hasDerivAt_id J).mul_const ((c+2*d*h)^2)
  have hd := (((hasDerivAt_id J).const_mul d).const_add delta).const_mul 4
  have hd0 : 4*(delta+d*J) ≠ 0 := mul_ne_zero (by norm_num) hG
  have hq := hn.div hd hd0
  convert (hasDerivAt_const J (a+(b+c)*h+d*h^2)).sub hq using 1 <;>
    first
    | (funext x <;> (try dsimp [responseMinimum]) <;>
        (try simp only [id_eq, mul_one, one_mul, zero_sub]) <;> ring)
    | (simp only [id_eq, mul_one, one_mul, zero_sub]
       field_simp [hG]
       ring)

theorem responseMinimum_derivatives (a b c d delta h J : ℝ)
    (hdelta : 0 < delta) (hJ : 0 < J) (hG : 0 < delta+d*J) :
    HasDerivAt (fun x : ℝ => responseMinimum a b c d delta x J)
      (b+delta*(c+2*d*h)/(delta+d*J)) h ∧
    HasDerivAt (fun x : ℝ => responseMinimum a b c d delta h x)
      (-delta*(c+2*d*h)^2/(4*(delta+d*J)^2)) J ∧
    -delta*(c+2*d*h)^2/(4*(delta+d*J)^2) ≤ 0 := by
  refine ⟨responseMinimum_deriv_h_core a b c d delta h J (ne_of_gt hG),
    responseMinimum_deriv_J_core a b c d delta h J (ne_of_gt hG), ?_⟩
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdelta.le) (sq_nonneg _))
    (by positivity)

theorem responseMinimum_zero (a b c d delta h : ℝ) :
    responseMinimum a b c d delta h 0 = a+(b+c)*h+d*h^2 := by
  simp [responseMinimum]

theorem response_leaf_convention (a b c d delta h : ℝ) :
    responseQuadratic a b c d delta h 0 h = responseMinimum a b c d delta h 0 := by
  simp only [responseQuadratic, responseMinimum, sub_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_div, add_zero, zero_mul, sub_zero]
  ring

theorem responseMinimum_continuousAt_zero (a b c d delta h : ℝ)
    (hdelta : 0 < delta) :
    ContinuousAt (fun J : ℝ => responseMinimum a b c d delta h J) 0 := by
  exact (responseMinimum_deriv_J_core a b c d delta h 0
    (by simpa only [mul_zero, add_zero] using ne_of_gt hdelta)).continuousAt

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.responseQuadratic
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseQuadratic
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimizer
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimizer
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_square
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_square
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_attained
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_attained
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_minimum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_minimum
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_deriv_h_core
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_deriv_h_core
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_deriv_J_core
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_deriv_J_core
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_derivatives
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_derivatives
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_leaf_convention
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_leaf_convention
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_continuousAt_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseMinimum_continuousAt_zero
