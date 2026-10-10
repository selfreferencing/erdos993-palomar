module

public import Erdos993Lean.Analytic.V213.ResponseMinimum
public import Erdos993Lean.Analytic.V213.ResponseHalfLightChild

/-! Current Lemma 5.25: retain the positive first-derivative term.
The child curve is actual, and its derivative is computed here. The only
remaining signs are the literal positive parent coefficients of that lemma;
the final row theorem must discharge those signs, rather than assume it.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

noncomputable def minimumAlong (a b c d delta lam u : ℝ) : ℝ :=
  responseMinimum a b c d delta (messageRatio u) (childJ lam u)

noncomputable def minimumCurveDerivative (b c d delta lam u : ℝ) : ℝ :=
  let nu := delta*(c+2*d*messageRatio u)/(delta+d*childJ lam u)
  b+nu-childSlope lam u*nu^2/(4*delta)

theorem minimumAlong_hasDerivAt (a b c d delta : ℝ) {lam u : ℝ}
    (hl : 0 < lam) (hu : 0 < u) (hu1 : u < 1) (hdelta : delta ≠ 0)
    (hG : delta+d*childJ lam u ≠ 0) :
    HasDerivAt (minimumAlong a b c d delta lam)
      (minimumCurveDerivative b c d delta lam u*childHDeriv u) u := by
  have hh := messageRatio_hasDerivAt hu hu1
  have hj := childJ_hasDerivAt hl hu hu1
  have hr := (hh.const_mul (2*d)).const_add c
  have hg := ((hj.const_mul d).const_add delta).const_mul 4
  have hnum := hj.mul (hr.pow 2)
  have hp := ((hasDerivAt_const u a).add (hh.const_mul (b+c))).add ((hh.pow 2).const_mul d)
  convert hp.sub (hnum.div hg (mul_ne_zero (by norm_num) hG)) using 1 <;>
    first
    | (funext x <;> (try dsimp [minimumAlong,responseMinimum]) <;>
        (try simp only [id_eq,Nat.reduceSub,pow_one,zero_add,mul_one,one_mul]) <;> ring)
    | ((try dsimp [minimumCurveDerivative]) <;>
        (try simp only [id_eq,Nat.reduceSub,pow_one,zero_add,mul_one,one_mul]) <;>
        field_simp [hdelta,hG] <;> ring)

theorem minimumCurveDerivative_eq_ratio (a b c d delta : ℝ) {lam u : ℝ}
    (hl : 0 < lam) (hu : 0 < u) (hu1 : u < 1) (hdelta : delta ≠ 0)
    (hG : delta+d*childJ lam u ≠ 0) :
    deriv (minimumAlong a b c d delta lam) u / deriv messageRatio u =
      minimumCurveDerivative b c d delta lam u := by
  rw [(minimumAlong_hasDerivAt a b c d delta hl hu hu1 hdelta hG).deriv,
    (messageRatio_hasDerivAt hu hu1).deriv]
  exact mul_div_cancel_right₀ _ (childHDeriv_neg hu hu1).ne

theorem minimumCurveDerivative_gt_b_of_nonpos {b c d delta lam u : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) (hl : 0 < lam) (hu : 0 < u)
    (huh : u ≤ childQ lam/2) (hr : 0 < c+2*d*messageRatio u)
    (heta : childSlope lam u ≤ 0) : b < minimumCurveDerivative b c d delta lam u := by
  have hb := half_child_bounds hl hu huh
  have hJ := hb.2.2.2.1
  have hG : 0 < delta+d*childJ lam u := by positivity
  have hnu : 0 < delta*(c+2*d*messageRatio u)/(delta+d*childJ lam u) := by positivity
  have hn : childSlope lam u*(delta*(c+2*d*messageRatio u)/(delta+d*childJ lam u))^2/
      (4*delta) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg heta (sq_nonneg _)) (by positivity)
  dsimp [minimumCurveDerivative]
  linarith

private theorem concave_quadratic_average (b eta delta s t c R k : ℝ)
    (heta : 0 ≤ eta) (hdelta : 0 < delta) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s+t = 1) (hc : k ≤ b+c-eta*c^2/(4*delta))
    (hR : k ≤ b+R-eta*R^2/(4*delta)) :
    k ≤ b+(s*c+t*R)-eta*(s*c+t*R)^2/(4*delta) := by
  have hi : (b+(s*c+t*R)-eta*(s*c+t*R)^2/(4*delta))-
      (s*(b+c-eta*c^2/(4*delta))+t*(b+R-eta*R^2/(4*delta))) =
      eta*s*t*(c-R)^2/(4*delta) := by
    have htval : t = 1-s := by linarith
    rw [htval]
    field_simp [hdelta.ne']
    ring
  have hn : 0 ≤ eta*s*t*(c-R)^2/(4*delta) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hc hs
  have h2 := mul_le_mul_of_nonneg_left hR ht
  have hk := add_le_add h1 h2
  have hsumk : s*k+t*k = k := by rw [← add_mul,hst,one_mul]
  rw [hsumk] at hk
  linarith

theorem response_derivative_three_endpoints {b c d delta h J eta k : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) (hh : 0 < h) (hJ : 0 < J)
    (hr : 0 < c+2*d*h) (heta : 0 < eta) (heta1 : eta < 1)
    (hk0 : k ≤ b)
    (hkc : k ≤ b+max c 0-(max c 0)^2/(4*delta))
    (hkR : k ≤ b+2*delta*h/J-eta*(2*delta*h/J)^2/(4*delta)) :
    k ≤ b+delta*(c+2*d*h)/(delta+d*J)-
      eta*(delta*(c+2*d*h)/(delta+d*J))^2/(4*delta) := by
  have hG : 0 < delta+d*J := by positivity
  have hR : 0 < 2*delta*h/J := by positivity
  have hnu : 0 < delta*(c+2*d*h)/(delta+d*J) := by positivity
  by_cases hc : 0 ≤ c
  · have hsum : delta/(delta+d*J)+(d*J)/(delta+d*J) = 1 := by
      field_simp [hG.ne'] <;> ring
    have heq : delta/(delta+d*J)*c+(d*J)/(delta+d*J)*(2*delta*h/J) =
        delta*(c+2*d*h)/(delta+d*J) := by
      field_simp [hG.ne',hJ.ne'] <;> ring
    have hceta : k ≤ b+c-eta*c^2/(4*delta) := by
      rw [max_eq_left hc] at hkc
      have heta0 : 0 ≤ 1-eta := by linarith
      have hn : 0 ≤ (1-eta)*c^2/(4*delta) := by positivity
      have hi : b+c-eta*c^2/(4*delta) = b+c-c^2/(4*delta)+(1-eta)*c^2/(4*delta) := by ring
      linarith
    have h := concave_quadratic_average b eta delta (delta/(delta+d*J))
      ((d*J)/(delta+d*J)) c (2*delta*h/J) k heta.le hdelta
      (by positivity) (by positivity) hsum hceta hkR
    simpa only [heq] using h
  · have hnuR : delta*(c+2*d*h)/(delta+d*J) ≤ 2*delta*h/J := by
      apply (div_le_div_iff₀ hG hJ).2
      have hn := mul_nonpos_of_nonpos_of_nonneg (show c ≤ 0 by linarith) hJ.le
      nlinarith [mul_nonneg (show 0 ≤ 2*delta*h by positivity) hdelta.le,
        mul_nonneg hdelta.le (neg_nonneg.mpr hn)]
    let nu := delta*(c+2*d*h)/(delta+d*J)
    let R := 2*delta*h/J
    have hv0 : 0 ≤ nu/R := div_nonneg hnu.le hR.le
    have hv1 : nu/R ≤ 1 := (div_le_one hR).2 hnuR
    have heq : (1-nu/R)*0+(nu/R)*R = nu := by
      rw [mul_zero,zero_add,div_mul_cancel₀ _ hR.ne']
    have h := concave_quadratic_average b eta delta (1-nu/R) (nu/R) 0 R k
      heta.le hdelta (by linarith) hv0 (by ring) (by simpa using hk0) hkR
    simpa only [heq] using h

/-- The literal minimum of the three quantities in (9), on the actual child curve. -/
theorem minimumCurveDerivative_lower {b c d delta lam u : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) (hb : 0 < b)
    (hl : 0 < lam) (hu : 0 < u) (huh : u ≤ childQ lam/2)
    (hr : 0 < c+2*d*messageRatio u) (heta : 0 < childSlope lam u)
    (heta1 : childSlope lam u < 1) :
    min b (min (b+max c 0-(max c 0)^2/(4*delta))
      (b-delta*(1-messageRatio u*childLog lam u)/
        (u*(childLog lam u)^2*(messageRatio u-1+u)))) ≤
      minimumCurveDerivative b c d delta lam u := by
  have hc := half_child_bounds hl hu huh
  apply response_derivative_three_endpoints hd hdelta hc.2.1 hc.2.2.2.1 hr heta heta1
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · rw [child_derivative_endpoint b delta hl hu huh hdelta]
    exact (min_le_right _ _).trans (min_le_right _ _)

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.minimumAlong
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.minimumAlong
#check Erdos993Lean.Analytic.V213.VarianceResponse.minimumCurveDerivative
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.minimumCurveDerivative
#check Erdos993Lean.Analytic.V213.VarianceResponse.minimumAlong_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.minimumAlong_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.minimumCurveDerivative_eq_ratio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.minimumCurveDerivative_eq_ratio
#check Erdos993Lean.Analytic.V213.VarianceResponse.minimumCurveDerivative_gt_b_of_nonpos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.minimumCurveDerivative_gt_b_of_nonpos
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_derivative_three_endpoints
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_derivative_three_endpoints
#check Erdos993Lean.Analytic.V213.VarianceResponse.minimumCurveDerivative_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.minimumCurveDerivative_lower
