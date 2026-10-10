module

public import Erdos993Lean.Analytic.V213.RowAIntegerRecords

/-!
The first three printed Row A integer-part polynomials.
No exact unprinted rational coefficient is assumed.

The identities and positive-quadratic certificates are checked in Lean.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

/-- A short square certificate, reusable for the printed quadratic checks. -/
theorem positive_quadratic {a b c : ℝ} (ha : 0 < a) (hd : 0 < 4*a*c-b^2)
    (y : ℝ) : 0 < a*y^2+b*y+c := by
  have hid : 4*a*(a*y^2+b*y+c) = (2*a*y+b)^2+(4*a*c-b^2) := by ring
  have hp : 0 < 4*a*(a*y^2+b*y+c) := by
    rw [hid]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hd
  by_contra hn
  have hn' : a*y^2+b*y+c ≤ 0 := le_of_not_gt hn
  have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4*a by positivity) hn'
  linarith

theorem floor_minus_zero_positive {x : ℝ} (hx : 0 ≤ x) :
    0 < floorPolynomial 0 x := by
  have he : 0 < 84-332*x^2+514*x^4 := by
    have h := positive_quadratic (a := 514) (b := -332) (c := 84)
      (by norm_num) (by norm_num) (x^2)
    nlinarith
  have ho : 0 < 33-245*x^2+831*x^4 := by
    have h := positive_quadratic (a := 831) (b := -245) (c := 33)
      (by norm_num) (by norm_num) (x^2)
    nlinarith
  have hxo := mul_nonneg hx ho.le
  have ht : 0 ≤ 479*x^6+162*x^7+37*x^8 := by positivity
  norm_num [floorPolynomial, floorCoefficients, Fin.sum_univ_succ]
  nlinarith

theorem floor_minus_one_positive {x : ℝ} (hx : 0 ≤ x) :
    0 < floorPolynomial 1 x := by
  norm_num [floorPolynomial, floorCoefficients, Fin.sum_univ_succ]
  positivity

theorem floor_minus_two_even_positive (x : ℝ) :
    0 < 583+2413*x^2-2605*x^4+345*x^6+480*x^8 := by
  by_cases hx : 1 ≤ x^2
  · let e := x^2-1
    have he : 0 ≤ e := by dsimp [e]; linarith
    have hid : 583+2413*x^2-2605*x^4+345*x^6+480*x^8 =
        1216+158*e+1310*e^2+2265*e^3+480*e^4 := by
      dsimp [e]
      ring
    rw [hid]
    positivity
  · let e := 1-x^2
    have he0 : 0 ≤ e := by dsimp [e]; linarith
    have he1 : e ≤ 1 := by dsimp [e]; nlinarith [sq_nonneg x]
    have he2 : e^2 ≤ 1 := by
      nlinarith [mul_nonneg he0 (show 0 ≤ 1-e by linarith)]
    have he3 : e^3 ≤ e^2 := by
      nlinarith [mul_nonneg (sq_nonneg e) (show 0 ≤ 1-e by linarith)]
    have hid : 583+2413*x^2-2605*x^4+345*x^6+480*x^8 =
        1216-158*e+1310*e^2-2265*e^3+480*e^4 := by
      dsimp [e]
      ring
    rw [hid]
    nlinarith [pow_nonneg he0 4]

theorem floor_minus_two_odd_positive (x : ℝ) :
    0 < 1984+175*x^2-2246*x^4+1300*x^6 := by
  have hq : 0 < 354*x^4-1125*x^2+1984 := by
    have h := positive_quadratic (a := 354) (b := -1125) (c := 1984)
      (by norm_num) (by norm_num) (x^2)
    nlinarith
  have hn : 0 ≤ 1300*x^2*(x^2-1)^2 := by positivity
  nlinarith

theorem floor_minus_two_positive {x : ℝ} (hx : 0 ≤ x) :
    0 < floorPolynomial 2 x := by
  have he := floor_minus_two_even_positive x
  have ho := floor_minus_two_odd_positive x
  have hxho := mul_nonneg hx ho.le
  have hrow : floorCoefficients 2 = ![583,1984,2413,175,-2605,-2246,345,1300,480] := rfl
  unfold floorPolynomial
  rw [hrow]
  norm_num [Fin.sum_univ_succ]
  nlinarith

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.positive_quadratic
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.positive_quadratic
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_zero_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_zero_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_one_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_one_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_two_even_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_two_even_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_two_odd_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_two_odd_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_two_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_minus_two_positive

