module

public import Erdos993Lean.Analytic.V213.RowAFloorFirstSigns

/-! The final three printed Row A floor polynomials.
No exact unprinted rational coefficients are inferred from these floors. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

theorem floor_plus_zero_positive {x : ℝ} (hx : 0 ≤ x) :
    0 < floorPolynomial 3 x := by
  have he : 0 < 26-62*x^2+242*x^4 := by
    have h := positive_quadratic (a := 242) (b := -62) (c := 26)
      (by norm_num) (by norm_num) (x^2)
    nlinarith
  have ht : 0 ≤ x+55*x^3+225*x^5+95*x^6+25*x^7+4*x^8 := by positivity
  have hrow : floorCoefficients 3 = ![26,1,-62,55,242,225,95,25,4] := rfl
  unfold floorPolynomial
  rw [hrow]
  norm_num [Fin.sum_univ_succ]
  nlinarith

theorem floor_plus_one_positive {x : ℝ} (hx : 0 ≤ x) :
    0 < floorPolynomial 4 x := by
  have hrow : floorCoefficients 4 = ![478,974,1211,2300,3008,1874,554,157,55] := rfl
  unfold floorPolynomial
  rw [hrow]
  norm_num [Fin.sum_univ_succ]
  positivity

theorem floor_plus_two_positive {x : ℝ} (hx : 0 ≤ x) :
    0 < floorPolynomial 5 x := by
  have hrow : floorCoefficients 5 = ![199,623,913,765,268,23,185,226,72] := rfl
  unfold floorPolynomial
  rw [hrow]
  norm_num [Fin.sum_univ_succ]
  positivity

theorem all_floor_polynomials_positive (r : Fin 6) {x : ℝ} (hx : 0 ≤ x) :
    0 < floorPolynomial r x := by
  fin_cases r
  · exact floor_minus_zero_positive hx
  · exact floor_minus_one_positive hx
  · exact floor_minus_two_positive hx
  · exact floor_plus_zero_positive hx
  · exact floor_plus_one_positive hx
  · exact floor_plus_two_positive hx

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_plus_zero_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_plus_zero_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_plus_one_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_plus_one_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_plus_two_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floor_plus_two_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.all_floor_polynomials_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.all_floor_polynomials_positive

