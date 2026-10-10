module

public import Erdos993Lean.F4U.Light.Construction.PaymentAlgebra

/-! Completion of the response square for the unchanged payment, with its
literal J=0 admissibility convention. The positive curvature premise is the
named response coefficient; later support guards must discharge it. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem quadratic_complete_square (a b c y : ℝ) (hc : c ≠ 0) :
    a+b*y+c*y^2 = (a-b^2/(4*c))+c*(y-(-b/(2*c)))^2 := by
  field_simp
  <;> ring

 theorem response_curvature_of_support (delta d J L : ℝ)
    (hd : 0 < delta) (hJ : 0 < J) (hJL : J ≤ L) (hG : 0 < delta+d*L) :
    0 < d+delta/J := by
  have hGJ : 0 < delta+d*J := by
    by_cases hd0 : 0 ≤ d
    · positivity
    · have hh := mul_le_mul_of_nonpos_left hJL (le_of_not_ge hd0)
      linarith
  have heq : d+delta/J = (delta+d*J)/J := by field_simp; ring
  rw [heq]
  exact div_pos hGJ hJ

 def responseConstant (r : Row) (lam Y rho u : ℝ) : ℝ :=
  p lam Y*parentN r lam Y rho/Y + p lam Y*beta r lam*rho*childH u +
    delta r lam*(childH u)^2/childJ lam u

 def responseLinear (r : Row) (lam Y rho u : ℝ) : ℝ :=
  p lam Y*(2*parentP r lam Y rho-alpha r lam-beta r lam)-
    2*delta r lam*childH u/childJ lam u

 def responseQuadratic (r : Row) (lam Y rho u : ℝ) : ℝ :=
  gamma r lam-delta r lam-p lam Y*Y*parentP r lam Y rho+delta r lam/childJ lam u

 theorem payment_response_expansion (r : Row) (lam Y rho u y : ℝ)
    (hJ : 0 < childJ lam u) :
    payment r lam Y rho u y = responseConstant r lam Y rho u +
      responseLinear r lam Y rho u*y+responseQuadratic r lam Y rho u*y^2 := by
  simp only [payment, reserve, if_pos hJ, responseConstant, responseLinear, responseQuadratic]
  ring

 theorem MinAt_zero_reserve (r : Row) (lam Y rho u : ℝ) (hJ : childJ lam u = 0) :
    MinAt r lam Y rho u (payment r lam Y rho u (childH u)) := by
  constructor
  · intro y hy
    rcases hy with hpos | ⟨_,heq⟩
    · rw [hJ] at hpos
      exact False.elim (lt_irrefl 0 hpos)
    · subst y
      exact le_rfl
  · exact ⟨childH u, Or.inr ⟨hJ,rfl⟩,rfl⟩

 theorem MinAt_positive_reserve (r : Row) (lam Y rho u : ℝ)
    (hJ : 0 < childJ lam u) (hQ : 0 < responseQuadratic r lam Y rho u) :
    MinAt r lam Y rho u
      (responseConstant r lam Y rho u-
        (responseLinear r lam Y rho u)^2/(4*responseQuadratic r lam Y rho u)) := by
  have hsq := quadratic_complete_square (responseConstant r lam Y rho u)
    (responseLinear r lam Y rho u) (responseQuadratic r lam Y rho u)
  constructor
  · intro y _
    rw [payment_response_expansion r lam Y rho u y hJ, hsq y hQ.ne']
    have hh := mul_nonneg hQ.le
      (sq_nonneg (y-(-responseLinear r lam Y rho u/(2*responseQuadratic r lam Y rho u))))
    linarith
  · refine ⟨-responseLinear r lam Y rho u/(2*responseQuadratic r lam Y rho u),
      Or.inl hJ, ?_⟩
    rw [payment_response_expansion r lam Y rho u _ hJ, hsq _ hQ.ne']
    simp

#print axioms quadratic_complete_square
#print axioms response_curvature_of_support
#print axioms responseConstant
#print axioms responseLinear
#print axioms responseQuadratic
#print axioms payment_response_expansion
#print axioms MinAt_zero_reserve
#print axioms MinAt_positive_reserve

end
end F4Unified.LightConstruction
