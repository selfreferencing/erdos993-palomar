module

public import Mathlib

/-! Small determinant algebra for the exact printed half-light product.
The cancellation is proved with symbolic scalar operands before any field
polynomial is expanded. No coefficient values, slacks or sign are assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

theorem determinant_separately_affine (A B K a b c H x R : ℝ) :
    (K-H*x+R)*(4*A*(a-x+H*R)-B^2)-
      H*(A*(b+2*x-2*R)^2-B*c*(b+2*x-2*R)+(a-x+H*R)*c^2) =
    K*(4*A*a-B^2)-H*(A*b^2-B*c*b+a*c^2)+
      x*(H*(B+c)^2-4*A*(K+H*(a+b)))+
      R*(4*A*(a+H*(K+b))-(B+H*c)^2)-4*A*x*R*(1-H)^2 := by
  ring

noncomputable def determinantTenTerms (X L C D E F G T Z xi A B a b K U gam del : ℝ) : ℝ :=
  let VK := 2*L*Z*K+X^2*D*F*xi*(a+b*Z)
  let VA := 2*L*D*F*a+Z*xi*K+X*Z*D*F*xi*b
  let V := B+16*X*L^3*T
  let W := B+8*X^2*L^2*T*xi
  X^2*L^3*C*T*E*F^2*K*A*a-
    (1/16)*X*L*C*E*F*Z*K*B^2-
    (1/8)*X^4*L^2*C*T*D*E*F^3*Z*xi*A*b^2+
    (1/2)*X^4*L^3*C*T*D*E*F^2*Z*xi*B*b-
    8*X^5*L^6*C*T^2*D*E*F^2*xi*a+
    (1/320)*X^3*C*D*E*Z*gam*U*xi*V^2-
    (1/20)*X^2*L^2*C*T*E*gam*U*A*VK+
    2*X*L^2*T*F^3*del*A*VA-
    (1/4)*L*D*F^3*Z*del*W^2-
    (1/10)*X*L*T*D*F^2*Z*A*gam*del*U*G^2

/-- Clear the common denominator only after the two square self-terms cancel. -/
theorem determinant_cleared_ten_terms
    (X L C D E F G T Z xi A B a b K U gam del : ℝ)
    (hX : X ≠ 0) (hL : L ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hE : E ≠ 0) (hF : F ≠ 0) (hT : T ≠ 0) (hZ : Z ≠ 0)
    (hG : G=2*L-X*xi) :
    let H := X*xi/(2*L)
    let A2 := A/(4*X*L^2*T*F)
    let A1 := B/(4*X*L^2*T*F)
    let a0 := a/Z
    let K0 := K/(X*D*F)
    let c := 4*L/F
    let x := gam*U/(10*F^2)
    let R := 4*del*F/(X^2*C*E)
    (X^4*L^5*C*T^2*D*E*F^4*Z)*
      ((K0-H*x+R)*(4*A2*(a0-x+H*R)-A1^2)-
        H*(A2*(b+2*x-2*R)^2-A1*c*(b+2*x-2*R)+(a0-x+H*R)*c^2)) =
      determinantTenTerms X L C D E F G T Z xi A B a b K U gam del := by
  dsimp only
  rw [determinant_separately_affine]
  subst G
  unfold determinantTenTerms
  field_simp [hX,hL,hC,hD,hE,hF,hT,hZ]
  <;> ring

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinant_separately_affine
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinant_separately_affine
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinantTenTerms
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinantTenTerms
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinant_cleared_ten_terms
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinant_cleared_ten_terms
