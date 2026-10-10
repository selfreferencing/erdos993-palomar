module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightPhysicalModel

/-! Exact Eq19 linkage. The table selects a row and phase, the mandatory
H.1 factor and correction remain in the coefficients, and the clearing
factor is positive on the full closed xi domain. No gate result is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

open HalfLight ZeroTiltLaplace.FinitePolynomial

noncomputable def weightedClearingFactor (r : Fin 8) (lam xi : ℝ) : ℝ :=
  (omegaQ r:ℝ)*lam^4*(1+lam)^5*(2-xi)*
    (Expr.eval (phaseDen (HalfLightGates.productSpec r).phase) lam xi)^2*
      (4+4*lam-lam*xi)*(2+2*lam-(lam-1)*xi)*(2+4*lam+2*lam^2-lam^2*xi)^4*
        Expr.eval (correctionDen (HalfLightGates.productSpec r).rowIndex
          (HalfLightGates.productSpec r).phase) lam xi

theorem weightedClearingFactor_positive (r : Fin 8) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) : 0<weightedClearingFactor r lam xi := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  have hT := phaseDen_positive (HalfLightGates.productSpec r).phase hl hx hx1
  have hZ := correctionDen_positive (HalfLightGates.productSpec r).rowIndex
    (HalfLightGates.productSpec r).phase hl hx hx1
  have hw : (0:ℚ)<omegaQ r := by unfold omegaQ; positivity
  have hwR : (0:ℝ)<(omegaQ r:ℝ) := by exact_mod_cast hw
  unfold weightedClearingFactor
  positivity

theorem polynomial_eq_printed_product (r : Fin 8) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    evaluate lam xi (determinantPolynomial r)=weightedClearingFactor r lam xi*
      jointDeterminant (HalfLightGates.productSpec r).rowIndex (HalfLightGates.productSpec r).phase
        lam (lam*xi/(2*(1+lam))) := by
  let i := (HalfLightGates.productSpec r).rowIndex
  let phase := (HalfLightGates.productSpec r).phase
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  have hT := phaseDen_positive phase hl hx hx1
  have hZ := correctionDen_positive i phase hl hx hx1
  have hR : responseFactor i lam (lam*xi/(2*(1+lam)))=
      4*Expr.eval (deltaPoly i) lam xi*(2+4*lam+2*lam^2-lam^2*xi)/
        (lam^2*(2-xi)*(2+2*lam-(lam-1)*xi)) := by
    rw [responseFactor_substitution i hl hx hx1,value_deltaPoly]
  have hbaseB : -alpha i lam-beta i lam=Expr.eval (baseB i) lam xi := (value_baseB i lam xi).symm
  have hc := determinant_cleared_ten_terms lam (1+lam) (2-xi) (4+4*lam-lam*xi)
    (2+2*lam-(lam-1)*xi) (2+4*lam+2*lam^2-lam^2*xi) (2+2*lam-lam*xi)
    (Expr.eval (phaseDen phase) lam xi) (Expr.eval (correctionDen i phase) lam xi) xi
    (Expr.eval (a2Num i phase) lam xi) (Expr.eval (a1Num i phase) lam xi)
    (Expr.eval (baseANum i phase) lam xi) (Expr.eval (baseB i) lam xi)
    (Expr.eval (baseKNum i) lam xi) (Expr.eval upperRatioNum lam xi)
    (Expr.eval (gammaPoly i) lam xi) (Expr.eval (deltaPoly i) lam xi)
    hl.ne' hL.ne' hC.ne' hD.ne' hE.ne' hF.ne' hT.ne' hZ.ne' (by ring)
  dsimp only at hc
  have hprod :
      (lam^4*(1+lam)^5*(2-xi)*(Expr.eval (phaseDen phase) lam xi)^2*
        (4+4*lam-lam*xi)*(2+2*lam-(lam-1)*xi)*(2+4*lam+2*lam^2-lam^2*xi)^4*
          Expr.eval (correctionDen i phase) lam xi)*
      jointDeterminant i phase lam (lam*xi/(2*(1+lam)))=
        Expr.eval (unweightedDeterminantPoly i phase) lam xi := by
    rw [unweighted_expression_sound,jointDeterminant_affine_model,
      quadraticA2_model i phase hl hx hx1,quadraticA1_model i phase hl hx hx1,
      corrected_alpha_model i phase hl hx hx1,gamma_upper_model i hl hx hx1,
      quadraticB1_model hl hx hx1,baseK_model i hl hx hx1,hR,hbaseB]
    exact hc
  rw [determinant_encoding_sound]
  simp only [determinantExpression,value_mul,value_scalar]
  change (omegaQ r:ℝ)*Expr.eval (unweightedDeterminantPoly i phase) lam xi= _
  rw [←hprod]
  unfold weightedClearingFactor
  change (omegaQ r:ℝ)*(_*jointDeterminant i phase lam (lam*xi/(2*(1+lam))))= _
  simp only [mul_assoc] <;> rfl

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.weightedClearingFactor
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.weightedClearingFactor
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.weightedClearingFactor_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.weightedClearingFactor_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.polynomial_eq_printed_product
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.polynomial_eq_printed_product
