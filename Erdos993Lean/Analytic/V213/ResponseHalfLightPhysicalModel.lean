module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCoefficientMeaning

/-! The actual analytic coefficients in the rational chart. All identities
are symbolic and apply on the full closed xi interval, including xi=0.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

open HalfLight ZeroTiltLaplace.FinitePolynomial

theorem phaseDen_positive (phase : ℕ) {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    0<Expr.eval (phaseDen phase) lam xi := by
  rw [value_phaseDen]
  split_ifs <;> linarith
theorem correctionDen_positive (i : Fin 4) (phase : ℕ) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    0<Expr.eval (correctionDen i phase) lam xi := by
  rw [value_correctionDen]
  split_ifs
  · exact mul_pos (by positivity) (clearing_factors_pos hl hx hx1).2.2.2.2.2
  · norm_num

theorem quadraticA2_model (i : Fin 4) (phase : ℕ) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    quadraticA2 i phase lam (lam*xi/(2*(1+lam)))=
      Expr.eval (a2Num i phase) lam xi/
        (4*lam*(1+lam)^2*Expr.eval (phaseDen phase) lam xi*(2+4*lam+2*lam^2-lam^2*xi)) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  have hT := phaseDen_positive phase hl hx hx1
  apply (eq_div_iff (by positivity)).2
  rw [value_a2Num i phase hl hx hx1]
  ring

theorem quadraticA1_model (i : Fin 4) (phase : ℕ) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    quadraticA1 i phase lam (lam*xi/(2*(1+lam)))=
      Expr.eval (a1Num i phase) lam xi/
        (4*lam*(1+lam)^2*Expr.eval (phaseDen phase) lam xi*(2+4*lam+2*lam^2-lam^2*xi)) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  have hT := phaseDen_positive phase hl hx hx1
  apply (eq_div_iff (by positivity)).2
  rw [value_a1Num i phase hl hx hx1]
  ring

theorem corrected_alpha_model (i : Fin 4) (phase : ℕ) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    alpha i lam-phaseCorrection i phase lam (lam*xi/(2*(1+lam)))*
      rhoStar lam (halfParent lam (lam*xi/(2*(1+lam))))=
        Expr.eval (baseANum i phase) lam xi/Expr.eval (correctionDen i phase) lam xi := by
  apply (eq_div_iff (correctionDen_positive i phase hl hx hx1).ne').2
  rw [value_baseANum i phase hl hx hx1]
  ring

theorem gamma_upper_model (i : Fin 4) {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    gamma i lam*upperRatio (halfParent lam (lam*xi/(2*(1+lam))))=
      Expr.eval (gammaPoly i) lam xi*Expr.eval upperRatioNum lam xi/
        (10*(2+4*lam+2*lam^2-lam^2*xi)^2) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  apply (eq_div_iff (by positivity)).2
  rw [value_gammaPoly,value_upperRatioNum hl hx hx1]
  ring

theorem quadraticB1_model {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    quadraticB1 lam (lam*xi/(2*(1+lam)))=4*(1+lam)/(2+4*lam+2*lam^2-lam^2*xi) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  unfold quadraticB1
  rw [halfParent_substitution hl hx hx1]
  apply (eq_div_iff hF.ne').2
  rw [mul_assoc,sub_mul,one_mul,div_mul_cancel₀ _ hF.ne']
  ring

theorem baseK_model (i : Fin 4) {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    capitalGamma i lam/halfParent lam (lam*xi/(2*(1+lam)))*
      lowerChildRatio (lam*xi/(2*(1+lam)))-
        (lam*xi/(2*(1+lam)))*(1-halfParent lam (lam*xi/(2*(1+lam))))=
      Expr.eval (baseKNum i) lam xi/(lam*(4+4*lam-lam*xi)*(2+4*lam+2*lam^2-lam^2*xi)) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  apply (eq_div_iff (by positivity)).2
  rw [value_baseKNum i hl hx hx1]
  ring

theorem jointDeterminant_affine_model (i : Fin 4) (phase : ℕ) (lam H : ℝ) :
    jointDeterminant i phase lam H=
      ((capitalGamma i lam/halfParent lam H*lowerChildRatio H-H*(1-halfParent lam H))-
        H*(gamma i lam*upperRatio (halfParent lam H))+responseFactor i lam H)*
      (4*quadraticA2 i phase lam H*
        ((alpha i lam-phaseCorrection i phase lam H*rhoStar lam (halfParent lam H))-
          gamma i lam*upperRatio (halfParent lam H)+H*responseFactor i lam H)-
            (quadraticA1 i phase lam H)^2)-
      H*(quadraticA2 i phase lam H*
        ((-alpha i lam-beta i lam)+2*(gamma i lam*upperRatio (halfParent lam H))-2*responseFactor i lam H)^2-
        quadraticA1 i phase lam H*quadraticB1 lam H*
          ((-alpha i lam-beta i lam)+2*(gamma i lam*upperRatio (halfParent lam H))-2*responseFactor i lam H)+
        ((alpha i lam-phaseCorrection i phase lam H*rhoStar lam (halfParent lam H))-
          gamma i lam*upperRatio (halfParent lam H)+H*responseFactor i lam H)*(quadraticB1 lam H)^2) := by
  unfold jointDeterminant quadraticK quadraticA0 quadraticB0
  ring

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.phaseDen_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.phaseDen_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.correctionDen_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.correctionDen_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.quadraticA2_model
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.quadraticA2_model
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.quadraticA1_model
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.quadraticA1_model
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.corrected_alpha_model
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.corrected_alpha_model
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.gamma_upper_model
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.gamma_upper_model
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.quadraticB1_model
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.quadraticB1_model
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.baseK_model
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.baseK_model
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.jointDeterminant_affine_model
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.jointDeterminant_affine_model
