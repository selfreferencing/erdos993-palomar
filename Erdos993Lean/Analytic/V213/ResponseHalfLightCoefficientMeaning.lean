module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightRationalChart

/-! Numerator meanings for the exact half-light determinant. The proof
keeps the field values symbolic; field data are used only through their
literal affine definitions. No polynomial coefficient expansion is imported.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

open HalfLight ZeroTiltLaplace.FinitePolynomial

@[simp] theorem value_alphaPoly (i : Fin 4) (lam xi : ℝ) :
    Expr.eval (alphaPoly i) lam xi=alpha i lam := value_fieldPolynomial i _ _ lam xi
@[simp] theorem value_betaPoly (i : Fin 4) (lam xi : ℝ) :
    Expr.eval (betaPoly i) lam xi=beta i lam := value_fieldPolynomial i _ _ lam xi
@[simp] theorem value_gammaPoly (i : Fin 4) (lam xi : ℝ) :
    Expr.eval (gammaPoly i) lam xi=gamma i lam := value_fieldPolynomial i _ _ lam xi
@[simp] theorem value_deltaPoly (i : Fin 4) (lam xi : ℝ) :
    Expr.eval (deltaPoly i) lam xi=delta i lam := value_fieldPolynomial i _ _ lam xi
@[simp] theorem value_gammaThetaPoly (i : Fin 4) (lam xi : ℝ) :
    Expr.eval (gammaThetaPoly i) lam xi=((rowData i).gammaTheta:ℝ) := rfl

@[simp] theorem value_phaseDen (phase : ℕ) (lam xi : ℝ) :
    Expr.eval (phaseDen phase) lam xi=if phase=1 then 1 else 2-xi := by
  split_ifs with hp <;> simp [phaseDen,hp,Expr.eval]
@[simp] theorem value_correctionDen (i : Fin 4) (phase : ℕ) (lam xi : ℝ) :
    Expr.eval (correctionDen i phase) lam xi=
      if i=3 ∧ phase=1 then (1+2*lam)*(2+2*lam-lam*xi) else 1 := by
  split_ifs with hp <;> simp [correctionDen,hp,Expr.eval]
@[simp] theorem value_correctionPoly (i : Fin 4) (phase : ℕ) {lam xi : ℝ} (hl : 0<lam) :
    Expr.eval (correctionPoly i phase) lam xi=
      phaseCorrection i phase lam (lam*xi/(2*(1+lam))) := by
  rw [phaseCorrection_substitution i phase hl]
  split_ifs with hp <;> simp [correctionPoly,hp,Expr.eval] <;> ring

theorem value_a2Num (i : Fin 4) (phase : ℕ) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    Expr.eval (a2Num i phase) lam xi=
      4*lam*(1+lam)^2*(Expr.eval (phaseDen phase) lam xi)*
        (2+4*lam+2*lam^2-lam^2*xi)*
          quadraticA2 i phase lam (lam*xi/(2*(1+lam))) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  unfold quadraticA2 sourceChordA
  rw [halfParent_substitution hl hx hx1]
  by_cases hp : phase=1
  · simp [a2Num,hp,phaseDen,price,Expr.eval]
    have hLC := mul_pos hL hC
    have hTG := mul_pos (show 0<1+2*lam by positivity) hG
    have hDG := mul_pos hD hG
    ring_nf at hL hC hD hE hF hG hLC hTG hDG
    field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring_nf <;>
      field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring <;>
        (have hc := congrArg (fun z : ℝ =>
          ((rowData i).gammaTheta:ℝ)*
            (4*lam+14*lam^2-2*lam^2*xi+14*lam^3-5*lam^3*xi+
              4*lam^4-2*lam^4*xi)*z) (mul_inv_cancel₀ hF.ne')
         nlinarith only [hc])
  · simp [a2Num,hp,phaseDen,price,sourceSlopeB,childQ,sourceChordError,Expr.eval]
    have hLC := mul_pos hL hC
    have hTG := mul_pos (show 0<1+2*lam by positivity) hG
    have hDG := mul_pos hD hG
    ring_nf at hL hC hD hE hF hG hLC hTG hDG
    field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring_nf <;>
      field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring

theorem value_a1Num (i : Fin 4) (phase : ℕ) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    Expr.eval (a1Num i phase) lam xi=
      4*lam*(1+lam)^2*(Expr.eval (phaseDen phase) lam xi)*
        (2+4*lam+2*lam^2-lam^2*xi)*
          quadraticA1 i phase lam (lam*xi/(2*(1+lam))) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  unfold quadraticA1 sourceChordB
  rw [halfParent_substitution hl hx hx1]
  simp only [a1Num,value_add,value_sub,value_mul,value_pow,value_alphaPoly,
    value_betaPoly,value_lam,value_xi,value_onePlus,value_factorF,value_correctionPoly i phase hl]
  by_cases hp : phase=1
  · simp [sourceBNum,hp,phaseDen,price,Expr.eval]
    have hLC := mul_pos hL hC
    have hTG := mul_pos (show 0<1+2*lam by positivity) hG
    have hDG := mul_pos hD hG
    ring_nf at hL hC hD hE hF hG hLC hTG hDG
    field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring_nf <;>
      field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring
  · simp [sourceBNum,hp,phaseDen,price,sourceIntercept,childQ,sourceChordError,Expr.eval]
    have hLC := mul_pos hL hC
    have hTG := mul_pos (show 0<1+2*lam by positivity) hG
    have hDG := mul_pos hD hG
    ring_nf at hL hC hD hE hF hG hLC hTG hDG
    field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring_nf <;>
      field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring

theorem value_baseANum (i : Fin 4) (phase : ℕ) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    Expr.eval (baseANum i phase) lam xi=
      Expr.eval (correctionDen i phase) lam xi*
        (alpha i lam-phaseCorrection i phase lam (lam*xi/(2*(1+lam)))*
          rhoStar lam (halfParent lam (lam*xi/(2*(1+lam))))) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  rw [rhoStar_substitution hl hx hx1,phaseCorrection_substitution i phase hl]
  simp only [baseANum,value_sub,value_mul,value_alphaPoly,value_factorF]
  by_cases hp : i=3 ∧ phase=1
  · simp [correctionPoly,correctionDen,hp,Expr.eval]
    have hLC := mul_pos hL hC
    have hTG := mul_pos (show 0<1+2*lam by positivity) hG
    have hDG := mul_pos hD hG
    ring_nf at hL hC hD hE hF hG hLC hTG hDG
    field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring_nf <;>
      field_simp [hl.ne',hL.ne',hC.ne',hD.ne',hE.ne',hF.ne',hG.ne',hLC.ne',hTG.ne',hDG.ne'] <;> ring <;>
        (have hc := congrArg (fun z : ℝ =>
          (-2-4*lam+4*lam*xi-2*lam^2+3*lam^2*xi-lam^2*xi^2+2*xi)*z)
            (mul_inv_cancel₀ hG.ne')
         nlinarith only [hc])
  · simp [correctionPoly,correctionDen,hp,Expr.eval]

@[simp] theorem value_baseB (i : Fin 4) (lam xi : ℝ) :
    Expr.eval (baseB i) lam xi= -alpha i lam-beta i lam := by simp [baseB]

theorem value_upperRatioNum {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    Expr.eval upperRatioNum lam xi=
      10*(2+4*lam+2*lam^2-lam^2*xi)^2*
        upperRatio (halfParent lam (lam*xi/(2*(1+lam)))) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  rw [halfParent_substitution hl hx hx1]
  simp [upperRatioNum,upperRatio,Expr.eval]
  field_simp [hF.ne'] <;> ring

theorem value_baseKNum (i : Fin 4) {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    Expr.eval (baseKNum i) lam xi=
      lam*(4+4*lam-lam*xi)*(2+4*lam+2*lam^2-lam^2*xi)*
        (capitalGamma i lam/halfParent lam (lam*xi/(2*(1+lam)))*
          lowerChildRatio (lam*xi/(2*(1+lam)))-
            (lam*xi/(2*(1+lam)))*(1-halfParent lam (lam*xi/(2*(1+lam))))) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  let F := 2+4*lam+2*lam^2-lam^2*xi
  let D := 4+4*lam-lam*xi
  let H := lam*xi/(2*(1+lam))
  let p := halfParent lam H
  let T := capitalGamma i lam/p*lowerChildRatio H
  have hc : T=2*capitalGamma i lam*F/(lam*D) := by
    dsimp only [T,p,H,F,D]
    rw [halfParent_substitution hl hx hx1,lowerChildRatio_substitution hl hx hx1]
    rw [div_div_eq_mul_div,div_mul_div_comm]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    ring
  have ht : T*(lam*D)=2*capitalGamma i lam*F := by
    rw [hc,div_mul_cancel₀ _ (mul_ne_zero hl.ne' hD.ne')]
  have hpF : (1-p)*F=2*(1+lam) := by
    dsimp only [p,H,F]
    rw [sub_mul,one_mul,halfParent_substitution hl hx hx1,div_mul_cancel₀ _ hF.ne']
    ring
  have hgap : H*(1-p)*F=lam*xi := by
    rw [mul_assoc,hpF]
    exact div_mul_cancel₀ _ (by positivity)
  calc
    Expr.eval (baseKNum i) lam xi=2*capitalGamma i lam*F^2-lam^2*D*xi := by
      dsimp only [F,D]
      simp only [baseKNum,value_add,value_sub,value_mul,value_pow,value_gammaPoly,
        value_deltaPoly,value_factorF,value_lam,value_factorD,value_xi,capitalGamma]
      norm_num [Expr.eval] <;> ring
    _=(T*(lam*D))*F-(H*(1-p)*F)*(lam*D) := by rw [ht,hgap]; ring
    _=lam*D*F*(T-H*(1-p)) := by ring

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_alphaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_alphaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_betaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_betaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_gammaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_gammaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_deltaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_deltaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_gammaThetaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_gammaThetaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_phaseDen
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_phaseDen
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_correctionDen
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_correctionDen
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_correctionPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_correctionPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_a2Num
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_a2Num
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_a1Num
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_a1Num
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_baseANum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_baseANum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_baseB
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_baseB
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_upperRatioNum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_upperRatioNum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_baseKNum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_baseKNum
