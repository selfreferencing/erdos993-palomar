module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightExprMeaning
public import Erdos993Lean.Analytic.V213.ResponseHalfLightQuadraticDefs

/-! Exact rational chart of T8a(19). The closed xi interval includes both
parent-leaf and child-half-light endpoints. All five clearing factors are
proved positive before their denominators are cleared. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

open HalfLight ZeroTiltLaplace.FinitePolynomial

theorem clearing_factors_pos {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    0<1+lam ∧ 0<2-xi ∧ 0<4+4*lam-lam*xi ∧
      0<2+2*lam-(lam-1)*xi ∧ 0<2+4*lam+2*lam^2-lam^2*xi ∧
      0<2+2*lam-lam*xi := by
  have hn := mul_nonneg hl.le (show 0≤1-xi by linarith)
  have hn2 := mul_nonneg (sq_nonneg lam) (show 0≤1-xi by linarith)
  exact ⟨by linarith,by linarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

theorem halfParent_substitution {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    halfParent lam (lam*xi/(2*(1+lam)))=
      lam*(2+2*lam-lam*xi)/(2+4*lam+2*lam^2-lam^2*xi) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  have hd : 1+lam*(1-lam*xi/(2*(1+lam)))=
      (2+4*lam+2*lam^2-lam^2*xi)/(2*(1+lam)) := by
    field_simp [hL.ne']
    ring
  unfold halfParent chartParent
  rw [hd]
  field_simp [hL.ne',hF.ne'] <;> ring

theorem halfXi_substitution {lam xi : ℝ} (hl : 0<lam) :
    halfXi lam (lam*xi/(2*(1+lam)))=xi := by
  unfold halfXi childQ
  have hL : 1+lam ≠ 0 := by positivity
  field_simp [hl.ne',hL] <;> ring

theorem rhoStar_substitution {lam xi : ℝ} (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    rhoStar lam (halfParent lam (lam*xi/(2*(1+lam))))=
      (2+4*lam+2*lam^2-lam^2*xi)/((1+2*lam)*(2+2*lam-lam*xi)) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  unfold rhoStar
  rw [sourceSwitch_activity hl,halfParent_substitution hl hx hx1]
  have hT : 1+2*lam ≠ 0 := by positivity
  field_simp [hl.ne',hT,hF.ne',hG.ne'] <;> ring

theorem responseFactor_substitution (i : Fin 4) {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    responseFactor i lam (lam*xi/(2*(1+lam)))=
      4*delta i lam*(2+4*lam+2*lam^2-lam^2*xi)/
        (lam^2*(2-xi)*(2+2*lam-(lam-1)*xi)) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  have hn : 1+lam*(1-lam*xi/(2*(1+lam)))=
      (2+4*lam+2*lam^2-lam^2*xi)/(2*(1+lam)) := by
    field_simp [hL.ne']
    ring
  have hd : lam^2*(1-lam*xi/(2*(1+lam)))^2-(lam*xi/(2*(1+lam)))^2=
      lam^2*(2-xi)*(2+2*lam-(lam-1)*xi)/(4*(1+lam)) := by
    field_simp [hL.ne']
    ring
  unfold responseFactor
  rw [hn,hd]
  field_simp [hl.ne',hL.ne',hC.ne',hE.ne'] <;> ring

theorem lowerChildRatio_substitution {lam xi : ℝ}
    (hl : 0<lam) (hx : 0≤xi) (hx1 : xi≤1) :
    lowerChildRatio (lam*xi/(2*(1+lam)))=
      2*(2+2*lam-lam*xi)/(4+4*lam-lam*xi) := by
  obtain ⟨hL,hC,hD,hE,hF,hG⟩ := clearing_factors_pos hl hx hx1
  have hd : 2-lam*xi/(2*(1+lam))=(4+4*lam-lam*xi)/(2*(1+lam)) := by
    field_simp [hL.ne']
    ring
  unfold lowerChildRatio
  rw [hd]
  field_simp [hL.ne',hD.ne'] <;> ring

theorem phaseCorrection_substitution (i : Fin 4) (phase : ℕ) {lam xi : ℝ}
    (hl : 0<lam) :
    phaseCorrection i phase lam (lam*xi/(2*(1+lam)))=
      (if i=3 ∧ phase=1 then (1-xi)/3 else 0) := by
  simp only [phaseCorrection,halfXi_substitution hl]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.clearing_factors_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.clearing_factors_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.halfParent_substitution
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.halfParent_substitution
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.halfXi_substitution
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.halfXi_substitution
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.rhoStar_substitution
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.rhoStar_substitution
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.responseFactor_substitution
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.responseFactor_substitution
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.lowerChildRatio_substitution
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.lowerChildRatio_substitution
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.phaseCorrection_substitution
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.phaseCorrection_substitution
