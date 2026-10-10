module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightBoundaryAlgebra
public import Erdos993Lean.Analytic.V213.ResponseSourceChords
public import Erdos993Lean.Analytic.V213.ResponseJointQuadratic

/-! Eq18 with the actual source chord discharged, followed by the exact
continuous determinant seam. Determinant positivity is not supplied here;
it remains the separate printed finite-polynomial obligation. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

open Set FreeCountVariance.Envelopes

theorem boundary_quadratic_lower {i : Fin 4} {phase : ℕ} {lam H rho y : ℝ}
    (hrow : inRow i lam) (hH : 0<H) (hcap : H≤childQ lam/2)
    (hphase : phaseDomain phase lam H rho) :
    jointQuadratic i phase lam H rho (parentY H*y/H) ≤
      parentY H*parentPayment i lam H rho H y/halfParent lam H := by
  have hl := (row_activity_bounds hrow).1
  have hr := phase_feasible hl hH.le hcap hphase
  exact boundary_quadratic_lower_of_source_chord hrow hH hcap hr.1 hr.2 hphase
    (sourceChord_lower hl hH.le hcap hphase)

theorem halfParent_continuousOn {lam : ℝ} (hl : 0<lam) :
    ContinuousOn (halfParent lam) (Icc 0 (childQ lam/2)) := by
  intro H hH
  have hp := halfParent_bounds hl hH.1 hH.2
  have hHm : 0<1-H := by linarith [hp.1]
  have hd : 1+lam*(1-H)≠0 := ne_of_gt (by positivity)
  unfold halfParent chartParent
  fun_prop (disch := assumption)

theorem sourceChord_continuousOn {lam : ℝ} (hl : 0<lam) (phase : ℕ) :
    ContinuousOn (sourceChordA phase lam) (Icc 0 (childQ lam/2)) ∧
    ContinuousOn (sourceChordB phase lam) (Icc 0 (childQ lam/2)) := by
  have hp := halfParent_continuousOn hl
  have he : ContinuousOn (sourceChordError lam) (Icc 0 (childQ lam/2)) := by
    intro H hH
    have hc : 2*H*(1+lam)≤lam :=
      (le_div_iff₀ (show 0<1+lam by linarith)).mp (show 2*H≤childQ lam by linarith [hH.2])
    have hd : 4*lam*(lam-(1+lam)*H)≠0 := ne_of_gt (mul_pos (by positivity) (by nlinarith))
    unfold sourceChordError
    fun_prop (disch := assumption)
  unfold sourceChordA sourceChordB
  by_cases hs : phase=1
  · simp only [hs,ite_true]
    constructor <;> fun_prop
  · simp only [hs,ite_false]
    constructor <;> fun_prop

theorem sourceChord_leaf {lam : ℝ} (hl : 0<lam) (rho : ℝ) :
    sourceChordA 2 lam 0*rho+sourceChordB 2 lam 0 =
      sourceSlopeA (childQ lam)*rho+sourceIntercept (childQ lam) := by
  simp only [sourceChordA,sourceChordB,show (2:ℕ)≠1 by decide,if_false]
  unfold sourceChordError halfParent chartParent sourceSlopeA sourceSlopeB childQ
  field_simp [hl.ne',show 1+lam≠0 by positivity]
  ring

theorem quadratic_coefficients_continuousOn {i : Fin 4} {lam : ℝ}
    (hrow : inRow i lam) (phase : ℕ) :
    ContinuousOn (quadraticA2 i phase lam) (Icc 0 (childQ lam/2)) ∧
    ContinuousOn (quadraticA1 i phase lam) (Icc 0 (childQ lam/2)) ∧
    ContinuousOn (quadraticA0 i phase lam) (Icc 0 (childQ lam/2)) ∧
    ContinuousOn (quadraticB1 lam) (Icc 0 (childQ lam/2)) ∧
    ContinuousOn (quadraticB0 i lam) (Icc 0 (childQ lam/2)) ∧
    ContinuousOn (quadraticK i lam) (Icc 0 (childQ lam/2)) := by
  have hl := (row_activity_bounds hrow).1
  have hp := halfParent_continuousOn hl
  have ha := (sourceChord_continuousOn hl phase).1
  have hb := (sourceChord_continuousOn hl phase).2
  have hU : ContinuousOn (fun H=>upperRatio (halfParent lam H)) (Icc 0 (childQ lam/2)) := by
    unfold upperRatio
    fun_prop
  have hR : ContinuousOn (responseFactor i lam) (Icc 0 (childQ lam/2)) := by
    intro H hH
    have hd := (responseFactor_den_pos hl hH.1 hH.2).ne'
    unfold responseFactor
    fun_prop (disch := assumption)
  have hlow : ContinuousOn lowerChildRatio (Icc 0 (childQ lam/2)) := by
    intro H hH
    have hh := (halfParent_bounds hl hH.1 hH.2).1
    have hd : 2-H≠0 := by linarith
    unfold lowerChildRatio
    fun_prop (disch := assumption)
  have hstar : ContinuousOn (fun H=>rhoStar lam (halfParent lam H)) (Icc 0 (childQ lam/2)) := by
    exact continuousOn_const.div hp (fun H hH=>(halfParent_bounds hl hH.1 hH.2).2.1.ne')
  have hmu : ContinuousOn (phaseCorrection i phase lam) (Icc 0 (childQ lam/2)) := by
    unfold phaseCorrection
    by_cases hm : i=3 ∧ phase=1
    · simp only [hm,true_and,ite_true,halfXi]
      fun_prop
    · simp only [hm,ite_false]
      fun_prop
  have hinv : ContinuousOn (fun H=>capitalGamma i lam/halfParent lam H) (Icc 0 (childQ lam/2)) :=
    continuousOn_const.div hp (fun H hH=>(halfParent_bounds hl hH.1 hH.2).2.1.ne')
  unfold quadraticA2 quadraticA1 quadraticA0 quadraticB1 quadraticB0 quadraticK
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> fun_prop

theorem quadraticK_at_zero {i : Fin 4} {lam : ℝ} (hl : 0<lam) :
    quadraticK i lam 0 = capitalGamma i lam/childQ lam+2*delta i lam*(1+lam)/lam^2 := by
  unfold quadraticK lowerChildRatio halfParent chartParent responseFactor childQ
  field_simp [hl.ne',show 1+lam≠0 by positivity]
  ring

theorem quadraticK_zero_pos {i : Fin 4} {lam : ℝ} (hrow : inRow i lam) :
    0<quadraticK i lam 0 := by
  have hl := (row_activity_bounds hrow).1
  have hG := row_Gamma_pos hrow
  have hd := (all_rows_fields_positive hrow).2.2.2
  have hq : 0<childQ lam := div_pos hl (by linarith)
  rw [quadraticK_at_zero hl]
  positivity

theorem joint_positive_of_determinant {i : Fin 4} {phase : ℕ} {lam : ℝ}
    (hrow : inRow i lam) (hphase : phase=1 ∨ phase=2)
    (hDet : ∀ H∈Icc 0 (childQ lam/2), 0<jointDeterminant i phase lam H) :
    (∀ H∈Icc 0 (childQ lam/2),0<jointXi i phase lam H) ∧
    (∀ H∈Ioc 0 (childQ lam/2),∀ rho z : ℝ,0<jointQuadratic i phase lam H rho z) := by
  have hl := (row_activity_bounds hrow).1
  have hq : 0<childQ lam := div_pos hl (by linarith)
  rcases quadratic_coefficients_continuousOn hrow phase with ⟨h2,h1,h0,hb1,hb0,hk⟩
  have hA : ∀ H∈Icc 0 (childQ lam/2),0<quadraticA2 i phase lam H := by
    intro H hH
    have hs := sourceChord_slopes_pos hl hH.1 hH.2
    have ha : 0<sourceChordA phase lam H := by rcases hphase with rfl | rfl; exact hs.1; exact hs.2
    exact mul_pos (row_price_pos hrow) ha
  exact joint_quadratic_connectedness (by positivity)
    (quadraticA2 i phase lam) (quadraticA1 i phase lam) (quadraticA0 i phase lam)
    (quadraticB1 lam) (quadraticB0 i lam) (quadraticK i lam)
    h2 h1 h0 hb1 hb0 hk hA (quadraticK_zero_pos hrow) hDet

theorem boundary_positive_of_determinant {i : Fin 4} {phase : ℕ} {lam H rho y : ℝ}
    (hrow : inRow i lam) (hH : 0<H) (hcap : H≤childQ lam/2)
    (hphase : phaseDomain phase lam H rho)
    (hDet : ∀ x∈Icc 0 (childQ lam/2),0<jointDeterminant i phase lam x) :
    0<parentPayment i lam H rho H y := by
  have hl := (row_activity_bounds hrow).1
  have hp := halfParent_bounds hl hH.le hcap
  have hY : 0<parentY H := scalarLog_pos hH (by linarith [hp.1])
  have hphase' : phase=1 ∨ phase=2 := by rcases hphase with h | h; exact Or.inl h.1; exact Or.inr h.1
  have hQ := (joint_positive_of_determinant hrow hphase' hDet).2 H ⟨hH,hcap⟩ rho (parentY H*y/H)
  have hlow := boundary_quadratic_lower (y:=y) hrow hH hcap hphase
  have hpos : 0<parentY H*parentPayment i lam H rho H y/halfParent lam H := hQ.trans_le hlow
  exact (mul_pos_iff_of_pos_left hY).mp ((div_pos_iff_of_pos_right hp.2.1).mp hpos)

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_quadratic_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_quadratic_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.halfParent_continuousOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.halfParent_continuousOn
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_continuousOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_continuousOn
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_leaf
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_leaf
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadratic_coefficients_continuousOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadratic_coefficients_continuousOn
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticK_at_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticK_at_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticK_zero_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticK_zero_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.joint_positive_of_determinant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.joint_positive_of_determinant
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_positive_of_determinant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_positive_of_determinant
