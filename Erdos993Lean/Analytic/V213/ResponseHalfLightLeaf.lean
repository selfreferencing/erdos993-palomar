module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightDeterminantPositive
public import Erdos993Lean.Analytic.V213.ResponseBoundaryQuadratic
public import Erdos993Lean.Analytic.V213.ResponseOneVertex

/-! The parent-leaf face is the original payment p*N, not the nonleaf formula
with parentY=0. Determinant positivity at H=0 is supplied by the finite068
consumer; no positivity assumption is exposed by the public leaf theorem. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

open HalfLight Set
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.O2

noncomputable def parentLeafN (i : Fin 4) (lam rho : ℝ) : ℝ :=
  price i lam*rho*O2.src lam (childQ lam) rho+alpha i lam*(1-rho)-
    (rho*(1-childQ lam)+gamma i lam*messageRatio (childQ lam))

noncomputable def parentLeafPayment (i : Fin 4) (lam rho : ℝ) : ℝ :=
  childQ lam*parentLeafN i lam rho

theorem halfParent_zero (lam : ℝ) : halfParent lam 0 = childQ lam := by
  simp [halfParent,chartParent,childQ]

theorem parent_leaf_phase_seam {lam : ℝ} (hl : 0 < lam) :
    rhoMin lam (childQ lam) = rhoStar lam (childQ lam) := by
  have hq : childQ lam ≠ 0 := ne_of_gt (by unfold childQ; positivity)
  have hq1 : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hq1' : 0 < 1-childQ lam := sub_pos.mpr hq1
  have hd : 0 < 1+lam*(1-childQ lam) := by positivity
  unfold rhoMin rhoStar
  apply (div_eq_div_iff hd.ne' hq).2
  rw [sourceSwitch_activity hl]
  unfold childQ
  field_simp [show 1+lam≠0 by positivity,show 1+2*lam≠0 by positivity]
  ring

private theorem positive_quadratic_from_gap {a b c : ℝ} (ha : 0<a)
    (hgap : 0<4*a*c-b^2) (x : ℝ) : 0<a*x^2+b*x+c := by
  have hid : 4*a*(a*x^2+b*x+c) = (2*a*x+b)^2+(4*a*c-b^2) := by ring
  have hp : 0<4*a*(a*x^2+b*x+c) := by nlinarith [sq_nonneg (2*a*x+b)]
  exact (mul_pos_iff_of_pos_left (by positivity : 0<4*a)).mp hp

theorem parent_leaf_quadratic_pos {i : Fin 4} {lam : ℝ} (hrow : inRow i lam)
    (rho : ℝ) :
    0 < quadraticA2 i 2 lam 0*rho^2+quadraticA1 i 2 lam 0*rho+quadraticA0 i 2 lam 0 := by
  have hl := (row_activity_bounds hrow).1
  have hq : 0 < childQ lam := by unfold childQ; positivity
  have hcap : (0:ℝ) ≤ childQ lam/2 := by positivity
  have hdet := HalfLightGates.printed_jointDeterminant_positive hrow
    (Or.inr rfl : (2:ℕ)=1 ∨ (2:ℕ)=2) (le_refl (0:ℝ)) hcap
  have hk := quadraticK_zero_pos hrow
  have hprod : 0 < quadraticK i lam 0*
      (4*quadraticA2 i 2 lam 0*quadraticA0 i 2 lam 0-(quadraticA1 i 2 lam 0)^2) := by
    simpa only [jointDeterminant,zero_mul,sub_zero] using hdet
  have hgap := (mul_pos_iff_of_pos_left hk).mp hprod
  have ha : 0 < quadraticA2 i 2 lam 0 :=
    mul_pos (row_price_pos hrow) (sourceChord_slopes_pos hl (le_refl 0) hcap).2
  exact positive_quadratic_from_gap ha hgap rho

theorem parent_leaf_quadratic_le_N {i : Fin 4} {lam rho : ℝ}
    (hrow : inRow i lam) (hrho : rhoMin lam (childQ lam) ≤ rho) (hrho1 : rho ≤ 1) :
    quadraticA2 i 2 lam 0*rho^2+quadraticA1 i 2 lam 0*rho+quadraticA0 i 2 lam 0 ≤
      parentLeafN i lam rho := by
  have hl := (row_activity_bounds hrow).1
  have hq : 0 < childQ lam := by unfold childQ; positivity
  have hcap : (0:ℝ) ≤ childQ lam/2 := by positivity
  have hr0 : 0 ≤ rho := (phase_split_bounds hl (le_refl 0) hcap).1.le.trans
    (by simpa only [halfParent_zero] using hrho)
  have hph : phaseDomain 2 lam 0 rho := Or.inr ⟨rfl,
    (by simpa only [halfParent_zero,←parent_leaf_phase_seam hl] using hrho),hrho1⟩
  have hs := sourceChord_lower hl (le_refl 0) hcap hph
  rw [halfParent_zero] at hs
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg (row_price_pos hrow).le hr0)
  have hu := parent_ratio_upper hrow (le_refl 0) hcap
  rw [halfParent_zero] at hu
  have hg := (all_rows_fields_positive hrow).2.2.1
  have hgu := mul_le_mul_of_nonneg_left hu hg.le
  have hcorr : phaseCorrection i 2 lam 0 = 0 := by simp [phaseCorrection]
  have hid : quadraticA2 i 2 lam 0*rho^2+quadraticA1 i 2 lam 0*rho+quadraticA0 i 2 lam 0 =
      price i lam*rho*(sourceChordA 2 lam 0*rho+sourceChordB 2 lam 0)+
      alpha i lam*(1-rho)-rho*(1-childQ lam)-gamma i lam*upperRatio (childQ lam) := by
    unfold quadraticA2 quadraticA1 quadraticA0
    rw [hcorr,halfParent_zero]
    ring
  rw [hid]
  unfold parentLeafN
  nlinarith

theorem parentLeafN_pos {i : Fin 4} {lam rho : ℝ}
    (hrow : inRow i lam) (hrho : rhoMin lam (childQ lam) ≤ rho) (hrho1 : rho ≤ 1) :
    0 < parentLeafN i lam rho :=
  (parent_leaf_quadratic_pos hrow rho).trans_le (parent_leaf_quadratic_le_N hrow hrho hrho1)

theorem parentLeafPayment_pos {i : Fin 4} {lam rho : ℝ}
    (hrow : inRow i lam) (hrho : rhoMin lam (childQ lam) ≤ rho) (hrho1 : rho ≤ 1) :
    0 < parentLeafPayment i lam rho := by
  have hl := (row_activity_bounds hrow).1
  exact mul_pos (by unfold childQ; positivity) (parentLeafN_pos hrow hrho hrho1)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem responsePayment_parent_leaf (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (i : Fin 4) {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : nbrsIn G s v = ∅) (rho t : ℝ) :
    responsePayment G lam (price i lam) (alpha i lam) (beta i lam) (gamma i lam)
      (delta i lam) s v rho t = parentLeafPayment i lam rho := by
  have hp : rootProb G lam s v = childQ lam :=
    (message_eq_q_iff_no_children hl hv).2 hchild
  have hz := zR_of_nbrsIn_empty hG hl.le hs hv hchild
  have hratio := messageRatio_root_eq (G:=G) hl s v
  have hreserve := responseReserve_leaf hG hl (gamma i lam) (delta i lam) hs hv hchild
  rw [hp] at hratio hreserve
  unfold responsePayment responseSourceMass
  simp only [hchild,Finset.sum_empty,hreserve,hp,hz]
  unfold parentLeafPayment parentLeafN
  rw [hratio]
  ring

theorem responsePayment_parent_leaf_pos (hG : G.IsAcyclic) {i : Fin 4} {lam rho : ℝ}
    (hrow : inRow i lam) {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : nbrsIn G s v = ∅) (hrho : rhoMin lam (childQ lam) ≤ rho)
    (hrho1 : rho ≤ 1) (t : ℝ) :
    0 < responsePayment G lam (price i lam) (alpha i lam) (beta i lam) (gamma i lam)
      (delta i lam) s v rho t := by
  rw [responsePayment_parent_leaf hG (row_activity_bounds hrow).1 i hs hv hchild rho t]
  exact parentLeafPayment_pos hrow hrho hrho1

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

-- Actual types and axioms.
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLeafN
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLeafN
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLeafPayment
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLeafPayment
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.halfParent_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.halfParent_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_leaf_phase_seam
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_leaf_phase_seam
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_leaf_quadratic_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_leaf_quadratic_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_leaf_quadratic_le_N
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_leaf_quadratic_le_N
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLeafN_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLeafN_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLeafPayment_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentLeafPayment_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.responsePayment_parent_leaf
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.responsePayment_parent_leaf
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.responsePayment_parent_leaf_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.responsePayment_parent_leaf_pos
#check Erdos993Lean.Analytic.O2.zR_of_nbrsIn_empty
#print axioms Erdos993Lean.Analytic.O2.zR_of_nbrsIn_empty
