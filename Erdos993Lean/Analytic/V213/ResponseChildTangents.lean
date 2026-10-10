module

public import Erdos993Lean.Analytic.V213.ResponseChildCurveCalculus
public import Erdos993Lean.Analytic.V213.ResponseOneVertex

/-!
Current Lemma 5.22, completed tangent and strict-concavity conclusions.
The h-coordinate is handled parametrically, with its already proved strict
injectivity, rather than by choosing a global inverse outside its range.
The strict weighted-chord statement is precisely strict concavity on the
actual h-curve. No endpoint or derivative-sign premise is left unproved.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set FreeCountVariance.Envelopes

/-- The literal tangent in the printed R_r,D_r,Y_r notation. -/
noncomputable def childTangent (lam r h : ℝ) : ℝ :=
  let R := scalarLog r/r
  let D := (1-(1-r)*R)/r
  (h*R-1+childLog lam r*((1-r)+(2*r*D-1)*h))/D

theorem childTangent_identity {lam r : ℝ} (hr : 0 < r) (hr1 : r < 1) (h : ℝ) :
    childTangent lam r h = childJ lam r+childSlope lam r*(h-messageRatio r) := by
  have hp := (scalarLog_pos hr hr1).ne'
  have hd := (childD_pos hr hr1).ne'
  have hsmall : (1-(1-r)*(scalarLog r/r))/r = childD r/r^2 := by
    unfold childD
    field_simp [hr.ne']
  unfold childTangent
  dsimp only
  rw [hsmall]
  unfold childJ childSlope
  rw [messageRatio_eq_scalarH hr.ne']
  unfold scalarH
  field_simp [hr.ne',hp,hd]
  unfold childD
  ring

theorem childTangent_at_contact {lam r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    childTangent lam r (messageRatio r) = childJ lam r := by
  rw [childTangent_identity hr hr1]
  ring

theorem childTangent_hasDerivAt {lam r : ℝ} (hr : 0 < r) (hr1 : r < 1) (h : ℝ) :
    HasDerivAt (childTangent lam r) (childSlope lam r) h := by
  have heq : childTangent lam r =
      fun x => childJ lam r+childSlope lam r*(x-messageRatio r) := by
    funext x
    exact childTangent_identity hr hr1 x
  rw [heq]
  convert (((hasDerivAt_id h).sub_const (messageRatio r)).const_mul
    (childSlope lam r)).const_add (childJ lam r) using 1 <;> simp

private theorem contactGap_hasDerivAt {lam r u : ℝ} (hl : 0 < lam)
    (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun x => childJ lam x-childSlope lam r*messageRatio x)
      (childHDeriv u*(childSlope lam u-childSlope lam r)) u := by
  convert (childJ_hasDerivAt hl hu hu1).sub
    ((messageRatio_hasDerivAt hu hu1).const_mul (childSlope lam r)) using 1
  ring

/-- Strict support away from contact, including contact r=q. -/
theorem childJ_lt_tangent {lam r u : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3)
    (hr : 0 < r) (hrq : r ≤ childQ lam) (hu : 0 < u)
    (huq : u ≤ childQ lam) (hne : u ≠ r) :
    childJ lam u < childTangent lam r (messageRatio u) := by
  have hq := (childQ_bounds hl hl7).2.2
  have hs := childSlope_strictMonoOn hl hl7
  have hgap : childJ lam u-childSlope lam r*messageRatio u <
      childJ lam r-childSlope lam r*messageRatio r := by
    rcases lt_or_gt_of_ne hne with hur | hru
    · have hm : StrictMonoOn
          (fun x => childJ lam x-childSlope lam r*messageRatio x) (Icc u r) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        · intro x hx
          exact (contactGap_hasDerivAt hl (hu.trans_le hx.1)
            ((hx.2.trans hrq).trans_lt hq)).continuousAt.continuousWithinAt
        · intro x hx
          have hx' : u < x ∧ x < r := by simpa only [interior_Icc, mem_Ioo] using hx
          have hx0 : 0 < x := hu.trans hx'.1
          have hxq : x ≤ childQ lam := hx'.2.le.trans hrq
          rw [(contactGap_hasDerivAt hl hx0 (hxq.trans_lt hq)).deriv]
          exact mul_pos_of_neg_of_neg (childHDeriv_neg hx0 (hxq.trans_lt hq))
            (sub_neg.mpr (hs ⟨hx0,hxq⟩ ⟨hr,hrq⟩ hx'.2))
      exact hm ⟨le_rfl,hur.le⟩ ⟨hur.le,le_rfl⟩ hur
    · have hm : StrictAntiOn
          (fun x => childJ lam x-childSlope lam r*messageRatio x) (Icc r u) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
        · intro x hx
          exact (contactGap_hasDerivAt hl (hr.trans_le hx.1)
            ((hx.2.trans huq).trans_lt hq)).continuousAt.continuousWithinAt
        · intro x hx
          have hx' : r < x ∧ x < u := by simpa only [interior_Icc, mem_Ioo] using hx
          have hx0 : 0 < x := hr.trans hx'.1
          have hxq : x ≤ childQ lam := hx'.2.le.trans huq
          rw [(contactGap_hasDerivAt hl hx0 (hxq.trans_lt hq)).deriv]
          exact mul_neg_of_neg_of_pos (childHDeriv_neg hx0 (hxq.trans_lt hq))
            (sub_pos.mpr (hs ⟨hr,hrq⟩ ⟨hx0,hxq⟩ hx'.1))
      exact hm ⟨le_rfl,hru.le⟩ ⟨hru.le,le_rfl⟩ hru
  rw [childTangent_identity hr (hrq.trans_lt hq)]
  linarith

theorem childJ_le_tangent {lam r u : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3)
    (hr : 0 < r) (hrq : r ≤ childQ lam) (hu : 0 < u) (huq : u ≤ childQ lam) :
    childJ lam u ≤ childTangent lam r (messageRatio u) := by
  by_cases heq : u = r
  · subst u
    exact (childTangent_at_contact hr (hrq.trans_lt (childQ_bounds hl hl7).2.2)).ge
  · exact (childJ_lt_tangent hl hl7 hr hrq hu huq heq).le

/-- Strict concavity as a function of the actual h coordinate, with literal
    positive weights and no inverse-function convention off the curve. -/
theorem child_curve_strict_concavity {lam u v w t : ℝ}
    (hl : 0 < lam) (hl7 : lam ≤ 7/3)
    (hu : 0 < u) (huq : u ≤ childQ lam) (hv : 0 < v) (hvq : v ≤ childQ lam)
    (hw : 0 < w) (hwq : w ≤ childQ lam) (huv : u ≠ v)
    (ht : 0 < t) (ht1 : t < 1)
    (hh : messageRatio w = t*messageRatio u+(1-t)*messageRatio v) :
    t*childJ lam u+(1-t)*childJ lam v < childJ lam w := by
  have hq := (childQ_bounds hl hl7).2.2
  have hratio : messageRatio u ≠ messageRatio v := by
    intro heq
    exact huv (messageRatio_strictAntiOn.injOn
      ⟨hu.le,huq.trans_lt hq⟩ ⟨hv.le,hvq.trans_lt hq⟩ heq)
  have huw : u ≠ w := by
    intro heq
    subst w
    have hz : (1-t)*(messageRatio u-messageRatio v) = 0 := by nlinarith [hh]
    rcases mul_eq_zero.mp hz with ht0 | hh0
    · linarith
    · exact hratio (sub_eq_zero.mp hh0)
  have h1 := mul_lt_mul_of_pos_left
    (childJ_lt_tangent hl hl7 hw hwq hu huq huw) ht
  have h2 := mul_le_mul_of_nonneg_left
    (childJ_le_tangent hl hl7 hw hwq hv hvq) (by linarith : 0 ≤ 1-t)
  have heq : t*childTangent lam w (messageRatio u)+
      (1-t)*childTangent lam w (messageRatio v) = childJ lam w := by
    rw [childTangent_identity hw (hwq.trans_lt hq),
      childTangent_identity hw (hwq.trans_lt hq), hh]
    ring
  linarith

/-- The final actual-child range, with the assigned h(0)=1 upper endpoint. -/
theorem child_messageRatio_bounds {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsAcyclic)
    {lam : ℝ} (hl : 0 < lam) {s : Finset V}
    (hs : Erdos993Lean.ConnectedIn G s) {v : V} (hv : v ∈ s)
    {w : V} (hw : w ∈ Erdos993Lean.nbrsIn G s v) :
    messageRatio (Erdos993Lean.Analytic.O2.cavH lam
      (Erdos993Lean.Analytic.Tail.rootProb G lam s v)) ≤
      messageRatio (Erdos993Lean.Analytic.Tail.rootProb G lam
        (Erdos993Lean.compIn G (s.erase v) w) w) ∧
    messageRatio (Erdos993Lean.Analytic.Tail.rootProb G lam
      (Erdos993Lean.compIn G (s.erase v) w) w) ≤ 1 := by
  refine ⟨child_messageRatio_lower hG hl hs hv hw, ?_⟩
  have hp := Erdos993Lean.Analytic.Tail.rootProb_pos (G := G) hl
    (Erdos993Lean.compIn G (s.erase v) w) w
  have hp1 := Erdos993Lean.Analytic.Tail.rootProb_lt_one (G := G) hl.le
    (Erdos993Lean.self_mem_branch hw)
  have hb := (messageRatio_weak_bounds hp.le hp1).2
  linarith

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.childTangent
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childTangent
#check Erdos993Lean.Analytic.V213.VarianceResponse.childTangent_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childTangent_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.childTangent_at_contact
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childTangent_at_contact
#check Erdos993Lean.Analytic.V213.VarianceResponse.childTangent_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childTangent_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childJ_lt_tangent
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childJ_lt_tangent
#check Erdos993Lean.Analytic.V213.VarianceResponse.childJ_le_tangent
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childJ_le_tangent
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_curve_strict_concavity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_curve_strict_concavity
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_messageRatio_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_messageRatio_bounds
