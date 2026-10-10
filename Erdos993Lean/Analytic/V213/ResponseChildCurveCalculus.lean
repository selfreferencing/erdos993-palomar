module

public import Erdos993Lean.Analytic.V213.ResponseChildCurveSigns

/-!
Actual parametric child curve for current Lemma 5.22. `childSlope` is dJ/dh,
not a freely supplied derivative or bound. Its strictly positive derivative
in u proves the strictly negative curvature in the decreasing h coordinate.
No old completed band/curve theorem is imported.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set Filter FreeCountVariance.Envelopes
open scoped Topology

noncomputable def childQ (lam : ℝ) : ℝ := lam/(1+lam)
noncomputable def childLog (lam u : ℝ) : ℝ := Real.log (lam*(1-u)/u)
noncomputable def childJ (lam u : ℝ) : ℝ := u*messageRatio u*childLog lam u
noncomputable def childHDeriv (u : ℝ) : ℝ := -childD u/((1-u)*(scalarLog u)^2)
noncomputable def childSlope (lam u : ℝ) : ℝ :=
  u*(scalarLog u+(u-2*(1-u)*scalarLog u)*childLog lam u)/childD u

theorem childQ_bounds {lam : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3) :
    0 < childQ lam ∧ childQ lam ≤ 7/10 ∧ childQ lam < 1 := by
  have hd : 0 < 1+lam := by linarith
  refine ⟨div_pos hl hd, ?_, ?_⟩
  · exact (div_le_iff₀ hd).2 (by linarith)
  · exact (div_lt_one hd).2 (by linarith)

theorem childLog_nonneg {lam u : ℝ} (hl : 0 < lam)
    (hu : 0 < u) (huq : u ≤ childQ lam) : 0 ≤ childLog lam u := by
  have hc := (le_div_iff₀ (show 0 < 1+lam by linarith)).mp huq
  apply Real.log_nonneg
  exact (le_div_iff₀ hu).2 (by nlinarith)

theorem childJ_zero (lam : ℝ) : childJ lam 0 = 0 := by
  simp [childJ]

theorem childJ_at_q {lam : ℝ} (hl : 0 < lam) : childJ lam (childQ lam) = 0 := by
  have hd : 1+lam ≠ 0 := by positivity
  have hi : lam*(1-childQ lam)/childQ lam = 1 := by
    unfold childQ
    field_simp [hl.ne',hd]
    ring
  simp [childJ,childLog,hi]

theorem childLog_hasDerivAt {lam u : ℝ} (hl : 0 < lam)
    (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt (childLog lam) (-1/(u*(1-u))) u := by
  have hk : 1-u ≠ 0 := by linarith
  have hv : lam*(1-u)/u ≠ 0 := ne_of_gt (div_pos (mul_pos hl (by linarith)) hu)
  convert ((((hasDerivAt_id u).const_sub 1).const_mul lam).div
    (hasDerivAt_id u) hu.ne').log hv using 1 <;>
    (try funext x) <;> dsimp [childLog] <;> field_simp [hl.ne',hu.ne',hk] <;> ring

theorem messageRatio_hasDerivAt {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt messageRatio (childHDeriv u) u := by
  have hk : 1-u ≠ 0 := by linarith
  have hphi := (scalarLog_pos hu hu1).ne'
  have hs : HasDerivAt scalarH (childHDeriv u) u := by
    convert hasDerivAt_scalarH hu hu1 using 1
    dsimp [childHDeriv,childD]
    field_simp [hk,hphi]
    ring
  apply hs.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hu.ne'] with x hx
  exact messageRatio_eq_scalarH hx

theorem childHDeriv_neg {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : childHDeriv u < 0 := by
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (childD_pos hu hu1))
    (mul_pos (by linarith) (sq_pos_of_pos (scalarLog_pos hu hu1)))

theorem childJ_hasDerivAt {lam u : ℝ} (hl : 0 < lam)
    (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt (childJ lam) (childSlope lam u*childHDeriv u) u := by
  have hk : 1-u ≠ 0 := by linarith
  have hphi := (scalarLog_pos hu hu1).ne'
  have hD := (childD_pos hu hu1).ne'
  convert (((hasDerivAt_id u).mul (messageRatio_hasDerivAt hu hu1)).mul
    (childLog_hasDerivAt hl hu hu1)) using 1 <;>
    (try funext x) <;> (try dsimp [childJ]) <;>
    (try simp only [messageRatio_eq_scalarH hu.ne',scalarH,childSlope,childHDeriv]) <;>
    (try field_simp [hu.ne',hk,hphi,hD]) <;> (try simp only [childD]) <;> ring

theorem childSlope_hasDerivAt {lam u : ℝ} (hl : 0 < lam)
    (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt (childSlope lam)
      (scalarLog u*(childA u*childLog lam u+childB u)/(childD u)^2) u := by
  have hk : 1-u ≠ 0 := by linarith
  have hD := (childD_pos hu hu1).ne'
  have hp := hasDerivAt_scalarLog hu1
  have hv := hasDerivAt_id u
  have hnum := hv.mul (hp.add ((hv.sub (((hv.const_sub 1).const_mul 2).mul hp)).mul
    (childLog_hasDerivAt hl hu hu1)))
  convert hnum.div (childD_hasDerivAt hu1) hD using 1 <;>
    (try funext x) <;> dsimp [childSlope] <;> field_simp [hu.ne',hk,hD] <;>
    (try simp only [childD,childA,childB]) <;> ring

theorem childSlope_deriv_pos {lam u : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3)
    (hu : 0 < u) (huq : u ≤ childQ lam) :
    0 < scalarLog u*(childA u*childLog lam u+childB u)/(childD u)^2 := by
  have hq := childQ_bounds hl hl7
  have hu1 := huq.trans_lt hq.2.2
  have hu7 := huq.trans hq.2.1
  have hp := mul_nonneg (childA_pos hu hu1).le (childLog_nonneg hl hu huq)
  have hB := childB_pos hu hu7
  exact div_pos (mul_pos (scalarLog_pos hu hu1) (by linarith))
    (sq_pos_of_pos (childD_pos hu hu1))

theorem childSlope_strictMonoOn {lam : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3) :
    StrictMonoOn (childSlope lam) (Ioc 0 (childQ lam)) := by
  have hq := childQ_bounds hl hl7
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro u hu
    exact (childSlope_hasDerivAt hl hu.1 (hu.2.trans_lt hq.2.2)).continuousAt.continuousWithinAt
  · intro u hu
    have hh := interior_subset hu
    rw [(childSlope_hasDerivAt hl hh.1 (hh.2.trans_lt hq.2.2)).deriv]
    exact childSlope_deriv_pos hl hl7 hh.1 hh.2

/-- The literal negative second derivative in the h coordinate. -/
theorem child_curvature_identity {lam u : ℝ} (hl : 0 < lam)
    (hu : 0 < u) (hu1 : u < 1) :
    deriv (childSlope lam) u / deriv messageRatio u =
      -(1-u)*(scalarLog u)^3*(childA u*childLog lam u+childB u)/(childD u)^3 := by
  rw [(childSlope_hasDerivAt hl hu hu1).deriv, (messageRatio_hasDerivAt hu hu1).deriv]
  have hk : 1-u ≠ 0 := by linarith
  have hphi := (scalarLog_pos hu hu1).ne'
  have hD := (childD_pos hu hu1).ne'
  unfold childHDeriv
  field_simp [hk,hphi,hD]

theorem child_curvature_neg {lam u : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3)
    (hu : 0 < u) (huq : u ≤ childQ lam) :
    deriv (childSlope lam) u / deriv messageRatio u < 0 := by
  have hu1 := huq.trans_lt (childQ_bounds hl hl7).2.2
  rw [(childSlope_hasDerivAt hl hu hu1).deriv, (messageRatio_hasDerivAt hu hu1).deriv]
  exact div_neg_of_pos_of_neg (childSlope_deriv_pos hl hl7 hu huq) (childHDeriv_neg hu hu1)

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.childQ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childQ
#check Erdos993Lean.Analytic.V213.VarianceResponse.childLog
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childLog
#check Erdos993Lean.Analytic.V213.VarianceResponse.childJ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childJ
#check Erdos993Lean.Analytic.V213.VarianceResponse.childHDeriv
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childHDeriv
#check Erdos993Lean.Analytic.V213.VarianceResponse.childSlope
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childSlope
#check Erdos993Lean.Analytic.V213.VarianceResponse.childQ_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childQ_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.childLog_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childLog_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.childJ_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childJ_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.childJ_at_q
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childJ_at_q
#check Erdos993Lean.Analytic.V213.VarianceResponse.childLog_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childLog_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childHDeriv_neg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childHDeriv_neg
#check Erdos993Lean.Analytic.V213.VarianceResponse.childJ_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childJ_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_deriv_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_deriv_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_strictMonoOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_strictMonoOn
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_curvature_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_curvature_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_curvature_neg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_curvature_neg
