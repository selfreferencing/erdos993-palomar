module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightChild

/-! The favorable child-product endpoint on E1,E2,H, and the common lower
product used on D. Only the explicitly printed fixed logarithm comparisons
are retained as finite scalar premises; no product-sign oracle is assumed. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set FreeCountVariance.Envelopes

noncomputable def halfProductGap (lam : ℝ) : ℝ :=
  childQ lam*Real.log (2+lam)-2*Real.log (2*(1+lam)/(2+lam))
noncomputable def childProductLower (lam : ℝ) : ℝ :=
  2*(lam+2)*Real.log (lam+2)/(3*lam+4)

theorem childLog_antitone {lam u v : ℝ} (hl : 0 < lam)
    (hu : 0 < u) (huv : u ≤ v) (hv1 : v < 1) : childLog lam v ≤ childLog lam u := by
  have hv : 0 < v := hu.trans_le huv
  apply Real.log_le_log (div_pos (mul_pos hl (by linarith)) hv)
  apply (div_le_div_iff₀ hv hu).2
  nlinarith

theorem child_product_antitone {lam u v : ℝ} (hl : 0 < lam)
    (hu : 0 < u) (huv : u ≤ v) (hvq : v ≤ childQ lam) :
    messageRatio v*childLog lam v ≤ messageRatio u*childLog lam u := by
  have hq1 : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hv1 := hvq.trans_lt hq1
  have hu1 := huv.trans_lt hv1
  have hv : 0 < v := hu.trans_le huv
  have hh := messageRatio_antitoneOn ⟨hu.le,hu1⟩ ⟨hv.le,hv1⟩ huv
  have hT := childLog_antitone hl hu huv hv1
  have hT0 := childLog_nonneg hl hv hvq
  have hh0 : 0 ≤ messageRatio u := by linarith [messageRatio_strict_lower hu hu1]
  exact mul_le_mul hh hT hT0 hh0

theorem childLog_at_half_q {lam : ℝ} (hl : 0 < lam) :
    childLog lam (childQ lam/2) = Real.log (lam+2) := by
  unfold childLog
  congr 1
  unfold childQ
  field_simp [hl.ne',ne_of_gt (show 0 < 1+lam by linarith)]
  ring

theorem scalarLog_at_half_q {lam : ℝ} (hl : 0 < lam) :
    scalarLog (childQ lam/2) = Real.log (2*(1+lam)/(2+lam)) := by
  have h1 : 1+lam ≠ 0 := by positivity
  have h2 : 2+lam ≠ 0 := by positivity
  have hi : 1-childQ lam/2 = (2*(1+lam)/(2+lam))⁻¹ := by
    unfold childQ
    field_simp [h1,h2]
    ring
  unfold scalarLog
  rw [hi,Real.log_inv]
  ring

theorem halfProductGap_identity {lam : ℝ} (hl : 0 < lam) :
    (messageRatio (childQ lam/2)*childLog lam (childQ lam/2)-1)*
      (2*scalarLog (childQ lam/2)) = halfProductGap lam := by
  have hu : 0 < childQ lam/2 := by unfold childQ; positivity
  have hu1 : childQ lam/2 < 1 := by
    have hq : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
    linarith
  rw [messageRatio_eq_scalarH hu.ne',scalarH,childLog_at_half_q hl]
  unfold halfProductGap
  rw [← scalarLog_at_half_q hl]
  field_simp [(scalarLog_pos hu hu1).ne']
  ring

theorem halfProductGap_hasDerivAt {lam : ℝ} (hl : 0 < lam) :
    HasDerivAt halfProductGap
      (Real.log (2+lam)/(1+lam)^2+(lam-2)/((1+lam)*(2+lam))) lam := by
  have h1 : 1+lam ≠ 0 := by positivity
  have h2 : 2+lam ≠ 0 := by positivity
  have hi : 2*(1+lam)/(2+lam) ≠ 0 := by positivity
  have hv := hasDerivAt_id lam
  have hq := hv.div (hv.const_add 1) h1
  have hL := (hv.const_add 2).log h2
  have hr := (((hv.const_add 1).const_mul 2).div (hv.const_add 2) h2).log hi
  convert (hq.mul hL).sub (hr.const_mul 2) using 1
  · funext x
    dsimp [halfProductGap, childQ] <;> ring
  · dsimp
    field_simp [h1,h2,hi] <;> ring

theorem halfProductGap_deriv_pos {lam : ℝ} (hl : 13/10 ≤ lam) :
    0 < deriv halfProductGap lam := by
  have hl0 : 0 < lam := by linarith
  have h1 : 0 < 1+lam := by linarith
  have h2 : 0 < 2+lam := by linarith
  have h3 : 0 < 3+lam := by linarith
  have hlog := (elementary_log_bounds (show 0 ≤ 1+lam by linarith)).1
  have hlog' : 2*(1+lam)/(3+lam) ≤ Real.log (2+lam) := by convert hlog using 1 <;> ring
  have hquot := div_le_div_of_nonneg_right hlog' (sq_nonneg (1+lam))
  have hi : (2*(1+lam)/(3+lam))/(1+lam)^2+(lam-2)/((1+lam)*(2+lam)) =
      (lam^2+3*lam-2)/((1+lam)*(2+lam)*(3+lam)) := by
    field_simp [h1.ne',h2.ne',h3.ne']
    ring
  have hn : 0 < (lam^2+3*lam-2)/((1+lam)*(2+lam)*(3+lam)) := by
    exact div_pos (by nlinarith [sq_nonneg lam]) (by positivity)
  rw [(halfProductGap_hasDerivAt hl0).deriv]
  linarith

theorem halfProductGap_pos {lam : ℝ} (hl : 13/10 ≤ lam)
    (h33 : (119/100 : ℝ) < Real.log (33/10))
    (h46 : Real.log (46/33) < (1/3 : ℝ)) : 0 < halfProductGap lam := by
  have hbase : 0 < halfProductGap (13/10) := by
    unfold halfProductGap childQ
    norm_num
    nlinarith
  have hm : StrictMonoOn halfProductGap (Ici (13/10)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro x hx
      have hx0 : (13/10 : ℝ) ≤ x := hx
      exact (halfProductGap_hasDerivAt (by linarith)).continuousAt.continuousWithinAt
    · intro x hx
      exact halfProductGap_deriv_pos (interior_subset hx)
  rcases hl.eq_or_lt with heq | hlt
  · simpa only [← heq] using hbase
  · exact hbase.trans (hm (by change (13/10 : ℝ) ≤ 13/10; exact le_rfl)
      (by change (13/10 : ℝ) ≤ lam; exact hl) hlt)

theorem child_product_gt_one_EH {lam u : ℝ} (hl : 13/10 ≤ lam)
    (hu : 0 < u) (huh : u ≤ childQ lam/2)
    (h33 : (119/100 : ℝ) < Real.log (33/10))
    (h46 : Real.log (46/33) < (1/3 : ℝ)) :
    1 < messageRatio u*childLog lam u := by
  have hl0 : 0 < lam := by linarith
  have hq0 : 0 < childQ lam := div_pos hl0 (by linarith)
  have hq1 : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hi := halfProductGap_identity hl0
  have hp := halfProductGap_pos hl h33 h46
  have hs := scalarLog_pos (show 0 < childQ lam/2 by linarith) (show childQ lam/2 < 1 by linarith)
  have hhalf : 1 < messageRatio (childQ lam/2)*childLog lam (childQ lam/2) := by
    nlinarith
  exact hhalf.trans_le (child_product_antitone hl0 hu huh (by linarith))

theorem child_product_lower {lam u : ℝ} (hl : 0 < lam) (hu : 0 < u)
    (huh : u ≤ childQ lam/2) : childProductLower lam ≤ messageRatio u*childLog lam u := by
  have hq0 : 0 < childQ lam := div_pos hl (by linarith)
  have hq1 : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hhalf := messageRatio_lower (show 0 ≤ childQ lam/2 by linarith)
    (show childQ lam/2 < 1 by linarith)
  have hlog : 0 ≤ Real.log (lam+2) := Real.log_nonneg (by linarith)
  have hm := mul_le_mul_of_nonneg_right hhalf hlog
  have hi : (2*(1-childQ lam/2)/(2-childQ lam/2))*Real.log (lam+2) =
      childProductLower lam := by
    unfold childProductLower childQ
    have h1 : 1+lam ≠ 0 := by positivity
    have h2 : 3*lam+4 ≠ 0 := by positivity
    field_simp [h1,h2]
    all_goals ring_nf
    all_goals field_simp [show (4+lam*3 : ℝ) ≠ 0 by positivity] <;> ring
  rw [hi,← childLog_at_half_q hl] at hm
  exact hm.trans (child_product_antitone hl hu huh (by linarith))

theorem childProductLower_hasDerivAt {lam : ℝ} (hl : 0 < lam) :
    HasDerivAt childProductLower
      (2*(3*lam+4-2*Real.log (lam+2))/(3*lam+4)^2) lam := by
  have h2 : lam+2 ≠ 0 := by positivity
  have h3 : 3*lam+4 ≠ 0 := by positivity
  have hv := hasDerivAt_id lam
  convert ((((hv.add_const 2).const_mul 2).mul ((hv.add_const 2).log h2)).div
    ((hv.const_mul 3).add_const 4) h3) using 1
  · funext x
    dsimp [childProductLower] <;> ring
  · dsimp
    field_simp [h2,h3] <;> ring

theorem childProductLower_deriv_gt_tenth {lam : ℝ}
    (hl : 4/5 ≤ lam) (hhi : lam ≤ 13/10) : 1/10 < deriv childProductLower lam := by
  have hl0 : 0 < lam := by linarith
  have hden : 0 < 3*lam+4 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < lam+2 by linarith)
  have hn : 0 < 24-4*lam-9*lam^2 := by nlinarith
  rw [(childProductLower_hasDerivAt hl0).deriv]
  apply (lt_div_iff₀ (sq_pos_of_pos hden)).2
  nlinarith

theorem child_product_D_linear {lam u : ℝ} (hl : 4/5 ≤ lam) (hhi : lam ≤ 13/10)
    (hu : 0 < u) (huh : u ≤ childQ lam/2)
    (h14 : (36/35 : ℝ) < Real.log (14/5)) :
    9/10+(lam-4/5)/10 < messageRatio u*childLog lam u := by
  have hbase : 9/10 < childProductLower (4/5) := by
    unfold childProductLower
    norm_num
    nlinarith
  have hm : MonotoneOn (fun x => childProductLower x-x/10) (Icc (4/5) (13/10)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun x => deriv childProductLower x-1/10)
    · intro x hx
      exact ((childProductLower_hasDerivAt (by linarith [hx.1])).sub
        ((hasDerivAt_id x).div_const 10)).continuousAt.continuousWithinAt
    · intro x hx
      have hh := interior_subset hx
      have hc := childProductLower_hasDerivAt (show 0 < x by linarith [hh.1])
      rw [hc.deriv]
      exact (hc.sub ((hasDerivAt_id x).div_const 10)).hasDerivWithinAt
    · intro x hx
      have hh := interior_subset hx
      linarith [childProductLower_deriv_gt_tenth hh.1 hh.2]
  have hstep := hm ⟨le_rfl,by norm_num⟩ ⟨hl,hhi⟩ hl
  have hprod := child_product_lower (show 0 < lam by linarith) hu huh
  linarith

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap
#check Erdos993Lean.Analytic.V213.VarianceResponse.childProductLower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childProductLower
#check Erdos993Lean.Analytic.V213.VarianceResponse.childLog_antitone
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childLog_antitone
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_product_antitone
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_product_antitone
#check Erdos993Lean.Analytic.V213.VarianceResponse.childLog_at_half_q
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childLog_at_half_q
#check Erdos993Lean.Analytic.V213.VarianceResponse.scalarLog_at_half_q
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.scalarLog_at_half_q
#check Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap_deriv_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap_deriv_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.halfProductGap_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_product_gt_one_EH
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_product_gt_one_EH
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_product_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_product_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.childProductLower_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childProductLower_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childProductLower_deriv_gt_tenth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childProductLower_deriv_gt_tenth
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_product_D_linear
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_product_D_linear
