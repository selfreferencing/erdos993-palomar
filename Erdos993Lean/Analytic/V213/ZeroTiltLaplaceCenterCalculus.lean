module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceDiagonalEndpoints

/-! The analytic part of the three center joins. All three printed rational
comparisons remain explicit in CenterJoinFacts; no finite check is run here. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace
open Real Set

noncomputable def centerLogOne (q : ℝ) : ℝ :=
  3*log q+log (1+3*q)+log (1+2*q)-log 50-log (2-q)-log (1+q)-
    log (2+q)-log (1+q-q^2)
noncomputable def centerLogOneSlope (q : ℝ) : ℝ :=
  3/q+3/(1+3*q)+2/(1+2*q)+1/(2-q)-1/(1+q)-1/(2+q)-
    (1-2*q)/(1+q-q^2)
noncomputable def centerLogTwo (q : ℝ) : ℝ :=
  3*log q+log (1+2*q)+2*log (1-q)+log (99-103*q)-log 150-
    3*log (2-q)-3*log (1+q)
noncomputable def centerLogTwoSlope (q : ℝ) : ℝ :=
  3/q+2/(1+2*q)-2/(1-q)-103/(99-103*q)+3/(2-q)-3/(1+q)
noncomputable def centerLogTwoCurvature (q : ℝ) : ℝ :=
  -3/q^2-4/(1+2*q)^2-2/(1-q)^2-103^2/(99-103*q)^2+
    3/(2-q)^2+3/(1+q)^2

structure CenterJoinFacts : Prop where
  upper : (3/1250:ℝ)<centerC1 (11/20)
  middle : centerC2 (3/7)<centerC2 (11/20)
  lower : (3/1250:ℝ)<centerC1 (3/7)+centerC2 (3/7)

theorem center_log_identities {q : ℝ} (hq : QDomain q) :
    log (centerC1 q)=centerLogOne q ∧ log (centerC2 q)=centerLogTwo q := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have h3:0<1+3*q:=by positivity
  have h22:0<1+2*q:=by positivity
  have h99:0<99-103*q:=by linarith [hq.2]
  constructor <;> simp only [centerC1,centerC2,centerLogOne,centerLogTwo] <;>
    rw [Real.log_div (by positivity) (by positivity)] <;>
    (repeat' rw [Real.log_mul (by positivity) (by positivity)]) <;>
    simp only [Real.log_pow] <;> ring

theorem hasDerivAt_centerLogOne {q : ℝ} (hq : QDomain q) :
    HasDerivAt centerLogOne (centerLogOneSlope q) q := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have d0:=((hasDerivAt_id q).log h0.ne').const_mul 3
  have d1:=(((hasDerivAt_id q).const_mul 3).const_add 1).log (by positivity)
  have d2:=(((hasDerivAt_id q).const_mul 2).const_add 1).log (by positivity)
  have d3:=((hasDerivAt_id q).const_sub 2).log h2.ne'
  have d4:=((hasDerivAt_id q).const_add 1).log hp.ne'
  have d5:=((hasDerivAt_id q).const_add 2).log h2p.ne'
  have d6:=(((hasDerivAt_id q).const_add 1).sub ((hasDerivAt_id q).pow 2)).log hf.ne'
  have hh:=((((((d0.add d1).add d2).sub_const (log 50)).sub d3).sub d4).sub d5).sub d6
  convert hh using 1 <;> (try funext t) <;> simp only [centerLogOne,centerLogOneSlope,
    Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq] <;> ring

theorem centerLogOneSlope_pos {q : ℝ} (hq : QDomain q) : 0<centerLogOneSlope q := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have hq1:q<1:=by linarith
  have h30:(3:ℝ)<3/q:=(lt_div_iff₀ h0).2 (by nlinarith)
  have h31:0≤3/(1+3*q):=by positivity
  have h21:0≤2/(1+2*q):=by positivity
  have h12:0≤1/(2-q):=by positivity
  have hn1:1/(1+q)≤(1:ℝ):=(div_le_one hp).2 (by linarith)
  have hn2:1/(2+q)≤(1/2:ℝ):=(div_le_iff₀ h2p).2 (by linarith)
  have hn3:(1-2*q)/(1+q-q^2)≤(1:ℝ):=(div_le_one hf).2 (by nlinarith)
  unfold centerLogOneSlope
  linarith

theorem centerC1_monotone : MonotoneOn centerC1 (Icc (1/4:ℝ) (7/10)) := by
  have hm : MonotoneOn centerLogOne (Icc (1/4:ℝ) (7/10)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro q hq
      exact (hasDerivAt_centerLogOne hq).continuousAt.continuousWithinAt
    · intro q hq
      exact (hasDerivAt_centerLogOne (interior_subset hq : q ∈ Icc (1/4:ℝ) (7/10))).differentiableAt.differentiableWithinAt
    · intro q hq
      rw [(hasDerivAt_centerLogOne (interior_subset hq : q ∈ Icc (1/4:ℝ) (7/10))).deriv]
      exact (centerLogOneSlope_pos (interior_subset hq : q ∈ Icc (1/4:ℝ) (7/10))).le
  intro x hx y hy hxy
  have h:=hm hx hy hxy
  rw [←(center_log_identities hx).1,←(center_log_identities hy).1] at h
  exact (Real.log_le_log_iff (center_terms_pos hx).1 (center_terms_pos hy).1).1 h

theorem hasDerivAt_centerLogTwo {q : ℝ} (hq : QDomain q) :
    HasDerivAt centerLogTwo (centerLogTwoSlope q) q := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have h99:0<99-103*q:=by linarith [hq.2]
  have d0:=((hasDerivAt_id q).log h0.ne').const_mul 3
  have d1:=(((hasDerivAt_id q).const_mul 2).const_add 1).log (by positivity)
  have d2:=(((hasDerivAt_id q).const_sub 1).log h1.ne').const_mul 2
  have d3:=(((hasDerivAt_id q).const_mul 103).const_sub 99).log h99.ne'
  have d4:=(((hasDerivAt_id q).const_sub 2).log h2.ne').const_mul 3
  have d5:=(((hasDerivAt_id q).const_add 1).log hp.ne').const_mul 3
  have hh:=(((((d0.add d1).add d2).add d3).sub_const (log 150)).sub d4).sub d5
  convert hh using 1 <;> (try funext t) <;> simp only [centerLogTwo,centerLogTwoSlope,
    Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq] <;> ring

theorem hasDerivAt_centerLogTwoSlope {q : ℝ} (hq : QDomain q) :
    HasDerivAt centerLogTwoSlope (centerLogTwoCurvature q) q := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have h99:0<99-103*q:=by linarith [hq.2]
  have d0:HasDerivAt (fun x:ℝ=>3/x) (-3/q^2) q:=by
    convert (hasDerivAt_const q (3:ℝ)).div (hasDerivAt_id q) h0.ne' using 1 <;> (try funext t) <;>
      (try simp only [Pi.div_apply,id_eq]) <;> ring
  have d1:HasDerivAt (fun x:ℝ=>2/(1+2*x)) (-4/(1+2*q)^2) q:=by
    convert (hasDerivAt_const q (2:ℝ)).div (((hasDerivAt_id q).const_mul 2).const_add 1)
      (by positivity) using 1 <;> (try funext t) <;> simp only [Pi.add_apply,Pi.mul_apply,Pi.div_apply,id_eq] <;> ring
  have d2:HasDerivAt (fun x:ℝ=>2/(1-x)) (2/(1-q)^2) q:=by
    convert (hasDerivAt_const q (2:ℝ)).div ((hasDerivAt_id q).const_sub 1) h1.ne' using 1 <;> (try funext t) <;>
      simp only [Pi.sub_apply,Pi.div_apply,id_eq] <;> ring
  have d3:HasDerivAt (fun x:ℝ=>103/(99-103*x)) (103^2/(99-103*q)^2) q:=by
    convert (hasDerivAt_const q (103:ℝ)).div
      (((hasDerivAt_id q).const_mul 103).const_sub 99) h99.ne' using 1 <;> (try funext t) <;>
      simp only [Pi.sub_apply,Pi.mul_apply,Pi.div_apply,id_eq] <;> ring
  have d4:HasDerivAt (fun x:ℝ=>3/(2-x)) (3/(2-q)^2) q:=by
    convert (hasDerivAt_const q (3:ℝ)).div ((hasDerivAt_id q).const_sub 2) h2.ne' using 1 <;> (try funext t) <;>
      simp only [Pi.sub_apply,Pi.div_apply,id_eq] <;> ring
  have d5:HasDerivAt (fun x:ℝ=>3/(1+x)) (-3/(1+q)^2) q:=by
    convert (hasDerivAt_const q (3:ℝ)).div ((hasDerivAt_id q).const_add 1) hp.ne' using 1 <;> (try funext t) <;>
      simp only [Pi.add_apply,Pi.div_apply,id_eq] <;> ring
  convert ((((d0.add d1).sub d2).sub d3).add d4).sub d5 using 1 <;> (try funext t) <;>
    (try simp only [centerLogTwoSlope,centerLogTwoCurvature,Pi.add_apply,Pi.sub_apply]) <;> ring

theorem centerLogTwoCurvature_nonpos {q : ℝ} (hq : QDomain q) :
    centerLogTwoCurvature q≤0 := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have h99:0<99-103*q:=by linarith [hq.2]
  have hpair1:3/(1+q)^2≤(3:ℝ)/q^2:=by
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) (sq_pos_of_pos h0)).2
    nlinarith
  have hpair2:3/(2-q)^2≤(2:ℝ)/(1-q)^2:=by
    apply (div_le_div_iff₀ (sq_pos_of_pos h2) (sq_pos_of_pos h1)).2
    nlinarith [sq_nonneg q,hq.2]
  have hpos1:0≤(4:ℝ)/(1+2*q)^2:=by positivity
  have hpos2:0≤(103:ℝ)^2/(99-103*q)^2:=by positivity
  unfold centerLogTwoCurvature
  simp only [neg_div]
  linarith

theorem centerLogTwo_concave : ConcaveOn ℝ (Icc (1/4:ℝ) (7/10)) centerLogTwo := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
  · intro q hq
    exact (hasDerivAt_centerLogTwo hq).continuousAt.continuousWithinAt
  · intro q hq
    exact (hasDerivAt_centerLogTwo (interior_subset hq : q ∈ Icc (1/4:ℝ) (7/10))).hasDerivWithinAt
  · intro q hq
    exact (hasDerivAt_centerLogTwoSlope (interior_subset hq : q ∈ Icc (1/4:ℝ) (7/10))).hasDerivWithinAt
  · intro q hq
    exact centerLogTwoCurvature_nonpos (interior_subset hq : q ∈ Icc (1/4:ℝ) (7/10))

theorem centerC2_ge_left_join {q : ℝ} (hq : (3/7:ℝ)≤q ∧ q≤11/20)
    (hjoin : centerC2 (3/7)≤centerC2 (11/20)) : centerC2 (3/7)≤centerC2 q := by
  have hl:QDomain (3/7):=by constructor <;> norm_num
  have hr:QDomain (11/20):=by constructor <;> norm_num
  have hm:QDomain q:=by constructor <;> linarith [hq.1,hq.2]
  let t:ℝ:=(q-3/7)/(11/20-3/7)
  have ht0:0≤t:=by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr hq.1) (by norm_num)
  have ht1:t≤1:=by dsimp [t]; norm_num; linarith [hq.2]
  have hxy:(1-t)*(3/7:ℝ)+t*(11/20)=q:=by dsimp [t]; ring
  have hc:=centerLogTwo_concave.2 hl hr (sub_nonneg.mpr ht1) ht0
    (show (1-t)+t=1 by ring)
  simp only [smul_eq_mul,hxy] at hc
  have he:=Real.log_le_log (center_terms_pos hl).2 hjoin
  rw [(center_log_identities hl).2,(center_log_identities hr).2] at he
  have ht:=mul_nonneg ht0 (sub_nonneg.mpr he)
  have hlog:centerLogTwo (3/7)≤centerLogTwo q:=by nlinarith
  rw [←(center_log_identities hl).2,←(center_log_identities hm).2] at hlog
  exact (Real.log_le_log_iff (center_terms_pos hl).2 (center_terms_pos hm).2).1 hlog

theorem center_sum_gt_delta (joins : CenterJoinFacts) {q : ℝ} (hq : QDomain q) :
    delta q<centerC1 q+centerC2 q := by
  by_cases hlo:q<3/7
  · simp only [delta,if_pos hlo]
    have hs:=center_terms_pos hq
    linarith
  · have hhi:3/7≤q:=le_of_not_gt hlo
    simp only [delta,if_neg hlo]
    by_cases hup:(11/20:ℝ)≤q
    · have hc:=centerC1_monotone (by constructor <;> norm_num) hq hup
      have hs:0<centerC2 q:=(center_terms_pos hq).2
      linarith [joins.upper]
    · have hqj:q≤11/20:=le_of_lt (lt_of_not_ge hup)
      have h1:=centerC1_monotone (by constructor <;> norm_num) hq hhi
      have h2:=centerC2_ge_left_join ⟨hhi,hqj⟩ joins.middle.le
      linarith [joins.lower]

theorem diagonal_center_pos (joins : CenterJoinFacts) {lam : ℝ}
    (hlam : ActivityDomain lam) : 0<diagonal lam (pZero (q lam)) := by
  have hsum:=center_sum_gt_delta joins (q_domain hlam)
  have hlo:=diagonal_center_lower hlam
  have hq:=q_pos (show 0<lam by linarith [hlam.1])
  have hfac:0<1+2*q lam:=by positivity
  nlinarith

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.center_log_identities
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.center_log_identities
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_centerLogOne
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_centerLogOne
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerLogOneSlope_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerLogOneSlope_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerC1_monotone
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerC1_monotone
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_centerLogTwo
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_centerLogTwo
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_centerLogTwoSlope
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_centerLogTwoSlope
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerLogTwoCurvature_nonpos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerLogTwoCurvature_nonpos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerLogTwo_concave
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerLogTwo_concave
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerC2_ge_left_join
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.centerC2_ge_left_join
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.center_sum_gt_delta
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.center_sum_gt_delta
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_center_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_center_pos

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.CenterJoinFacts
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.CenterJoinFacts
