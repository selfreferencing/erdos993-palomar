module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightProduct

/-! Literal D-row adverse estimate (11)--(13). The row-specific affine delta
bound and the two explicitly printed fixed logarithms are the only remaining
inputs. The final row wrapper will supply them from the reviewed exact fields.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

theorem child_D_adverse_numerator {lam u delta : ℝ}
    (hl : 4/5 ≤ lam) (hhi : lam ≤ 13/10) (hu : 0 < u) (huh : u ≤ childQ lam/2)
    (hd : 0 < delta) (hdhi : delta < (23+21*(lam-4/5))/1000)
    (hprod : messageRatio u*childLog lam u < 1)
    (h14 : (36/35 : ℝ) < Real.log (14/5)) :
    delta*(1-messageRatio u*childLog lam u) < 23/10000 := by
  have hlin := child_product_D_linear hl hhi hu huh h14
  have hz0 : 0 ≤ lam-4/5 := by linarith
  have hz1 : lam-4/5 ≤ 1/2 := by linarith
  have hgap : 1-messageRatio u*childLog lam u < (1-(lam-4/5))/10 := by linarith
  have hgapPos : 0 < (1-(lam-4/5))/10 := by linarith
  have h1 := mul_lt_mul_of_pos_left hgap hd
  have h2 := mul_lt_mul_of_pos_right hdhi hgapPos
  have h3 : ((23+21*(lam-4/5))/1000)*((1-(lam-4/5))/10) ≤ 23/10000 := by
    nlinarith [sq_nonneg (lam-4/5)]
  exact (h1.trans h2).trans_le h3

theorem child_D_adverse_u {lam u : ℝ}
    (hl : 4/5 ≤ lam) (hhi : lam ≤ 13/10) (hu : 0 < u) (huh : u ≤ childQ lam/2)
    (hprod : messageRatio u*childLog lam u < 1)
    (h16 : (9/8 : ℝ) < Real.log (16/5)) : 1/5 < u := by
  by_contra hnot
  have hu5 : u ≤ 1/5 := le_of_not_gt hnot
  have hu1 : u < 1 := by linarith
  have hh := messageRatio_lower hu.le hu1
  have hlow : (8/9 : ℝ) ≤ 2*(1-u)/(2-u) :=
    (le_div_iff₀ (by linarith : 0 < 2-u)).2 (by linarith)
  have harg : (16/5 : ℝ) ≤ lam*(1-u)/u := by
    apply (le_div_iff₀ hu).2
    nlinarith [mul_nonneg (show 0 ≤ lam-4/5 by linarith) (show 0 ≤ 1-u by linarith)]
  have hT : (9/8 : ℝ) < childLog lam u := h16.trans_le
    (Real.log_le_log (by norm_num) harg)
  have hhh : (8/9 : ℝ) ≤ messageRatio u := hlow.trans hh
  nlinarith [mul_nonneg (show 0 ≤ messageRatio u-8/9 by linarith)
    (show 0 ≤ childLog lam u by linarith)]

theorem child_D_log_gt_one {lam u : ℝ}
    (hl : 4/5 ≤ lam) (hhi : lam ≤ 13/10) (hu : 0 < u) (huh : u ≤ childQ lam/2)
    (h14 : (36/35 : ℝ) < Real.log (14/5)) : 1 < childLog lam u := by
  have hl0 : 0 < lam := by linarith
  have hq1 : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hanti := childLog_antitone hl0 hu huh (show childQ lam/2 < 1 by linarith)
  rw [childLog_at_half_q hl0] at hanti
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 14/5) (show 14/5 ≤ lam+2 by linarith)
  linarith

theorem child_D_adverse_gap {lam u : ℝ}
    (hl : 4/5 ≤ lam) (hhi : lam ≤ 13/10) (hu : 0 < u) (huh : u ≤ childQ lam/2)
    (hu5 : 1/5 < u) : (4/45 : ℝ) < messageRatio u-1+u := by
  have hb := half_child_bounds (show 0 < lam by linarith) hu huh
  have hden : 0 < 2-u := by linarith [hb.1]
  have hp : (4/45 : ℝ) < u*(1-u)/(2-u) := by
    apply (lt_div_iff₀ hden).2
    have hx : 0 < (5*u-1)*(8-9*u) := mul_pos (by linarith) (by linarith [hb.1])
    nlinarith
  have hh := messageRatio_lower hu.le (show u < 1 by linarith [hb.1])
  have hi : 2*(1-u)/(2-u)-1+u = u*(1-u)/(2-u) := by
    field_simp [hden.ne']
    ring
  linarith

theorem child_D_adverse_bound {lam u delta : ℝ}
    (hl : 4/5 ≤ lam) (hhi : lam ≤ 13/10) (hu : 0 < u) (huh : u ≤ childQ lam/2)
    (hd : 0 < delta) (hdhi : delta < (23+21*(lam-4/5))/1000)
    (hprod : messageRatio u*childLog lam u < 1)
    (h14 : (36/35 : ℝ) < Real.log (14/5))
    (h16 : (9/8 : ℝ) < Real.log (16/5)) :
    delta*(1-messageRatio u*childLog lam u)/
      (u*(childLog lam u)^2*(messageRatio u-1+u)) < 207/1600 := by
  have hu5 := child_D_adverse_u hl hhi hu huh hprod h16
  have hgap := child_D_adverse_gap hl hhi hu huh hu5
  have hT := child_D_log_gt_one hl hhi hu huh h14
  have hnum := child_D_adverse_numerator hl hhi hu huh hd hdhi hprod h14
  have hT2 : 1 < (childLog lam u)^2 := by nlinarith
  have hum : (1/5 : ℝ) < u*(childLog lam u)^2 := by
    have hh := mul_lt_mul_of_pos_left hT2 hu
    nlinarith
  have hden : (4/225 : ℝ) < u*(childLog lam u)^2*(messageRatio u-1+u) := by
    have hh := mul_lt_mul_of_pos_left hgap (show 0 < u*(childLog lam u)^2 by nlinarith)
    nlinarith
  apply (div_lt_iff₀ (show 0 < u*(childLog lam u)^2*(messageRatio u-1+u) by linarith)).2
  nlinarith

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.child_D_adverse_numerator
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_D_adverse_numerator
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_D_adverse_u
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_D_adverse_u
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_D_log_gt_one
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_D_log_gt_one
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_D_adverse_gap
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_D_adverse_gap
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_D_adverse_bound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_D_adverse_bound
