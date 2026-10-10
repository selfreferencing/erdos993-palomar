module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceDiagonalModel
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialSigns

/-! Literal diagonal minimum at p0. Two finite sign premises remain exactly
those encoded by Pminus and Pplus. The side derivative monotonicity is proved
from the actual base curvature and the actual right correction. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Set

theorem delta_bounds (q : ℝ) : -(1/125:ℝ)≤delta q ∧ delta q≤3/1250 := by
  unfold delta
  split_ifs <;> constructor <;> norm_num

theorem diagonalJMinus_order {q v v0 d d0 : ℝ} (hq : QDomain q)
    (hv : v0≤v) (hd : d0≤d) : diagonalJMinus q v d≤diagonalJMinus q v0 d0 := by
  have hq0 := (q_factors_pos hq).1
  have hq1 : 0<1-q := (q_factors_pos hq).2.1
  have ha : 0≤aQ q := by unfold aQ; have := hq.2; positivity
  have hvp := mul_nonneg ha (sub_nonneg.mpr hv)
  have hdp := mul_nonneg (sub_nonneg.mpr hd)
    (show 0≤(1+q)^2/(q*(1+2*q)^2) by positivity)
  have hid : diagonalJMinus q v0 d0-diagonalJMinus q v d=
      aQ q*(v-v0)+(d-d0)*((1+q)^2/(q*(1+2*q)^2)) := by
    unfold diagonalJMinus
    ring
  linarith

theorem diagonalJPlus_order {q v v0 d d0 : ℝ} (hq : QDomain q)
    (hv : v0≤v) (hd : d≤d0) : diagonalJPlus q v0 d0≤diagonalJPlus q v d := by
  rcases q_factors_pos hq with ⟨hq0,hq1,hqp,hq2,hq2p,hf⟩
  have ha : 0≤aQ q := by unfold aQ; positivity
  have hvfactor : 0≤(1+q)/q^2-1 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ (sq_pos_of_pos hq0)).2
    nlinarith [hq.2]
  have hvp := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hv)) hvfactor
  have hdp := mul_nonneg (sub_nonneg.mpr hd)
    (show 0≤(1+q)^2/(q*(1+2*q)^2) by positivity)
  have hid : diagonalJPlus q v d-diagonalJPlus q v0 d0=
      aQ q*(v-v0)*((1+q)/q^2-1)+(d0-d)*((1+q)^2/(q*(1+2*q)^2)) := by
    unfold diagonalJPlus diagonalJMinus
    ring
  linarith

theorem diagonal_side_signs {lam : ℝ} (hlam : ActivityDomain lam)
    (hm : 0<polyMinus (q lam)) (hp : 0<polyPlus (q lam)) :
    diagonalJMinus (q lam) (w lam) (delta (q lam))<0 ∧
      0<diagonalJPlus (q lam) (w lam) (delta (q lam)) := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_domain hlam
  have hden := (diagonal_clearing_factors_pos hq).1
  have hminus : diagonalJMinus (q lam) (wMinus (q lam)) (-1/125)<0 := by
    unfold polyMinus at hm
    nlinarith
  have hplus : 0<diagonalJPlus (q lam) (wMinus (q lam)) (3/1250) := by
    unfold polyPlus at hp
    nlinarith
  have hw := (w_mobius_bounds hl).2.1
  have hd := delta_bounds (q lam)
  have hminusNorm : diagonalJMinus (q lam) (wMinus (q lam)) (-(1/125))<0 := by
    simpa only [neg_div] using hminus
  exact ⟨(diagonalJMinus_order hq hw hd.1).trans_lt hminusNorm,
    hplus.trans_le (diagonalJPlus_order hq hw hd.2)⟩

theorem diagonal_slopes_at_center {lam : ℝ} (hlam : ActivityDomain lam) :
    diagonalBaseSlope lam (pZero (q lam))=(1+q lam)*diagonalJMinus (q lam) (w lam) (delta (q lam)) ∧
    diagonalRightSlope lam (pZero (q lam))=(1+q lam)*diagonalJPlus (q lam) (w lam) (delta (q lam)) := by
  have hl : 0<lam := by linarith [hlam.1]
  rcases q_factors_pos (q_domain hlam) with ⟨hq,h1,hp,h2,h2p,hf⟩
  have hc : 0<1+2*q lam := by positivity
  have ha := a_eq_aQ hl
  have hc1 : 1-pZero (q lam)=1/(1+q lam) := by
    unfold pZero; field_simp [hp.ne'] <;> ring
  have hc2 : 1-q lam*pZero (q lam)=(1+q lam-(q lam)^2)/(1+q lam) := by
    unfold pZero; field_simp [hp.ne'] <;> ring
  have hc3 : 1+q lam-q lam*pZero (q lam)=(1+2*q lam)/(1+q lam) := by
    unfold pZero; field_simp [hp.ne'] <;> ring
  have hc4 : q lam-pZero (q lam)=(q lam)^2/(1+q lam) := by
    unfold pZero; field_simp [hp.ne'] <;> ring
  constructor <;> simp only [diagonalRightSlope,diagonalBaseSlope,diagonalJPlus,diagonalJMinus,ellH,rate] <;>
    rw [hc1,hc2,hc3] <;> (try rw [hc4]) <;> unfold pZero <;> rw [ha] <;>
    generalize hqv : q lam=qv at hq hp hf hc ⊢ <;>
    generalize hfv : 1+qv-qv^2=fv at hf ⊢ <;>
    generalize hcv : 1+2*qv=cv at hc ⊢ <;>
    field_simp [hq.ne',hp.ne',hf.ne',hc.ne'] <;> ring

theorem right_correction_monotone {lam p r : ℝ} (hlam : ActivityDomain lam)
    (hp0 : pZero (q lam)≤p) (hpr : p≤r) (hrq : r<q lam) :
    a lam*w lam*q lam/(p*(q lam-p))≤a lam*w lam*q lam/(r*(q lam-r)) := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hp : 0<p := (pZero_pos_lt hq).1.trans_le hp0
  have hr : 0<r := hp.trans_le hpr
  have hpq := hpr.trans_lt hrq
  have hpHalf : q lam/2≤p := by
    have htop : q lam/2≤pZero (q lam) := by
      unfold pZero
      apply (le_div_iff₀ (by positivity : 0<1+q lam)).2
      nlinarith [q_lt_one hl]
    exact htop.trans hp0
  have hden : r*(q lam-r)≤p*(q lam-p) := by
    have hh := mul_nonneg (sub_nonneg.mpr hpr) (show 0≤p+r-q lam by linarith)
    nlinarith only [hh]
  have ha : 0≤a lam := by linarith [(a_bounds hlam).1]
  have hw := (w_pos_lt_one hl).1.le
  have hqp : 0<q lam-p := sub_pos.mpr hpq
  have hqr : 0<q lam-r := sub_pos.mpr hrq
  apply (div_le_div_iff₀ (by positivity : 0<p*(q lam-p))
    (by positivity : 0<r*(q lam-r))).2
  exact mul_le_mul_of_nonneg_left hden (by positivity)

theorem diagonalRightSlope_monotone {lam p r : ℝ} (hlam : ActivityDomain lam)
    (hp0 : pZero (q lam)≤p) (hpr : p≤r) (hrq : r<q lam) :
    diagonalRightSlope lam p≤diagonalRightSlope lam r := by
  have hl : 0<lam := by linarith [hlam.1]
  have hp : 0<p := (pZero_pos_lt (q_pos hl)).1.trans_le hp0
  have hb := diagonalBaseSlope_monotone hlam ⟨hp,hpr.trans_lt hrq⟩ ⟨hp.trans_le hpr,hrq⟩ hpr
  exact add_le_add hb (right_correction_monotone hlam hp0 hpr hrq)

theorem diagonal_minimum_at_center {lam : ℝ} (hlam : ActivityDomain lam)
    (hm : 0<polyMinus (q lam)) (hP : 0<polyPlus (q lam))
    {p : ℝ} (hp : 0<p) (hpq : p<q lam) :
    diagonal lam (pZero (q lam))≤diagonal lam p := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hc := pZero_pos_lt hq
  have hsign := diagonal_side_signs hlam hm hP
  have hsl := diagonal_slopes_at_center hlam
  have hleft : diagonalBaseSlope lam (pZero (q lam))<0 := by
    rw [hsl.1]
    exact mul_neg_of_pos_of_neg (by positivity) hsign.1
  have hright : 0<diagonalRightSlope lam (pZero (q lam)) := by
    rw [hsl.2]
    exact mul_pos (by positivity) hsign.2
  by_cases hpc : p≤pZero (q lam)
  · have hmono : AntitoneOn (diagonalLeftValue lam) (Ioc 0 (pZero (q lam))) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 _)
      · intro z hz
        exact (hasDerivAt_diagonalLeftValue hlam hz.1 (hz.2.trans_lt hc.2)).continuousAt.continuousWithinAt
      · intro z hz
        have hz' := interior_subset hz
        exact (hasDerivAt_diagonalLeftValue hlam hz'.1 (hz'.2.trans_lt hc.2)).differentiableAt.differentiableWithinAt
      · intro z hz
        have hz' := interior_subset hz
        rw [(hasDerivAt_diagonalLeftValue hlam hz'.1 (hz'.2.trans_lt hc.2)).deriv]
        exact (diagonalBaseSlope_monotone hlam ⟨hz'.1,hz'.2.trans_lt hc.2⟩ hc hz'.2).trans hleft.le
    rw [diagonal_eq_left hl hc.1 le_rfl,diagonal_eq_left hl hp hpc]
    exact hmono ⟨hp,hpc⟩ ⟨hc.1,le_rfl⟩ hpc
  · have hcp : pZero (q lam)≤p := le_of_lt (lt_of_not_ge hpc)
    have hmono : MonotoneOn (diagonalRightValue lam) (Ico (pZero (q lam)) (q lam)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ico _ _)
      · intro z hz
        exact (hasDerivAt_diagonalRightValue hlam (hc.1.trans_le hz.1) hz.2).continuousAt.continuousWithinAt
      · intro z hz
        have hz' := interior_subset hz
        exact (hasDerivAt_diagonalRightValue hlam (hc.1.trans_le hz'.1) hz'.2).differentiableAt.differentiableWithinAt
      · intro z hz
        have hz' := interior_subset hz
        rw [(hasDerivAt_diagonalRightValue hlam (hc.1.trans_le hz'.1) hz'.2).deriv]
        exact hright.le.trans (diagonalRightSlope_monotone hlam le_rfl hz'.1 hz'.2)
    rw [diagonal_eq_right hl hc.1 hc.2 le_rfl,diagonal_eq_right hl hp hpq hcp]
    exact hmono ⟨le_rfl,hc.2⟩ ⟨hcp,hpq⟩ hcp

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.delta_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.delta_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalJMinus_order
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalJMinus_order
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalJPlus_order
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalJPlus_order
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_side_signs
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_side_signs
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_slopes_at_center
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_slopes_at_center
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.right_correction_monotone
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.right_correction_monotone
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalRightSlope_monotone
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalRightSlope_monotone
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_minimum_at_center
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_minimum_at_center
