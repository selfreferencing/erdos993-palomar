module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceCenterCalculus
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceUnitBinding

/-! Current T2a Sections4.3--4.5 variable elimination, ending at the literal
UnitNonnegative. The only unresolved premises are precisely the printed
polynomial signs and three rational center comparisons. No old profile,
rate, cap, unit theorem, or graph conclusion is substituted. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace
open Real Set

theorem unit_monotone_x_large (signs : CurrentPolynomialSigns) {lam p : ℝ}
    (hlam : ActivityDomain lam) (hp0 : pZero (q lam)≤p) (hpq : p≤q lam) :
    MonotoneOn (fun x=>unitExpression lam x 0 p) (Ici 0) := by
  have hl:0<lam:=by linarith [hlam.1]
  have hp:0<p:=(pZero_pos_lt (q_pos hl)).1.trans_le hp0
  have hq:=q_domain hlam
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro x hx
    exact (hasDerivAt_unit_x hl x p).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_unit_x hl x p).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_unit_x hl x p).deriv]
    have hx0:0≤x:=interior_subset hx
    by_cases he:p=q lam
    · subst p
      exact (leaf_unitXSlope_pos hlam hx0
        (signs.leafSlope _ _ hq (halfExp_pos x).le (halfExp_le_one hx0))).le
    · have hpql:p<q lam:=lt_of_le_of_ne hpq he
      exact (interior_unitXSlope_pos hlam hx0 hp hpql hp0
        (signs.interior _ _ hq (halfExp_pos x).le (halfExp_le_one hx0))).le

theorem diagonal_nonnegative (signs : CurrentPolynomialSigns) (joins : CenterJoinFacts)
    {lam p : ℝ} (hlam : ActivityDomain lam) (hp : 0<p) (hpq : p≤q lam) :
    0≤diagonal lam p := by
  by_cases he:p=q lam
  · subst p
    exact diagonal_leaf_nonnegative hlam (signs.leaf _ (q_domain hlam))
  · exact (diagonal_center_pos joins hlam).le.trans
      (diagonal_minimum_at_center hlam (signs.minus _ (q_domain hlam))
        (signs.plus _ (q_domain hlam)) hp (lt_of_le_of_ne hpq he))

/-- Literal current equation37, including the small-p feasible endpoint and
assigned leaf. The large-parent branch decreases x to b(p); the small-parent
branch increases p either to p0 or to its actual feasible endpoint 1-exp(-x). -/
theorem unit_zero_nonnegative (signs : CurrentPolynomialSigns) (joins : CenterJoinFacts)
    {lam x p : ℝ} (hlam : ActivityDomain lam) (hx : 0<x) (hp : 0<p)
    (hpq : p≤q lam) (hpx : b p≤x) : 0≤unitExpression lam x 0 p := by
  have hl:0<lam:=by linarith [hlam.1]
  have hq:=q_pos hl
  have hq1:=q_lt_one hl
  have hc:=pZero_pos_lt hq
  have hc1:(pZero (q lam))<1:=hc.2.trans hq1
  have hbc:0<b (pZero (q lam)):=b_pos hc.1 hc1
  by_cases hlarge:pZero (q lam)≤p
  · have hbp:0<b p:=b_pos hp (hpq.trans_lt hq1)
    exact (diagonal_nonnegative signs joins hlam hp hpq).trans
      (unit_monotone_x_large signs hlam hlarge hpq hbp.le hx.le hpx)
  · have hpc:p≤pZero (q lam):=le_of_lt (lt_of_not_ge hlarge)
    by_cases hxc:b (pZero (q lam))≤x
    · have hmove:=unit_antitone_small_parent hlam hx.le hp hpc le_rfl
      have hdec:=unit_monotone_x_large signs hlam (p:=pZero (q lam)) le_rfl hc.2.le
        hbc.le hx.le hxc
      exact ((diagonal_center_pos joins hlam).le.trans hdec).trans hmove
    · let r:ℝ:=1-exp (-x)
      have hex:exp (-x)<1:=by
        rw [←Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      have hr:0<r:=by dsimp [r]; linarith
      have hr1:r<1:=by dsimp [r]; linarith [Real.exp_pos (-x)]
      have hpr:p≤r:=(feasible_iff (hpq.trans_lt hq1)).1 hpx
      have hxr:x≤b (pZero (q lam)):=le_of_lt (lt_of_not_ge hxc)
      have hbound:=Real.exp_le_exp.mpr (show -b (pZero (q lam))≤-x by linarith)
      rw [exp_neg_b hc1] at hbound
      have hrc:r≤pZero (q lam):=by
        change 1-exp (-x)≤pZero (q lam)
        linarith only [hbound]
      have hbr:b r=x:=by
        unfold b
        rw [show 1-r=exp (-x) by dsimp [r]; ring,Real.log_exp]
        ring
      have hmove:=unit_antitone_small_parent hlam hx.le hp hpr hrc
      have hdiag:=diagonal_nonnegative signs joins hlam hr (hrc.trans hc.2.le)
      unfold diagonal at hdiag
      rw [hbr] at hdiag
      exact hdiag.trans hmove

/-- The complete actual unit inequality, conditional only on the finite
certificate interfaces. y=0 is separate because Pi(0) is assigned zero. -/
theorem unit_nonnegative_of_signs (signs : CurrentPolynomialSigns) (joins : CenterJoinFacts)
    {lam : ℝ} (hlam : ActivityDomain lam) : UnitNonnegative lam := by
  intro x y p hd
  rcases hd with ⟨hx,hy,hp,hpq,hpx⟩
  have hzero:=unit_zero_nonnegative signs joins hlam hx hp hpq hpx
  by_cases he:y=0
  · subst y
    exact hzero
  · have hyp:0<y:=lt_of_le_of_ne hy (Ne.symm he)
    have hstep:=eliminate_y hlam hx hp hpq hyp
    have ha:0≤a lam:=by linarith [(a_bounds hlam).1]
    have hL:0≤activityLog lam:=by
      unfold activityLog
      apply Real.log_nonneg
      linarith [hlam.1]
    exact (by nlinarith [mul_nonneg ha hL] : 0≤unitExpression lam x 0 p+a lam*activityLog lam).trans hstep

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_monotone_x_large
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_monotone_x_large
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_nonnegative
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_zero_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_zero_nonnegative
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_nonnegative_of_signs
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_nonnegative_of_signs
