module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceRates

/-! Actual current rate shape and endpoint transfer for the23 printed groups.
No group/rate literals or numerical comparisons are generated or accepted here.
Both endpoints are needed, including the interval containing the smooth maximum.
The low extension remains a valid lower bound at the upward switch itself. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace
open Real Set

noncomputable def ratePeak : ℝ := (sqrt 5-1)/2
noncomputable def rateSlope (q : ℝ) : ℝ :=
  4*(1-q-q^2)*(1+3*q-q^2)/((1+q)*(2-q))^2

theorem ratePeak_bounds :
    (1/2:ℝ)<ratePeak ∧ ratePeak<7/10 ∧ ratePeak^2+ratePeak=1 := by
  have hs0:=sqrt_nonneg (5:ℝ)
  have hs2: (sqrt (5:ℝ))^2=5:=sq_sqrt (by norm_num)
  unfold ratePeak
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem hasDerivAt_rateR {q : ℝ} (hq : QDomain q) :
    HasDerivAt rateR (rateSlope q) q := by
  have hd:=rate_den_pos hq
  have hn:=(((hasDerivAt_id q).const_mul 2).mul
    (((hasDerivAt_id q).const_mul 2).const_add 1)).mul
    ((hasDerivAt_id q).const_sub 1)
  have hden:=((hasDerivAt_id q).const_add 1).mul ((hasDerivAt_id q).const_sub 2)
  have hh:=hn.div hden hd.ne'
  convert hh using 1 <;>
    (try funext t) <;>
    simp only [rateR,rateSlope,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,id_eq] <;>
    field_simp [hd.ne'] <;> ring

theorem rateSlope_sign {q : ℝ} (hq : QDomain q) :
    (q≤ratePeak → 0≤rateSlope q) ∧ (ratePeak≤q → rateSlope q≤0) := by
  have hpeak:=ratePeak_bounds
  have hq0:0<q:=by linarith [hq.1]
  have hq1:0<1-q:=by linarith [hq.2]
  have hfactor:0<1+3*q-q^2:=by nlinarith [mul_pos hq0 hq1]
  have hsum:0<1+ratePeak+q:=by linarith [hpeak.1]
  have hid:1-q-q^2=(ratePeak-q)*(1+ratePeak+q):=by
    nlinarith [hpeak.2.2]
  have hd:=rate_den_pos hq
  unfold rateSlope
  rw [hid]
  constructor
  · intro h
    have hh:0≤ratePeak-q:=sub_nonneg.mpr h
    positivity
  · intro h
    have hh:ratePeak-q≤0:=sub_nonpos.mpr h
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
          (mul_nonpos_of_nonpos_of_nonneg hh hsum.le)) hfactor.le
    · positivity

theorem rateR_monotone_left :
    MonotoneOn rateR (Icc (1/4:ℝ) ratePeak) := by
  have hpeak:=ratePeak_bounds
  have hQ:∀q∈Icc (1/4:ℝ) ratePeak, QDomain q:=by
    intro q hq
    exact ⟨hq.1,hq.2.trans hpeak.2.1.le⟩
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro q hq
    exact (hasDerivAt_rateR (hQ q hq)).continuousAt.continuousWithinAt
  · intro q hq
    exact (hasDerivAt_rateR (hQ q (interior_subset hq))).differentiableAt.differentiableWithinAt
  · intro q hq
    have hh:=interior_subset hq
    rw [(hasDerivAt_rateR (hQ q hh)).deriv]
    exact (rateSlope_sign (hQ q hh)).1 hh.2

theorem rateR_antitone_right :
    AntitoneOn rateR (Icc ratePeak (7/10:ℝ)) := by
  have hpeak:=ratePeak_bounds
  have hQ:∀q∈Icc ratePeak (7/10:ℝ), QDomain q:=by
    intro q hq
    exact ⟨by linarith [hpeak.1,hq.1],hq.2⟩
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro q hq
    exact (hasDerivAt_rateR (hQ q hq)).continuousAt.continuousWithinAt
  · intro q hq
    exact (hasDerivAt_rateR (hQ q (interior_subset hq))).differentiableAt.differentiableWithinAt
  · intro q hq
    have hh:=interior_subset hq
    rw [(hasDerivAt_rateR (hQ q hh)).deriv]
    exact (rateSlope_sign (hQ q hh)).2 hh.1

/-- Works also when the interval straddles the maximum; no direction of
monotonicity is guessed from its endpoints. -/
theorem rateR_min_endpoints {l t h : ℝ} (hl : QDomain l) (hh : QDomain h)
    (hlt : l≤t) (hth : t≤h) : min (rateR l) (rateR h)≤rateR t := by
  by_cases ht:t≤ratePeak
  · have hm:=rateR_monotone_left ⟨hl.1,hlt.trans ht⟩ ⟨hl.1.trans hlt,ht⟩ hlt
    exact (min_le_left _ _).trans hm
  · have ht':ratePeak≤t:=le_of_lt (lt_of_not_ge ht)
    have hm:=rateR_antitone_right ⟨ht',hth.trans hh.2⟩ ⟨ht'.trans hth,hh.2⟩ hth
    exact (min_le_right _ _).trans hm

theorem constant_rate_min_endpoints {l t h : ℝ} (hl : QDomain l) (hh : QDomain h)
    (hlt : l≤t) (hth : t≤h) (d : ℝ) :
    min (rateR l+d) (rateR h+d)≤rateR t+d := by
  have he:min (rateR l+d) (rateR h+d)=min (rateR l) (rateR h)+d:=by
    by_cases hh:rateR l≤rateR h
    · have hs : rateR l+d≤rateR h+d := by linarith only [hh]
      rw [min_eq_left hh,min_eq_left hs]
    · have hh':rateR h≤rateR l:=le_of_lt (lt_of_not_ge hh)
      have hs : rateR h+d≤rateR l+d := by linarith only [hh']
      rw [min_eq_right hh',min_eq_right hs]
  rw [he]
  have hm := rateR_min_endpoints hl hh hlt hth
  linarith only [hm]

theorem q_monotone_positive {l h : ℝ} (hl : 0<l) (hlh : l≤h) : q l≤q h := by
  have hh:0<h:=hl.trans_le hlh
  unfold q
  apply (div_le_div_iff₀ (by positivity : 0<1+l) (by positivity : 0<1+h)).2
  nlinarith

theorem actual_rate_ge_low (t : ℝ) : lowRate t≤rate t := by
  unfold lowRate rate delta
  split_ifs <;> linarith

/-- At lambda=3/4 the actual high branch is above the low right limit, so
this closed-interval lower bound is also valid for the printed group8. -/
theorem ellH_low_endpoints {l h lam : ℝ} (hl : ActivityDomain l) (hh : ActivityDomain h)
    (hll : l≤lam) (hlh : lam≤h) :
    min (lowRate (q l)) (lowRate (q h))≤ellH lam := by
  have hl0:0<l:=by linarith [hl.1]
  have hlam0:0<lam:=hl0.trans_le hll
  have hm:=constant_rate_min_endpoints (q_domain hl) (q_domain hh)
    (q_monotone_positive hl0 hll) (q_monotone_positive hlam0 hlh) (-(1/125:ℝ))
  change min (lowRate (q l)) (lowRate (q h))≤lowRate (q lam) at hm
  exact hm.trans (actual_rate_ge_low (q lam))

theorem ellH_high_endpoints {l h lam : ℝ} (hl : ActivityDomain l) (hh : ActivityDomain h)
    (hs : (3/4:ℝ)≤l) (hll : l≤lam) (hlh : lam≤h) :
    min (highRate (q l)) (highRate (q h))≤ellH lam := by
  have hl0:0<l:=by linarith [hl.1]
  have hlam0:0<lam:=hl0.trans_le hll
  have hq:=q_monotone_positive (by norm_num : (0:ℝ)<3/4) (hs.trans hll)
  have hq34:q (3/4)=(3/7:ℝ):=by norm_num [q]
  rw [hq34] at hq
  have hq3:(3/7:ℝ)≤q lam:=hq
  have hm:=constant_rate_min_endpoints (q_domain hl) (q_domain hh)
    (q_monotone_positive hl0 hll) (q_monotone_positive hlam0 hlh) (3/1250:ℝ)
  change min (highRate (q l)) (highRate (q h))≤highRate (q lam) at hm
  change min (highRate (q l)) (highRate (q h))≤rate (q lam)
  rwa [rate_high hq3]

theorem low_group_margin {l h lam bar margin : ℝ}
    (hl : ActivityDomain l) (hh : ActivityDomain h) (hll : l≤lam) (hlh : lam≤h)
    (hleft : margin≤lowRate (q l)-bar) (hright : margin≤lowRate (q h)-bar) :
    margin≤ellH lam-bar := by
  have hend:bar+margin ≤ min (lowRate (q l)) (lowRate (q h)):=
    le_min (by linarith) (by linarith)
  have hp:=hend.trans (ellH_low_endpoints hl hh hll hlh)
  linarith

theorem high_group_margin {l h lam bar margin : ℝ}
    (hl : ActivityDomain l) (hh : ActivityDomain h) (hs : (3/4:ℝ)≤l)
    (hll : l≤lam) (hlh : lam≤h)
    (hleft : margin≤highRate (q l)-bar) (hright : margin≤highRate (q h)-bar) :
    margin≤ellH lam-bar := by
  have hend:bar+margin ≤ min (highRate (q l)) (highRate (q h)):=
    le_min (by linarith) (by linarith)
  have hp:=hend.trans (ellH_high_endpoints hl hh hs hll hlh)
  linarith

theorem input_rate_margin {lam bar target margin : ℝ}
    (hgroup : margin≤ellH lam-bar) (htarget : target≤bar) :
    margin≤ellH lam-target := by linarith

theorem input_rate_threshold {lam bar target : ℝ} {g : Nat}
    (hgroup : (g:ℝ)/1000000≤ellH lam-bar) (htarget : target≤bar) (hg : 200<g) :
    target+1/5000<ellH lam := by
  have hgR:(200:ℝ)<g:=by exact_mod_cast hg
  have hm:=input_rate_margin hgroup htarget
  linarith

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.ratePeak_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.ratePeak_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_rateR
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_rateR
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateSlope_sign
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateSlope_sign
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_monotone_left
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_monotone_left
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_antitone_right
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_antitone_right
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_min_endpoints
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_min_endpoints
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.constant_rate_min_endpoints
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.constant_rate_min_endpoints
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_monotone_positive
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_monotone_positive
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.actual_rate_ge_low
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.actual_rate_ge_low
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.ellH_low_endpoints
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.ellH_low_endpoints
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.ellH_high_endpoints
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.ellH_high_endpoints
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.low_group_margin
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.low_group_margin
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.high_group_margin
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.high_group_margin
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.input_rate_margin
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.input_rate_margin
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.input_rate_threshold
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.input_rate_threshold
