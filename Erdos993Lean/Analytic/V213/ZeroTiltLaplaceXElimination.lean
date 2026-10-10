module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceYElimination
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceSignPolynomials
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds

/-! Actual current equation38. The only remaining premises in the slope
positivity wrappers are the literal PI/PJ signs on their printed rectangles.
The assigned H(q)=0 is used separately; no nonleaf limit is substituted. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Set

noncomputable def eSlope (lam x : ℝ) : ℝ :=
  ellH lam*exp (-x)/(1+q lam*exp (-x))^2
noncomputable def unitXSlope (lam x p : ℝ) : ℝ :=
  K lam p-(p/b p)*(E lam x+x*eSlope lam x)-(1-a lam)*messageAt lam x

theorem b_pos {p : ℝ} (hp : 0<p) (hp1 : p<1) : 0<b p :=
  hp.trans_le (p_le_b hp1)

theorem p_div_b_upper {p : ℝ} (hp : 0<p) (hp1 : p<1) : p/b p≤(2-p)/2 := by
  have h := (FreeCountVariance.Envelopes.scalarH_bounds hp hp1).2
  simpa only [FreeCountVariance.Envelopes.scalarH,
    FreeCountVariance.Envelopes.scalarLog,b,sub_div,div_self (by norm_num : (2:ℝ)≠0)] using h

theorem interior_p_div_b_upper {q p : ℝ} (hq : QDomain q) (hp : 0<p)
    (hpq : p<q) (hp0 : pZero q≤p) : p/b p≤(2+q)/(2*(1+q)) := by
  have hp1 : p<1 := by linarith [hq.2]
  have hh := p_div_b_upper hp hp1
  have he : (2-pZero q)/2=(2+q)/(2*(1+q)) := by
    unfold pZero
    field_simp [show 1+q≠0 by linarith [hq.1]] <;> ring
  rw [←he]
  linarith

theorem interior_K_lower {lam p : ℝ} (hlam : ActivityDomain lam)
    (hp : 0<p) (hpq : p<q lam) : 1+a lam*(1-q lam)≤K lam p := by
  have hl : 0<lam := by linarith [hlam.1]
  have hb := b_pos hp (hpq.trans (q_lt_one hl))
  have ha : 0≤a lam := by linarith [(a_bounds hlam).1]
  have hh := mul_le_mul_of_nonneg_left (H_ge_b hlam hp hpq) ha
  have hw := mul_le_mul_of_nonneg_left (w_le_q hl) ha
  have hquot : a lam≤a lam*H lam p/b p := by
    apply (le_div_iff₀ hb).2
    simpa only [mul_comm] using hh
  unfold K
  linarith

theorem leaf_K_lower {lam : ℝ} (hlam : ActivityDomain lam) :
    1-a lam*q lam≤K lam (q lam) := by
  have hl : 0<lam := by linarith [hlam.1]
  have ha : 0≤a lam := by linarith [(a_bounds hlam).1]
  have hw := mul_le_mul_of_nonneg_left (w_le_q hl) ha
  simp only [K,H_leaf,mul_zero,zero_div,add_zero]
  linarith

theorem messageAt_halfExp {lam : ℝ} (hlam : 0<lam) (x : ℝ) :
    messageAt lam x=q lam*(halfExp x)^2/elimT (q lam) (halfExp x) := by
  have hq1 : 0<1-q lam := by linarith [q_lt_one hlam]
  have he : 0<1+lam*exp (-x) := by positivity
  have ht : 0<1-q lam+q lam*(halfExp x)^2 := by
    have hq := q_pos hlam
    positivity
  rw [halfExp_sq] at ht
  unfold messageAt elimT
  rw [halfExp_sq]
  have hm : lam*(1-q lam)=q lam :=
    (eq_div_iff hq1.ne').mp (activity_from_q hlam)
  apply (div_eq_div_iff he.ne' ht.ne').2
  nlinarith [congrArg (fun z : ℝ => z*exp (-x)) hm]

theorem e_combination_nonneg {lam x : ℝ} (hlam : ActivityDomain lam) (hx : 0≤x) :
    0≤E lam x+x*eSlope lam x := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hell := (activity_rate_bounds hlam).1
  unfold E eSlope
  positivity

/-- The preceding half-exponential bound supplies the actual E+xE' upper bound. -/
theorem e_combination_upper {lam x : ℝ} (hlam : ActivityDomain lam) (hx : 0≤x) :
    E lam x+x*eSlope lam x≤
      (ellH lam/q lam)*elimH0 (q lam) (halfExp x)/(elimS (q lam) (halfExp x))^2 := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hell := (activity_rate_bounds hlam).1
  have hu := halfExp_pos x
  have hs : 0<1+q lam*(halfExp x)^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right (x_le_halfExp_inv_sub hx)
    (show 0≤ellH lam*(halfExp x)^2/(1+q lam*(halfExp x)^2)^2 by positivity)
  have hid : E lam x+x*eSlope lam x=
      ellH lam/(q lam*(1+q lam*(halfExp x)^2))+
      x*(ellH lam*(halfExp x)^2/(1+q lam*(halfExp x)^2)^2) := by
    simp only [E,eSlope,halfExp_sq]
  rw [hid]
  calc
    _≤ellH lam/(q lam*(1+q lam*(halfExp x)^2))+
      ((halfExp x)⁻¹-halfExp x)*(ellH lam*(halfExp x)^2/
        (1+q lam*(halfExp x)^2)^2) := add_le_add le_rfl hmul
    _=(ellH lam/q lam)*elimH0 (q lam) (halfExp x)/
        (elimS (q lam) (halfExp x))^2 := by
      unfold elimH0 elimS
      field_simp [hq.ne',hu.ne',hs.ne'] <;> ring

theorem hasDerivAt_unit_x {lam : ℝ} (hlam : 0<lam) (x p : ℝ) :
    HasDerivAt (fun z => unitExpression lam z 0 p) (unitXSlope lam x p) x := by
  have he := hasDerivAt_E hlam x
  have hf := hasDerivAt_f hlam x
  have hh := ((hasDerivAt_id x).mul
    ((he.const_mul (p/b p)).const_sub (K lam p))).add ((hf.const_mul (1-a lam)).sub_const (f lam 0))
  convert hh using 1
  · funext z
    simp only [unitExpression,Pi_zero,mul_zero,add_zero,
      Pi.add_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
    ring
  · simp only [unitXSlope,eSlope,id_eq]
    ring

/-- A scalar order step used by both actual branches, with all signs visible. -/
theorem xSlope_lower_of_bounds {K k r rbar e ebar loss : ℝ}
    (hK : k≤K) (hr : r≤rbar) (hr0 : 0≤rbar) (he : e≤ebar) (he0 : 0≤e) :
    k-rbar*ebar-loss≤K-r*e-loss := by
  have hm := mul_le_mul hr he he0 hr0
  linarith

theorem interior_unitXSlope_lower {lam x p : ℝ} (hlam : ActivityDomain lam)
    (hx : 0≤x) (hp : 0<p) (hpq : p<q lam) (hp0 : pZero (q lam)≤p) :
    interiorSlopeLower (q lam) (halfExp x) (delta (q lam))≤unitXSlope lam x p := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hs := e_combination_upper hlam hx
  have hr := interior_p_div_b_upper (q_domain hlam) hp hpq hp0
  have hh := xSlope_lower_of_bounds (interior_K_lower hlam hp hpq) hr
    (by positivity : 0≤(2+q lam)/(2*(1+q lam))) hs (e_combination_nonneg hlam hx)
      (loss := (1-a lam)*messageAt lam x)
  rw [messageAt_halfExp hl] at hh
  have hS : 0<elimS (q lam) (halfExp x) := (elimination_factors_pos (q_domain hlam) _).1
  have hT : 0<elimT (q lam) (halfExp x) := (elimination_factors_pos (q_domain hlam) _).2.1
  convert hh using 1 <;>
    simp only [interiorSlopeLower,unitXSlope,ellH,rate,a_eq_aQ hl,messageAt_halfExp hl] <;>
    field_simp [hq.ne',hS.ne',hT.ne',show 1+q lam≠0 by positivity] <;> ring

theorem leaf_unitXSlope_lower {lam x : ℝ} (hlam : ActivityDomain lam) (hx : 0≤x) :
    leafSlopeLower (q lam) (halfExp x) (delta (q lam))≤unitXSlope lam x (q lam) := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hh := xSlope_lower_of_bounds (leaf_K_lower hlam)
    (p_div_b_upper hq (q_lt_one hl)) (by linarith [q_lt_one hl] : 0≤(2-q lam)/2)
    (e_combination_upper hlam hx) (e_combination_nonneg hlam hx)
    (loss := (1-a lam)*messageAt lam x)
  rw [messageAt_halfExp hl] at hh
  have hS : 0<elimS (q lam) (halfExp x) := (elimination_factors_pos (q_domain hlam) _).1
  have hT : 0<elimT (q lam) (halfExp x) := (elimination_factors_pos (q_domain hlam) _).2.1
  convert hh using 1 <;>
    simp only [leafSlopeLower,unitXSlope,ellH,rate,a_eq_aQ hl,messageAt_halfExp hl] <;>
    field_simp [hq.ne',hS.ne',hT.ne'] <;> ring

theorem interior_unitXSlope_pos {lam x p : ℝ} (hlam : ActivityDomain lam)
    (hx : 0≤x) (hp : 0<p) (hpq : p<q lam) (hp0 : pZero (q lam)≤p)
    (hI : 0<polyI (q lam) (halfExp x) (delta (q lam))) :
    0<unitXSlope lam x p := by
  have hden := (elimination_factors_pos (q_domain hlam) (halfExp x)).2.2.1
  have h := div_pos hI hden
  rw [←interiorSlope_clearing (q_domain hlam)] at h
  exact h.trans_le (interior_unitXSlope_lower hlam hx hp hpq hp0)

theorem leaf_unitXSlope_pos {lam x : ℝ} (hlam : ActivityDomain lam) (hx : 0≤x)
    (hJ : 0<polyJ (q lam) (halfExp x) (delta (q lam))) :
    0<unitXSlope lam x (q lam) := by
  have hden := (elimination_factors_pos (q_domain hlam) (halfExp x)).2.2.2
  have h := div_pos hJ hden
  rw [←leafSlope_clearing (q_domain hlam)] at h
  exact h.trans_le (leaf_unitXSlope_lower hlam hx)

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.b_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.b_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.p_div_b_upper
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.p_div_b_upper
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_p_div_b_upper
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_p_div_b_upper
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_K_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_K_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leaf_K_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leaf_K_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.messageAt_halfExp
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.messageAt_halfExp
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.e_combination_nonneg
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.e_combination_nonneg
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.e_combination_upper
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.e_combination_upper
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_unit_x
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_unit_x
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.xSlope_lower_of_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.xSlope_lower_of_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_unitXSlope_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_unitXSlope_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leaf_unitXSlope_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leaf_unitXSlope_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_unitXSlope_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_unitXSlope_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leaf_unitXSlope_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leaf_unitXSlope_pos
