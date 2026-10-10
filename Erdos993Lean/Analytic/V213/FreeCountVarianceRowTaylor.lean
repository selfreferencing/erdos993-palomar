module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowBounds

/-!
Interpretation of the actual A-row midpoint worksheet.
This proves the basepoint, slope and curvature input bounds from E/B point
enclosures, then uses the continuous analytic cell lemma. The positive M0
comparison is a separate input; aRowOK does not contain it. No finite record
or completed AC comparison is assumed or evaluated here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Set Erdos993Lean.ExactComparisons.F3All

private theorem quotient_order {a b c d : ℝ}
    (ha : 0≤a) (hab : a≤b) (hc : 0<c) (hcd : c≤d) : a/d≤b/c := by
  apply (div_le_div_iff₀ (hc.trans_le hcd) hc).2
  exact (mul_le_mul_of_nonneg_right hab hc.le).trans
    (mul_le_mul_of_nonneg_left hcd (ha.trans hab))

theorem T0_exp_form {D lam : ℝ} (hlam : 0<lam) (y : ℝ) :
    T0 D lam y = ((1+lam)/(exp y+lam)-1)/D+
      (7/12:ℝ)*y*exp y/((1+lam)*logActivity lam) := by
  have h1 : 1+lam≠0 := ne_of_gt (by linarith)
  have he : exp y+lam≠0 := ne_of_gt (add_pos (exp_pos y) hlam)
  have hi : message lam y/q lam=(1+lam)/(exp y+lam) := by
    rw [message_eq_exp_quotient hlam]
    unfold q
    field_simp [hlam.ne', h1, he]
    <;> ring
  unfold T0
  rw [hi]
  ring

theorem T0Slope_exp_form {D lam : ℝ} (hlam : 0<lam) (y : ℝ) :
    T0Slope D lam y = -(1+lam)*exp y/(D*(exp y+lam)^2)+
      (7/12:ℝ)*(1+y)*exp y/((1+lam)*logActivity lam) := by
  have h1 : 1+lam≠0 := ne_of_gt (by linarith)
  have he : exp y+lam≠0 := ne_of_gt (add_pos (exp_pos y) hlam)
  have hi : message lam y*(1-message lam y)/q lam=
      (1+lam)*exp y/(exp y+lam)^2 := by
    rw [message_eq_exp_quotient hlam]
    unfold q
    field_simp [hlam.ne', h1, he]
    <;> ring
  calc
    T0Slope D lam y = -(message lam y*(1-message lam y)/q lam)/D+
        (7/12:ℝ)*(1+y)*exp y/((1+lam)*logActivity lam) := by
      unfold T0Slope
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hi]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- A positive weight preserves the exp/beta endpoint enclosure. -/
theorem exp_beta_weight_bounds {lam y elo ehi blo bhi weight : ℝ}
    (hlam : 0<lam) (helo : 0<elo) (hblo : 0<blo) (hw : 0≤weight)
    (hel : elo≤exp y) (heu : exp y≤ehi)
    (hbl : blo≤logActivity lam) (hbu : logActivity lam≤bhi) :
    weight*elo/((1+lam)*bhi) ≤ weight*exp y/((1+lam)*logActivity lam) ∧
    weight*exp y/((1+lam)*logActivity lam) ≤ weight*ehi/((1+lam)*blo) := by
  have h1 : 0<1+lam := by linarith
  have hb := logActivity_pos hlam
  constructor
  · exact quotient_order (mul_nonneg hw helo.le)
      (mul_le_mul_of_nonneg_left hel hw) (mul_pos h1 hb)
      (mul_le_mul_of_nonneg_left hbu h1.le)
  · exact quotient_order (mul_nonneg hw (exp_pos y).le)
      (mul_le_mul_of_nonneg_left heu hw) (mul_pos h1 hblo)
      (mul_le_mul_of_nonneg_left hbl h1.le)

/-- The negative derivative term reverses both independent positive
quotient bounds. This avoids any sign change hidden in a denominator step. -/
theorem negative_exp_quotient_bounds {D lam y elo ehi : ℝ}
    (hD : 0<D) (hlam : 0<lam) (helo : 0<elo)
    (hel : elo≤exp y) (heu : exp y≤ehi) :
    -(1+lam)*ehi/(D*(elo+lam)^2) ≤ -(1+lam)*exp y/(D*(exp y+lam)^2) ∧
    -(1+lam)*exp y/(D*(exp y+lam)^2) ≤ -(1+lam)*elo/(D*(ehi+lam)^2) := by
  have h1 : 0<1+lam := by linarith
  have hlo : 0<elo+lam := add_pos helo hlam
  have hex : 0<exp y+lam := add_pos (exp_pos y) hlam
  have hhi : 0<ehi+lam := hex.trans_le (by linarith)
  have hslo : (elo+lam)^2≤(exp y+lam)^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hel) (add_pos hlo hex).le
    nlinarith only [hh]
  have hshi : (exp y+lam)^2≤(ehi+lam)^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr heu) (add_pos hex hhi).le
    nlinarith only [hh]
  have hupper := quotient_order (mul_nonneg h1.le (exp_pos y).le)
    (mul_le_mul_of_nonneg_left heu h1.le) (mul_pos hD (sq_pos_of_pos hlo))
    (mul_le_mul_of_nonneg_left hslo hD.le)
  have hlower := quotient_order (mul_nonneg h1.le helo.le)
    (mul_le_mul_of_nonneg_left hel h1.le) (mul_pos hD (sq_pos_of_pos hex))
    (mul_le_mul_of_nonneg_left hshi hD.le)
  constructor
  · simpa only [neg_mul, neg_div] using neg_le_neg hupper
  · simpa only [neg_mul, neg_div] using neg_le_neg hlower

theorem ARowFacts.T_base_lower {r : ARow} (hr : ARowFacts r) :
    cellTR r ≤ T0 (r.D : ℝ) (r.bd.b.lam : ℝ) (r.mid.y : ℝ) := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  have hb : (0:ℝ)<r.bd.b.lam := by exact_mod_cast hr.bd.activity_pos
  have hy := hr.midpoint_domain.2.1
  have he := hr.mid
  have hbeta := hr.bd.beta_bounds
  have hfrac := quotient_order (show 0≤1+(r.bd.b.lam : ℝ) by linarith)
    le_rfl (add_pos (exp_pos (r.mid.y : ℝ)) hb)
    (add_le_add he.2.2 (le_rfl : (r.bd.b.lam : ℝ) ≤ r.bd.b.lam))
  have hfirst := div_le_div_of_nonneg_right (sub_le_sub_right hfrac 1) hD.le
  have hsecond := (exp_beta_weight_bounds hb he.1 hbeta.1
    (show 0≤(7/12:ℝ)*(r.mid.y : ℝ) by positivity)
    he.2.1 he.2.2 hbeta.2.1.le hbeta.2.2.le).1
  rw [T0_exp_form hb]
  exact add_le_add hfirst hsecond

theorem ARowFacts.T_slope_bounds {r : ARow} (hr : ARowFacts r) :
    cellTMinusR r ≤ T0Slope (r.D : ℝ) (r.bd.b.lam : ℝ) (r.mid.y : ℝ) ∧
    T0Slope (r.D : ℝ) (r.bd.b.lam : ℝ) (r.mid.y : ℝ) ≤ cellTPlusR r := by
  have hD := (aRowOK_domain_real hr.checked).1
  have hb : (0:ℝ)<r.bd.b.lam := by exact_mod_cast hr.bd.activity_pos
  have hy := hr.midpoint_domain.2.1
  have he := hr.mid
  have hbeta := hr.bd.beta_bounds
  have hfirst := negative_exp_quotient_bounds hD hb he.1 he.2.1 he.2.2
  have hsecond := exp_beta_weight_bounds hb he.1 hbeta.1
    (show 0≤(7/12:ℝ)*(1+(r.mid.y : ℝ)) by positivity)
    he.2.1 he.2.2 hbeta.2.1.le hbeta.2.2.le
  rw [T0Slope_exp_form hb]
  exact ⟨add_le_add hfirst.1 hsecond.1, add_le_add hfirst.2 hsecond.2⟩

theorem ARowFacts.T_slope_abs {r : ARow} (hr : ARowFacts r) :
    |T0Slope (r.D : ℝ) (r.bd.b.lam : ℝ) (r.mid.y : ℝ)| ≤ cellJ0R r := by
  have h := hr.T_slope_bounds
  apply abs_le.mpr
  constructor
  · have hleft : -|cellTMinusR r|≤cellTMinusR r := neg_abs_le _
    have hmax : |cellTMinusR r|≤cellJ0R r := le_max_left _ _
    linarith only [h.1, hleft, hmax]
  · exact h.2.trans ((le_abs_self _).trans (le_max_right _ _))

theorem ARowFacts.M0_curvature_lower {r : ARow} (hr : ARowFacts r)
    (hD : (6/5:ℝ)≤r.D) {y : ℝ}
    (hy : y∈Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ)) :
    cellM0R r ≤ T0Curvature (r.D : ℝ) (r.bd.b.lam : ℝ) y := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD0, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  have hb : (0:ℝ)<r.bd.b.lam := by exact_mod_cast hr.bd.activity_pos
  have he := hr.ac.exp_bounds
  have hbeta := hr.bd.beta_bounds
  have hsecond := (exp_beta_weight_bounds hb he.1 hbeta.1
    (show 0≤(7/12:ℝ)*(2+(r.ac.e.y : ℝ)) by positivity)
    he.2.1 he.2.2 hbeta.2.1.le hbeta.2.2.le).1
  have hanalytic := T0Curvature_lower hD hb hb7 hc hy.1
  apply (sub_le_sub_right hsecond (1/10:ℝ)).trans
  convert hanalytic using 1 <;> ring

theorem cellPsiR_eq_quadraticLoss (r : ARow) :
    cellPsiR r = quadraticLoss (cellM0R r) (cellJ0R r) (cellWidthR r) := by
  rfl

theorem ARowFacts.T_lower {r : ARow} (hr : ARowFacts r)
    (hD : (6/5:ℝ)≤r.D) (hM : 0<cellM0R r) {lam y : ℝ}
    (hlam : lam∈Icc (r.ac.b.lam : ℝ) (r.bd.b.lam : ℝ))
    (hy : y∈Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ)) :
    cellTR r-cellPsiR r ≤ T0 (r.D : ℝ) lam y := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD0, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  rw [cellPsiR_eq_quadraticLoss]
  exact T0_ge_rectangle_cell_lower hD (by linarith) hb7 hc hlam hy
    hr.midpoint_domain.1 hM
    ((abs_nonneg (cellTMinusR r)).trans (le_max_left _ _))
    hr.midpoint_domain.2.2 (hr.midpoint_distance hy)
    (fun z hz => hr.M0_curvature_lower hD hz) hr.T_base_lower hr.T_slope_abs

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.T0_exp_form
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.T0_exp_form
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.T0Slope_exp_form
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.T0Slope_exp_form
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.exp_beta_weight_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.exp_beta_weight_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.negative_exp_quotient_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.negative_exp_quotient_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.T_base_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.T_base_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.T_slope_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.T_slope_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.T_slope_abs
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.T_slope_abs
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.M0_curvature_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.M0_curvature_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellPsiR_eq_quadraticLoss
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellPsiR_eq_quadraticLoss
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.T_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.T_lower
