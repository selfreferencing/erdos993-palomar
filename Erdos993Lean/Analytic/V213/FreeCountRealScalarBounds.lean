module

public import Erdos993Lean.Analytic.V213.FreeCountRealLogEnvelopes
public import Erdos993Lean.Analytic.V213.FreeCountVarianceDefs

/-!
Current T1 (*) and (16). The first logarithm
inequalities are proved by derivative comparison. The two derivative signs
on 0<p<=7/10 use the same positive artanh series as the paper, with an
explicit polynomial factorization in w=p/(2-p), instead of an unproved
concavity assumption. No finite packet, cap comparison, or graph theorem is
consumed. The raw quotient scalarH is only asserted on 0<p<1: its Lean value
at zero is not the paper's continuous extension h0(0)=1.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

open Real Set Finset

theorem hasDerivAt_log_lower_gap {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun x : ℝ => log (1+x) - 2*x/(2+x))
      (z^2/((1+z)*(2+z)^2)) z := by
  have h1 : 1+z ≠ 0 := by positivity
  have h2 : 2+z ≠ 0 := by positivity
  convert (((hasDerivAt_id z).const_add 1).log h1).sub
    (((hasDerivAt_id z).const_mul 2).div ((hasDerivAt_id z).const_add 2) h2) using 1
  all_goals
    (try funext t) <;> dsimp <;> field_simp [h1, h2] <;> ring

theorem hasDerivAt_log_upper_gap {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun x : ℝ => x*(2+x)/(2*(1+x)) - log (1+x))
      (z^2/(2*(1+z)^2)) z := by
  have h1 : 1+z ≠ 0 := by positivity
  have h2 : 2*(1+z) ≠ 0 := by positivity
  convert (((hasDerivAt_id z).mul ((hasDerivAt_id z).const_add 2)).div
    (((hasDerivAt_id z).const_add 1).const_mul 2) h2).sub
    (((hasDerivAt_id z).const_add 1).log h1) using 1
  all_goals
    (try funext t) <;> dsimp <;> field_simp [h1] <;> ring

/-- Both elementary inequalities in the actual display (*), including z=0. -/
theorem log_star {z : ℝ} (hz : 0 ≤ z) :
    2*z/(2+z) ≤ log (1+z) ∧ log (1+z) ≤ z*(2+z)/(2*(1+z)) := by
  have hl := zero_le_value_of_nonneg_deriv hz (f := fun x => log (1+x)-2*x/(2+x))
    (f' := fun x => x^2/((1+x)*(2+x)^2)) (by norm_num)
    (fun x hx => hasDerivAt_log_lower_gap hx.1)
    (fun x hx => by have hx0 : 0 ≤ x := hx.1; positivity)
  have hu := zero_le_value_of_nonneg_deriv hz
    (f := fun x => x*(2+x)/(2*(1+x))-log (1+x))
    (f' := fun x => x^2/(2*(1+x)^2)) (by norm_num)
    (fun x hx => hasDerivAt_log_upper_gap hx.1)
    (fun x hx => by have hx0 : 0 ≤ x := hx.1; positivity)
  constructor <;> linarith

noncomputable def scalarLog (p : ℝ) : ℝ := -log (1-p)
noncomputable def scalarH (p : ℝ) : ℝ := p/scalarLog p

theorem scalarLog_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < scalarLog p := by
  unfold scalarLog
  exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

theorem log_odds_eq {p : ℝ} (hp1 : p < 1) :
    log (1+p/(1-p)) = scalarLog p := by
  have hn : 1-p ≠ 0 := by linarith
  have hi : 1+p/(1-p) = 1/(1-p) := by field_simp [hn] <;> ring
  rw [hi, Real.log_div (by norm_num) hn]
  simp [scalarLog]

theorem scalarLog_upper {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    scalarLog p ≤ p/(1-p) := by
  have hm : 0 < 1-p := by linarith
  have hz : 0 < 1+p/(1-p) := by positivity
  have hh := Real.log_le_sub_one_of_pos hz
  rw [log_odds_eq hp1] at hh
  linarith

theorem scalarLog_lower {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    2*p/(2-p) ≤ scalarLog p := by
  have hz : 0 ≤ p/(1-p) := div_nonneg hp.le (by linarith)
  have hh := (log_star hz).1
  rw [log_odds_eq hp1] at hh
  have hn : 1-p ≠ 0 := by linarith
  have hn2 : 2-p ≠ 0 := by linarith
  have hnd : 2+p/(1-p) ≠ 0 := by positivity
  have hid : 2*(p/(1-p))/(2+p/(1-p)) = 2*p/(2-p) := by
    apply (div_eq_div_iff hnd hn2).2
    field_simp [hn] <;> ring
  rwa [hid] at hh

/-- The first pair of inequalities of (16), with the nonzero domain explicit. -/
theorem scalarH_bounds {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    1-p ≤ scalarH p ∧ scalarH p ≤ 1-p/2 := by
  have hb := scalarLog_pos hp hp1
  have hl := scalarLog_lower hp hp1
  have hu := scalarLog_upper hp hp1
  have hu' : scalarLog p*(1-p) ≤ p :=
    (le_div_iff₀ (by linarith : 0 < 1-p)).mp hu
  have hl' : 2*p ≤ scalarLog p*(2-p) :=
    (div_le_iff₀ (by linarith : 0 < 2-p)).mp hl
  unfold scalarH
  constructor
  · apply (le_div_iff₀ hb).2
    nlinarith
  · apply (div_le_iff₀ hb).2
    nlinarith

theorem hasDerivAt_scalarLog {p : ℝ} (hp1 : p < 1) :
    HasDerivAt scalarLog (1/(1-p)) p := by
  have hn : 1-p ≠ 0 := by linarith
  convert (((hasDerivAt_id p).const_sub 1).log hn).neg using 1
  all_goals
    (try funext t) <;> dsimp [scalarLog] <;> ring

theorem hasDerivAt_scalarH {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt scalarH ((scalarLog p-p/(1-p))/(scalarLog p)^2) p := by
  have hb := (scalarLog_pos hp hp1).ne'
  convert (hasDerivAt_id p).div (hasDerivAt_scalarLog hp1) hb using 1
  all_goals
    (try funext t) <;> (try dsimp [scalarH]) <;> ring

theorem scalarH_deriv_nonpos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    deriv scalarH p ≤ 0 := by
  rw [(hasDerivAt_scalarH hp hp1).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (scalarLog_upper hp hp1))
    (sq_nonneg _)

theorem scalarH_antitone : AntitoneOn scalarH (Ioo 0 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 1)
    (f' := fun p => (scalarLog p-p/(1-p))/(scalarLog p)^2)
  · intro p hp
    exact (hasDerivAt_scalarH hp.1 hp.2).continuousAt.continuousWithinAt
  · intro p hp
    have hh := interior_subset hp
    exact (hasDerivAt_scalarH hh.1 hh.2).hasDerivWithinAt
  · intro p hp
    have hh := interior_subset hp
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (scalarLog_upper hh.1 hh.2)) (sq_nonneg _)

/-- The named endpoint lower bound used in the printed scalar discussion. -/
theorem log_ten_thirds_gt_seven_sixths : (7/6 : ℝ) < log (10/3) := by
  have hh := Real.sum_range_le_log_div (x := (7/13 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hh
  linarith

/-- The first two positive artanh terms, in the actual probability coordinate. -/
theorem scalarLog_two_terms {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    2*(p/(2-p)+(p/(2-p))^3/3) ≤ scalarLog p := by
  have h2 : 0 < 2-p := by linarith
  have hw0 : 0 ≤ p/(2-p) := div_nonneg hp.le h2.le
  have hw1 : p/(2-p) < 1 := (div_lt_one h2).2 (by linarith)
  have hi : (1+p/(2-p))/(1-p/(2-p)) = 1/(1-p) := by
    apply (div_eq_div_iff (sub_pos.mpr hw1).ne' (sub_pos.mpr hp1).ne').2
    field_simp [h2.ne'] <;> ring
  have hh := Real.sum_range_le_log_div hw0 hw1 2
  rw [hi, Real.log_div (by norm_num) (ne_of_gt (show 0 < 1-p by linarith))] at hh
  norm_num [Finset.sum_range_succ] at hh
  dsimp [scalarLog]
  linarith

theorem scalarH_deriv_gt_neg_one {p : ℝ} (hp : 0 < p) (hp7 : p ≤ 7/10) :
    -1 < deriv scalarH p := by
  have hp1 : p < 1 := by linarith
  have h2 : 0 < 2-p := by linarith
  let w := p/(2-p)
  let b := 2*(w+w^3/3)
  have hw : 0 < w := div_pos hp h2
  have hw7 : w ≤ 7/13 := (div_le_iff₀ h2).2 (by linarith)
  have hw1 : w < 1 := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbl : b ≤ scalarLog p := scalarLog_two_terms hp hp1
  have hpow := pow_le_pow_left₀ hb hbl 2
  have hl := scalarLog_pos hp hp1
  have hz : p/(1-p) = 2*w/(1-w) := by
    apply (div_eq_div_iff (ne_of_gt (show 0 < 1-p by linarith))
      (ne_of_gt (show 0 < 1-w by linarith))).2
    dsimp [w]
    field_simp [h2.ne'] <;> ring
  have hbracket : 0 < 9-15*w+3*w^2*(3-4*w)+2*w^4*(1-w) := by
    have ha : 0 < 9-15*w := by linarith
    have hb0 : 0 ≤ 3*w^2*(3-4*w) :=
      mul_nonneg (by positivity) (by linarith)
    have hc0 : 0 ≤ 2*w^4*(1-w) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hid : (1-w)*(b^2+b-2*w/(1-w)) =
      (2/9)*w^2*(9-15*w+3*w^2*(3-4*w)+2*w^4*(1-w)) := by
    dsimp [b]
    field_simp [ne_of_gt (show 0 < 1-w by linarith)] <;> ring
  have hp0 : 0 < (1-w)*(b^2+b-2*w/(1-w)) := by rw [hid]; positivity
  have hb0 : 0 < b^2+b-2*w/(1-w) := by nlinarith
  have hnum : 0 < (scalarLog p)^2+scalarLog p-p/(1-p) := by rw [hz]; linarith
  rw [(hasDerivAt_scalarH hp hp1).deriv]
  apply (lt_div_iff₀ (sq_pos_of_pos hl)).2
  nlinarith

/-- The polynomial sign used for the last inequality of (16). -/
theorem two_term_monotonicity_cubic {w : ℝ} (hw : 0 ≤ w) (hw7 : w ≤ 7/13) :
    0 < 3-6*w+2*w^2-2*w^3 := by
  have hn : 0 ≤ ((7/13 : ℝ)-w) *
      (6-2*((7/13 : ℝ)+w)+2*((7/13 : ℝ)^2+(7/13)*w+w^2)) := by
    apply mul_nonneg (by linarith)
    nlinarith [sq_nonneg w]
  have hid : 3-6*w+2*w^2-2*w^3 = (81/2197 : ℝ) +
      ((7/13 : ℝ)-w) *
        (6-2*((7/13 : ℝ)+w)+2*((7/13 : ℝ)^2+(7/13)*w+w^2)) := by ring
  rw [hid]
  linarith

theorem square_log_derivative_numerator_pos {p : ℝ} (hp : 0 < p) (hp7 : p ≤ 7/10) :
    0 < 2*(1-p)*scalarLog p-p := by
  have hp1 : p < 1 := by linarith
  have h2 : 0 < 2-p := by linarith
  let w := p/(2-p)
  let b := 2*(w+w^3/3)
  have hw : 0 < w := div_pos hp h2
  have hw7 : w ≤ 7/13 := (div_le_iff₀ h2).2 (by linarith)
  have hbl : b ≤ scalarLog p := scalarLog_two_terms hp hp1
  have hcross : p = 2*w/(1+w) := by
    apply (eq_div_iff (ne_of_gt (show 0 < 1+w by linarith))).2
    dsimp [w]
    field_simp [h2.ne'] <;> ring
  have hid : (1+w)*(2*(1-p)*b-p) =
      (2/3)*w*(3-6*w+2*w^2-2*w^3) := by
    rw [hcross]
    dsimp [b]
    field_simp [ne_of_gt (show 0 < 1+w by linarith)] <;> ring
  have hprod : 0 < (1+w)*(2*(1-p)*b-p) := by
    rw [hid]
    exact mul_pos (mul_pos (by norm_num) hw) (two_term_monotonicity_cubic hw.le hw7)
  have hlow : 0 < 2*(1-p)*b-p := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hbl (by linarith : 0 ≤ 2*(1-p))
  linarith

theorem hasDerivAt_square_over_log {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun s => s^2/scalarLog s)
      (p*(2*(1-p)*scalarLog p-p)/((1-p)*(scalarLog p)^2)) p := by
  have hb := (scalarLog_pos hp hp1).ne'
  have h1 : 1-p ≠ 0 := by linarith
  convert (hasDerivAt_pow 2 p).div (hasDerivAt_scalarLog hp1) hb using 1
  · field_simp [hb, h1] <;> ring

theorem square_over_log_monotone :
    MonotoneOn (fun p : ℝ => p^2/scalarLog p) (Set.Ioc 0 (7/10)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 (7/10))
    (f' := fun p => p*(2*(1-p)*scalarLog p-p)/((1-p)*(scalarLog p)^2))
  · intro p hp
    exact (hasDerivAt_square_over_log hp.1 (by linarith [hp.2])).continuousAt.continuousWithinAt
  · intro p hp
    have hh := interior_subset hp
    exact (hasDerivAt_square_over_log hh.1 (by linarith [hh.2])).hasDerivWithinAt
  · intro p hp
    have hh := interior_subset hp
    have hnum := square_log_derivative_numerator_pos hh.1 hh.2
    have hp : 0 < p := hh.1
    have hm : 0 < 1-p := by linarith [hh.2]
    have hl := scalarLog_pos hh.1 (by linarith [hh.2])
    positivity

theorem message_scalarH_bounds {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    1-message lam t ≤ message lam t/logMass lam t ∧
      message lam t/logMass lam t ≤ 1-message lam t/2 := by
  have hh := scalarH_bounds (message_pos hlam t) (message_lt_one hlam t)
  simpa [scalarH, scalarLog, logMass_eq_neg_log hlam t] using hh

theorem message_le_q {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) : message lam t ≤ q lam := by
  rw [message_eq_exp_quotient hlam]
  unfold q
  apply (div_le_div_iff₀ (by positivity : 0 < exp t+lam) (by positivity : 0 < 1+lam)).2
  have he : 1 ≤ exp t := Real.one_le_exp_iff.mpr ht
  nlinarith

/-- Literal last inequality of (16), now for the actual parent/child definitions. -/
theorem message_square_over_logMass_le {lam t : ℝ} (hlam : 0 < lam)
    (hlam7 : lam ≤ 7/3) (ht : 0 ≤ t) :
    message lam t ^ 2/logMass lam t ≤ q lam ^ 2/logActivity lam := by
  have hq7 : q lam ≤ 7/10 := by
    unfold q
    apply (div_le_iff₀ (by positivity : 0 < 1+lam)).2
    linarith
  have hmq := message_le_q hlam ht
  have hh := square_over_log_monotone
    (show message lam t ∈ Set.Ioc 0 (7/10) from ⟨message_pos hlam t, hmq.trans hq7⟩)
    (show q lam ∈ Set.Ioc 0 (7/10) from ⟨q_pos hlam, hq7⟩) hmq
  have htlog : scalarLog (message lam t) = logMass lam t :=
    (logMass_eq_neg_log hlam t).symm
  have hqlog : scalarLog (q lam) = logActivity lam := by
    simpa [scalarLog] using (logMass_eq_neg_log hlam 0).symm
  simpa [htlog, hqlog] using hh

end Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_log_lower_gap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_log_lower_gap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_log_upper_gap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_log_upper_gap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_star
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_star
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_odds_eq
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_odds_eq
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_scalarLog
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_scalarLog
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_scalarH
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_scalarH
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_deriv_nonpos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_deriv_nonpos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_antitone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_antitone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_ten_thirds_gt_seven_sixths
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_ten_thirds_gt_seven_sixths
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_two_terms
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_two_terms
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_deriv_gt_neg_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_deriv_gt_neg_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.two_term_monotonicity_cubic
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.two_term_monotonicity_cubic
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.square_log_derivative_numerator_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.square_log_derivative_numerator_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_square_over_log
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_square_over_log
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.square_over_log_monotone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.square_over_log_monotone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.message_scalarH_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.message_scalarH_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.message_le_q
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.message_le_q
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.message_square_over_logMass_le
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.message_square_over_logMass_le
