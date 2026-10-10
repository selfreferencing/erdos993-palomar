module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceDefs

/-!
Rational part of current Lemma 4.2. Closed low and
high extensions are separate statements; `rate` takes the high value at3/7.
All proofs are generic algebra/inequalities. No old rate table or numerical
certificate family is imported. The explicit cleared factorizations replace
some of the paper's derivative-sign arguments and must be disclosed as such.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real

theorem rate_den_pos {q : ℝ} (hq : QDomain q) : 0 < (1+q)*(2-q) := by
  have hq0 : 0 < q := by linarith [hq.1]
  have hq1 : q < 1 := by linarith [hq.2]
  exact mul_pos (by linarith) (by linarith)

theorem rate_den_le (q : ℝ) : (1+q)*(2-q) ≤ 9/4 := by
  nlinarith [sq_nonneg (q-1/2)]

theorem aQ_bounds {q : ℝ} (hq : QDomain q) :
    7/300 ≤ aQ q ∧ aQ q ≤ 31/300 ∧ aQ q < 11/100 := by
  have hd : 0 < 100*(1-q) := by linarith [hq.2]
  unfold aQ
  refine ⟨(le_div_iff₀ hd).2 ?_, (div_le_iff₀ hd).2 ?_, (div_lt_iff₀ hd).2 ?_⟩ <;>
    linarith [hq.1, hq.2]

theorem aQ_le_twentieth {q : ℝ} (hq : QDomain q) (hqh : q ≤ 1/2) : aQ q ≤ 1/20 := by
  unfold aQ
  apply (div_le_iff₀ (by linarith [hq.2] : 0 < 100*(1-q))).2
  linarith

theorem rateR_ge_nine_thirty_fifths {q : ℝ} (hq : QDomain q) : 9/35 ≤ rateR q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hs : q^2 ≤ (7/10 : ℝ)^2 := pow_le_pow_left₀ hq0 hq.2 2
  have hf : 0 ≤ (4*q-1)*(-35*q^2+11*q+18) := by
    apply mul_nonneg (by linarith [hq.1])
    nlinarith
  have hid : 35*(2*q*(1+2*q)*(1-q))-9*((1+q)*(2-q)) =
      (4*q-1)*(-35*q^2+11*q+18) := by ring
  unfold rateR
  apply (le_div_iff₀ (rate_den_pos hq)).2
  nlinarith

theorem rateR_lt_nineteen_fortieths {q : ℝ} (hq : QDomain q) : rateR q < 19/40 := by
  let r : ℝ := (sqrt 5-1)/2
  have hs0 : 0 ≤ sqrt (5 : ℝ) := sqrt_nonneg _
  have hs2 : (sqrt (5 : ℝ))^2 = 5 := sq_sqrt (by norm_num)
  have hr : 0 < r := by dsimp [r]; nlinarith
  have hr2 : r^2 = 1-r := by dsimp [r]; nlinarith
  have hr3 : r^3 = 2*r-1 := by
    calc
      r^3 = r*r^2 := by ring
      _ = r*(1-r) := by rw [hr2]
      _ = 2*r-1 := by nlinarith [hr2]
  have hid : (4*r-2)*((1+q)*(2-q))-2*q*(1+2*q)*(1-q) =
      4*(q-r)^2*(q+r) := by
    linear_combination 4*q*hr2-4*hr3
  have hq0 : 0 < q := by linarith [hq.1]
  have hn : 0 ≤ (4*r-2)*((1+q)*(2-q))-2*q*(1+2*q)*(1-q) := by
    rw [hid]
    positivity
  have hu : rateR q ≤ 4*r-2 := by
    unfold rateR
    apply (div_le_iff₀ (rate_den_pos hq)).2
    linarith
  have hs : sqrt (5 : ℝ) < 179/80 := by nlinarith
  have hrb : 4*r-2 < 19/40 := by dsimp [r]; linarith
  exact hu.trans_lt hrb

theorem rateR_sub_q {q : ℝ} (hq : QDomain q) :
    rateR q-q = q^2*(1-3*q)/((1+q)*(2-q)) := by
  have hd := (rate_den_pos hq).ne'
  apply (eq_div_iff hd).2
  unfold rateR
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

/-- The low extension is valid on the closed interval, including q=3/7. -/
theorem lowRate_le_q {q : ℝ} (hq : LowClosedDomain q) : lowRate q ≤ q := by
  have hQ : QDomain q := ⟨hq.1, by linarith [hq.2]⟩
  have hd := rate_den_pos hQ
  by_cases hh : q ≤ 1/3
  · have hq0 : 0 ≤ q := by linarith [hq.1]
    have hs : (1/4 : ℝ)^2 ≤ q^2 := pow_le_pow_left₀ (by norm_num) hq.1 2
    have hf : 0 ≤ (4*q-1)*(105*q^2-9*q-2) := by
      apply mul_nonneg (by linarith [hq.1])
      nlinarith
    have hid : (1+q)*(2-q)-140*q^2*(1-3*q) =
        (4*q-1)*(105*q^2-9*q-2) := by ring
    have hg : rateR q-q ≤ 1/140 := by
      rw [rateR_sub_q hQ]
      apply (div_le_iff₀ hd).2
      nlinarith
    dsimp [lowRate]
    linarith
  · have hg : rateR q-q ≤ 0 := by
      rw [rateR_sub_q hQ]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)) hd.le
    dsimp [lowRate]
    linarith

theorem high_rate_gap {q : ℝ} (hq : HighDomain q) : 8/343 ≤ q-rateR q := by
  have hQ : QDomain q := ⟨by linarith [hq.1], hq.2⟩
  have hd := rate_den_pos hQ
  have hs : (3/7 : ℝ)^2 ≤ q^2 := pow_le_pow_left₀ (by norm_num) hq.1 2
  have hl : (2/7 : ℝ) ≤ 3*q-1 := by linarith [hq.1]
  have hm : (3/7 : ℝ)^2*(2/7) ≤ q^2*(3*q-1) :=
    mul_le_mul hs hl (by norm_num) (sq_nonneg _)
  have he : q-rateR q = q^2*(3*q-1)/((1+q)*(2-q)) := by
    have hh := rateR_sub_q hQ
    calc
      q-rateR q = -(rateR q-q) := by ring
      _ = -(q^2*(1-3*q)/((1+q)*(2-q))) := by rw [hh]
      _ = q^2*(3*q-1)/((1+q)*(2-q)) := by ring
  rw [he]
  apply (le_div_iff₀ hd).2
  nlinarith [rate_den_le q]

theorem highRate_le_q {q : ℝ} (hq : HighDomain q) : highRate q ≤ q := by
  have hh := high_rate_gap hq
  dsimp [highRate]
  linarith

theorem lowRate_bounds {q : ℝ} (hq : LowClosedDomain q) :
    0 < lowRate q ∧ lowRate q ≤ q ∧ lowRate q < 12/25 := by
  have hQ : QDomain q := ⟨hq.1, by linarith [hq.2]⟩
  have hl := rateR_ge_nine_thirty_fifths hQ
  have hu := rateR_lt_nineteen_fortieths hQ
  refine ⟨?_, lowRate_le_q hq, ?_⟩ <;> dsimp [lowRate] <;> linarith

theorem highRate_bounds {q : ℝ} (hq : HighDomain q) :
    0 < highRate q ∧ highRate q ≤ q ∧ highRate q < 12/25 := by
  have hQ : QDomain q := ⟨by linarith [hq.1], hq.2⟩
  have hl := rateR_ge_nine_thirty_fifths hQ
  have hu := rateR_lt_nineteen_fortieths hQ
  refine ⟨?_, highRate_le_q hq, ?_⟩ <;> dsimp [highRate] <;> linarith

theorem rate_bounds {q : ℝ} (hq : QDomain q) :
    0 < rate q ∧ rate q ≤ q ∧ rate q < 12/25 := by
  by_cases hh : q < 3/7
  · rw [rate_low hh]
    exact lowRate_bounds ⟨hq.1, hh.le⟩
  · rw [rate_high (le_of_not_gt hh)]
    exact highRate_bounds ⟨le_of_not_gt hh, hq.2⟩

theorem low_budget_factor {q : ℝ} (hq : QDomain q) (hqh : q ≤ 1/2) :
    9/8 ≤ (1-q)*(1+q)^2 := by
  have hf : 0 ≤ (1/2-q)*(q^2+3*q/2-1/4) := by
    apply mul_nonneg (by linarith)
    nlinarith [sq_nonneg q, hq.1]
  have hid : (1-q)*(1+q)^2-9/8 = (1/2-q)*(q^2+3*q/2-1/4) := by ring
  nlinarith

theorem high_budget_factor {q : ℝ} (hq : QDomain q) (hqh : 1/2 ≤ q) :
    9/16 ≤ q*(1-q)*(1+q)^2 := by
  have hq0 : 0 ≤ q := by linarith
  have hs2 : q^2 ≤ (7/10 : ℝ)^2 := pow_le_pow_left₀ hq0 hq.2 2
  have hs3 : q^3 ≤ (7/10 : ℝ)^3 := pow_le_pow_left₀ hq0 hq.2 3
  have hf : 0 ≤ (q-1/2)*(-q^3-3*q^2/2+q/4+9/8) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hid : q*(1-q)*(1+q)^2-9/16 =
      (q-1/2)*(-q^3-3*q^2/2+q/4+9/8) := by ring
  nlinarith

theorem rate_budget {q : ℝ} (hq : QDomain q) :
    rate q ≤ (1-aQ q)*q*(1-q)*(1+q)^2 := by
  have hr := rate_bounds hq
  have ha := aQ_bounds hq
  have hq0 : 0 < q := by linarith [hq.1]
  by_cases hh : q ≤ 1/2
  · have haf : 19/20 ≤ 1-aQ q := by linarith [aQ_le_twentieth hq hh]
    have hg := low_budget_factor hq hh
    have hm : (19/20 : ℝ)*(9/8) ≤ (1-aQ q)*((1-q)*(1+q)^2) :=
      mul_le_mul haf hg (by norm_num) (by linarith [ha.2.2])
    have h1 : 1 ≤ (1-aQ q)*((1-q)*(1+q)^2) := by linarith
    have hqf := mul_le_mul_of_nonneg_left h1 hq0.le
    calc
      rate q ≤ q := hr.2.1
      _ ≤ (1-aQ q)*q*(1-q)*(1+q)^2 := by nlinarith [hqf]
  · have haf : 89/100 ≤ 1-aQ q := by linarith [ha.2.2]
    have hg := high_budget_factor hq (le_of_lt (lt_of_not_ge hh))
    have hm : (89/100 : ℝ)*(9/16) ≤ (1-aQ q)*(q*(1-q)*(1+q)^2) :=
      mul_le_mul haf hg (by norm_num) (by linarith [ha.2.2])
    nlinarith [hr.2.2]

/-- The actual activity-parametrized rational conclusions of Lemma4.2. -/
theorem activity_rate_bounds {lam : ℝ} (h : ActivityDomain lam) :
    0 < ellH lam ∧ ellH lam ≤ q lam ∧ ellH lam < 12/25 ∧
      ellH lam ≤ (1-a lam)*q lam*(1-q lam)*(1+q lam)^2 := by
  have hh := rate_bounds (q_domain h)
  have hb := rate_budget (q_domain h)
  rw [← a_eq_aQ (by linarith [h.1] : 0 < lam)] at hb
  exact ⟨hh.1, hh.2.1, hh.2.2, hb⟩

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_den_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_den_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_den_le
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_den_le
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.aQ_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.aQ_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.aQ_le_twentieth
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.aQ_le_twentieth
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_ge_nine_thirty_fifths
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_ge_nine_thirty_fifths
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_lt_nineteen_fortieths
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_lt_nineteen_fortieths
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_sub_q
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rateR_sub_q
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.lowRate_le_q
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.lowRate_le_q
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.high_rate_gap
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.high_rate_gap
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.highRate_le_q
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.highRate_le_q
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.lowRate_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.lowRate_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.highRate_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.highRate_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.low_budget_factor
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.low_budget_factor
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.high_budget_factor
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.high_budget_factor
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_budget
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_budget
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.activity_rate_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.activity_rate_bounds
