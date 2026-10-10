module

public import Erdos993Lean.BCFG.ChartDefinitions

/-! Elementary closed-chart geometry and envelope signs.
No logarithm comparison, finite certificate or analytic clearing is assumed. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem row_constants_pos (r : AnalyticRow) :
    0 < theta r ∧ 0 < alpha r ∧ 0 < beta r ∧ 0 < kappa r := by
  cases r <;> norm_num [theta,alpha,beta,kappa]

theorem price_pos {r : AnalyticRow} {lam : ℝ} (hl : 0 < lam) :
    0 < price r lam := div_pos (row_constants_pos r).1 (by linarith)

theorem gamma_pos {r : AnalyticRow} {lam : ℝ} (hl : 0 < lam) :
    0 < gamma r lam := mul_pos (row_constants_pos r).2.2.2 hl

theorem occupation_bounds {lam omega : ℝ} (hl : 0 < lam) (hw : 0 < omega) :
    0 < occupation lam omega ∧ occupation lam omega < 1 := by
  have hd : 0 < 1+lam*omega := by positivity
  exact ⟨div_pos (mul_pos hl hw) hd,
    (div_lt_one hd).2 (by linarith)⟩

theorem occupation_le_q {lam omega : ℝ} (hl : 0 < lam)
    (hw : 0 < omega) (hw1 : omega ≤ 1) : occupation lam omega ≤ q lam := by
  have hd : 0 < 1+lam*omega := by positivity
  have h1 : 0 < 1+lam := by linarith
  apply (div_le_div_iff₀ hd h1).2
  have hx := mul_nonneg hl.le (sub_nonneg.mpr hw1)
  nlinarith

theorem rhoZero_bounds {lam omega : ℝ} (hl : 0 < lam) (hw : 0 < omega) :
    0 < rhoZero lam omega ∧ rhoZero lam omega < 1 := by
  have hn : 0 < 1+lam*omega := by positivity
  have hd : 0 < 1+lam+lam*omega := by positivity
  exact ⟨div_pos hn hd, (div_lt_one hd).2 (by linarith)⟩

theorem dCoeff_pos {lam omega : ℝ} (hl : 0 < lam) (hw : 0 < omega) :
    0 < dCoeff lam omega := sub_pos.mpr (occupation_bounds hl hw).2

theorem rCoeff_pos {r : AnalyticRow} {lam omega : ℝ}
    (hl : 0 < lam) (hw : 0 < omega) : 0 < rCoeff r lam omega :=
  div_pos (gamma_pos hl) (occupation_bounds hl hw).1

theorem one_sub_q (lam : ℝ) (h : 1+lam ≠ 0) : 1-q lam = 1/(1+lam) := by
  unfold q
  field_simp [h]
  ring

theorem lightOmega_bounds {lam x : ℝ} (hl : 0 < lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1/(1+lam) ≤ lightOmega lam x ∧ lightOmega lam x ≤ 1 := by
  have hq := q_bounds hl
  have hx := mul_le_mul_of_nonneg_left hx1 hq.1.le
  have hp : 0 ≤ q lam*x := mul_nonneg hq.1.le hx0
  have hi := one_sub_q lam (show 1+lam ≠ 0 by linarith)
  unfold lightOmega
  constructor <;> nlinarith

theorem lightOmega_pos {lam x : ℝ} (hl : 0 < lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 < lightOmega lam x :=
  (one_div_pos.mpr (show 0 < 1+lam by linarith)).trans_le
    (lightOmega_bounds hl hx0 hx1).1

theorem lightZ_bounds {lam x : ℝ} (hl : 0 < lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ lightZ lam x ∧ lightZ lam x < 1 := by
  have hw := lightOmega_pos hl hx0 hx1
  have hw1 := (lightOmega_bounds hl hx0 hx1).2
  have hd : 0 < 1+lightOmega lam x := by linarith
  exact ⟨div_nonneg (sub_nonneg.mpr hw1) hd.le,
    (div_lt_one hd).2 (by linarith)⟩

theorem lightUpper_nonneg {lam x : ℝ} (hl : 0 < lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ lightUpper lam x := by
  obtain ⟨hz0,hz1⟩ := lightZ_bounds hl hx0 hx1
  have hd : 0 < 1-(lightZ lam x)^2 := by
    have hh : 0 < (1-lightZ lam x)*(1+lightZ lam x) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  unfold lightUpper
  positivity

theorem heavyOmega_pos {r : AnalyticRow} {lam v : ℝ}
    (hl : 0 < lam) (hv : 0 < v) : 0 < heavyOmega r lam v := by
  unfold heavyOmega
  positivity

theorem heavyZ_bounds {v : ℝ} (hv0 : 1/2 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ heavyZ v ∧ heavyZ v ≤ 1/3 := by
  have hd : 0 < 1+v := by linarith
  exact ⟨div_nonneg (sub_nonneg.mpr hv1) hd.le,
    (div_le_iff₀ hd).2 (by linarith)⟩

theorem lightCenter_bounds {r : AnalyticRow} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < lightCenter r x ∧ lightCenter r x < 1 := by
  cases r <;> simp only [lightCenter] <;> constructor <;> linarith

theorem cubicEnvelope_le_one {p : ℝ} (hp : 0 ≤ p) : cubicEnvelope p ≤ 1 := by
  have hp2 : 0 ≤ p^2 := sq_nonneg p
  have hp3 : 0 ≤ p^3 := pow_nonneg hp _
  unfold cubicEnvelope
  linarith

theorem cubicEnvelope_ge_fifty_over_eighty_one {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 2/3) : 50/81 ≤ cubicEnvelope p := by
  have hs : 0 ≤ (2/3-p)*(2/3+p) := mul_nonneg (by linarith) (by linarith)
  have hc : 0 ≤ (2/3-p)*(p^2+2/3*p+4/9) :=
    mul_nonneg (by linarith) (by positivity)
  have hp2 : p^2 ≤ 4/9 := by nlinarith
  have hp3 : p^3 ≤ 8/27 := by nlinarith
  unfold cubicEnvelope
  linarith

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.row_constants_pos
#print axioms Erdos993Lean.BCFG.Analytic.row_constants_pos
#check Erdos993Lean.BCFG.Analytic.price_pos
#print axioms Erdos993Lean.BCFG.Analytic.price_pos
#check Erdos993Lean.BCFG.Analytic.gamma_pos
#print axioms Erdos993Lean.BCFG.Analytic.gamma_pos
#check Erdos993Lean.BCFG.Analytic.occupation_bounds
#print axioms Erdos993Lean.BCFG.Analytic.occupation_bounds
#check Erdos993Lean.BCFG.Analytic.occupation_le_q
#print axioms Erdos993Lean.BCFG.Analytic.occupation_le_q
#check Erdos993Lean.BCFG.Analytic.rhoZero_bounds
#print axioms Erdos993Lean.BCFG.Analytic.rhoZero_bounds
#check Erdos993Lean.BCFG.Analytic.dCoeff_pos
#print axioms Erdos993Lean.BCFG.Analytic.dCoeff_pos
#check Erdos993Lean.BCFG.Analytic.rCoeff_pos
#print axioms Erdos993Lean.BCFG.Analytic.rCoeff_pos
#check Erdos993Lean.BCFG.Analytic.one_sub_q
#print axioms Erdos993Lean.BCFG.Analytic.one_sub_q
#check Erdos993Lean.BCFG.Analytic.lightOmega_bounds
#print axioms Erdos993Lean.BCFG.Analytic.lightOmega_bounds
#check Erdos993Lean.BCFG.Analytic.lightOmega_pos
#print axioms Erdos993Lean.BCFG.Analytic.lightOmega_pos
#check Erdos993Lean.BCFG.Analytic.lightZ_bounds
#print axioms Erdos993Lean.BCFG.Analytic.lightZ_bounds
#check Erdos993Lean.BCFG.Analytic.lightUpper_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.lightUpper_nonneg
#check Erdos993Lean.BCFG.Analytic.heavyOmega_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavyOmega_pos
#check Erdos993Lean.BCFG.Analytic.heavyZ_bounds
#print axioms Erdos993Lean.BCFG.Analytic.heavyZ_bounds
#check Erdos993Lean.BCFG.Analytic.lightCenter_bounds
#print axioms Erdos993Lean.BCFG.Analytic.lightCenter_bounds
#check Erdos993Lean.BCFG.Analytic.cubicEnvelope_le_one
#print axioms Erdos993Lean.BCFG.Analytic.cubicEnvelope_le_one
#check Erdos993Lean.BCFG.Analytic.cubicEnvelope_ge_fifty_over_eighty_one
#print axioms Erdos993Lean.BCFG.Analytic.cubicEnvelope_ge_fifty_over_eighty_one
