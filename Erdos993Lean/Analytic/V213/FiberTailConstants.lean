module

public import Erdos993Lean.Analytic.V213.FiberTailNormalization
public import Erdos993Lean.Analytic.V213.FiberProfileInverseBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
Actual C_q in Eq91/92. The bounds
13/6 and 5/2 apply to the whole printed absolute-skew domains. They
follow analytic bounds on pi and exp(1), with no new finite family.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_pi_exp_upper : 2*Real.pi*Real.exp 1 < (25/6 : ℝ)^2 := by
  have hp : Real.pi < 22/7 := by linarith only [Real.pi_lt_d4]
  have he := fiber_exp_one_upper
  have hp0 := Real.pi_pos
  have he0 := Real.exp_pos (1 : ℝ)
  have h1 := mul_lt_mul_of_pos_right hp he0
  have h2 := mul_lt_mul_of_pos_left he (by norm_num : (0 : ℝ) < 22/7)
  nlinarith only [h1,h2]

theorem fiber_tail_C_formula {rhi : ℝ} (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) :
    fiberTailC rhi = Real.sqrt (2*Real.pi*Real.exp 1)/(2*Real.sqrt (1-rhi^2)) := by
  have hb : 0 < 1-rhi^2 := by nlinarith only [hr0,hr1]
  have ha : 0 < 2*Real.pi*Real.exp 1 := by positivity
  have hsa := (Real.sqrt_pos.mpr ha).ne'
  have hsb := (Real.sqrt_pos.mpr hb).ne'
  unfold fiberTailC fiberAG
  rw [Real.sqrt_div hb.le]
  rw [show Real.sqrt (4 : ℝ) = 2 by norm_num]
  field_simp
  <;> ring

theorem fiber_tail_C_central {rhi : ℝ} (hr0 : 0 ≤ rhi) (hr : rhi ≤ 1/4) :
    fiberTailC rhi ≤ 13/6 := by
  have hr1 : rhi < 1 := by linarith only [hr]
  have hb : 15/16 ≤ 1-rhi^2 := by nlinarith only [hr0,hr]
  have hb0 : 0 < 1-rhi^2 := by linarith only [hb]
  have hs := Real.sq_sqrt hb0.le
  have hsp := Real.sqrt_pos.mpr hb0
  have ha0 : 0 ≤ 2*Real.pi*Real.exp 1 := by positivity
  have ha := Real.sq_sqrt ha0
  have hap := Real.sqrt_nonneg (2*Real.pi*Real.exp 1)
  have hu := fiber_tail_pi_exp_upper
  rw [fiber_tail_C_formula hr0 hr1]
  apply (div_le_iff₀ (mul_pos (by norm_num) hsp)).2
  nlinarith only [hb,hs,ha,hap,hsp,hu]

theorem fiber_tail_C_outer {rhi : ℝ} (hr0 : 0 ≤ rhi) (hr : rhi ≤ 1/2) :
    fiberTailC rhi ≤ 5/2 := by
  have hr1 : rhi < 1 := by linarith only [hr]
  have hb : 3/4 ≤ 1-rhi^2 := by nlinarith only [hr0,hr]
  have hb0 : 0 < 1-rhi^2 := by linarith only [hb]
  have hs := Real.sq_sqrt hb0.le
  have hsp := Real.sqrt_pos.mpr hb0
  have ha0 : 0 ≤ 2*Real.pi*Real.exp 1 := by positivity
  have ha := Real.sq_sqrt ha0
  have hap := Real.sqrt_nonneg (2*Real.pi*Real.exp 1)
  have hu := fiber_tail_pi_exp_upper
  rw [fiber_tail_C_formula hr0 hr1]
  apply (div_le_iff₀ (mul_pos (by norm_num) hsp)).2
  nlinarith only [hb,hs,ha,hap,hsp,hu]

end Erdos993Lean.Analytic.V213
