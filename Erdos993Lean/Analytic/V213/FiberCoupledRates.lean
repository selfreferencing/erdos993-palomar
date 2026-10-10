module

public import Erdos993Lean.Analytic.V213.FiberCornerBounds

/-!
All-real coupled C1/C2 rates. The coupled
function is evaluated at the actual right endpoint; its ell component
is never asserted to be a common lower input rate. No endpoint sampling
replaces the whole closed parameter interval.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set Real

noncomputable def fiberCoupledRate (base slope c z : ℝ) : ℝ :=
  base + slope*z - c*Real.log (1+z)

theorem fiber_coupled_rate_deriv {base slope c z : ℝ} (hz : -1 < z) :
    HasDerivAt (fiberCoupledRate base slope c) (slope-c/(1+z)) z := by
  have hp : 1+z ≠ 0 := by linarith only [hz]
  have hlog := ((hasDerivAt_id z).const_add 1).log hp
  convert (((hasDerivAt_id z).const_mul slope).const_add base).sub (hlog.const_mul c) using 1 <;>
    first | rfl | (dsimp; ring)

theorem fiber_coupled_rate_antitone {base slope c l h : ℝ}
    (hl : -1 < l) (hs : 0 ≤ slope) (hc : slope*(1+h) ≤ c) :
    AntitoneOn (fiberCoupledRate base slope c) (Icc l h) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l h)
  · intro z hz
    exact (fiber_coupled_rate_deriv (lt_of_lt_of_le hl hz.1)).continuousAt.continuousWithinAt
  · intro z hz
    exact (fiber_coupled_rate_deriv (lt_of_lt_of_le hl (interior_subset hz).1)).hasDerivWithinAt
  · intro z hz
    have hz' := interior_subset hz
    have hp : 0 < 1+z := by linarith only [hl,hz'.1]
    have hsc : slope*(1+z) ≤ c := (mul_le_mul_of_nonneg_left (by linarith only [hz'.2]) hs).trans hc
    exact sub_nonpos.mpr ((le_div_iff₀ hp).2 hsc)

theorem fiber_coupled_rate_monotone {base slope c l h : ℝ}
    (hl : -1 < l) (hs : 0 ≤ slope) (hc : c ≤ slope*(1+l)) :
    MonotoneOn (fiberCoupledRate base slope c) (Icc l h) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l h)
  · intro z hz
    exact (fiber_coupled_rate_deriv (lt_of_lt_of_le hl hz.1)).continuousAt.continuousWithinAt
  · intro z hz
    exact (fiber_coupled_rate_deriv (lt_of_lt_of_le hl (interior_subset hz).1)).hasDerivWithinAt
  · intro z hz
    have hz' := interior_subset hz
    have hp : 0 < 1+z := by linarith only [hl,hz'.1]
    have hsc : c ≤ slope*(1+z) := hc.trans (mul_le_mul_of_nonneg_left (by linarith only [hz'.1]) hs)
    exact sub_nonneg.mpr ((div_le_iff₀ hp).2 hsc)

theorem fiber_c1_coupled_lower {z c : ℝ} (hz : z ∈ Icc (9/25 : ℝ) (9/20))
    (hc : c = 13/25 ∨ c = 3/5) :
    279/1000 - (929/2500)*c ≤ fiberCoupledRate (243/2000) (7/20) c z := by
  have hm : AntitoneOn (fiberCoupledRate (243/2000) (7/20) c) (Icc (9/25) (9/20)) :=
    fiber_coupled_rate_antitone (by norm_num) (by norm_num) (by rcases hc with rfl|rfl <;> norm_num)
  have he := hm hz (by norm_num : (9/20 : ℝ) ∈ Icc (9/25) (9/20)) hz.2
  have hl := fiber_corner_log_upper .y29_20
  norm_num [fiberCornerLogById,lowMeanFractionReal] at hl
  have hc0 : 0 ≤ c := by rcases hc with rfl|rfl <;> norm_num
  have hmul := mul_le_mul_of_nonneg_left hl hc0
  dsimp [fiberCoupledRate] at he ⊢
  norm_num at he
  linarith only [he,hmul]

theorem fiber_c2_cut_coupled_lower {z : ℝ} (hz : z ∈ Icc (1/2 : ℝ) (3/5)) :
    3/10 - (203/500)*(27/50) ≤ fiberCoupledRate (27/250) (48/125) (27/50) z := by
  have hm : MonotoneOn (fiberCoupledRate (27/250) (48/125) (27/50)) (Icc (1/2) (3/5)) :=
    fiber_coupled_rate_monotone (by norm_num) (by norm_num) (by norm_num)
  have he := hm (by norm_num : (1/2 : ℝ) ∈ Icc (1/2) (3/5)) hz hz.1
  have hl := fiber_corner_log_upper .y3_2
  norm_num [fiberCornerLogById,lowMeanFractionReal] at hl
  dsimp [fiberCoupledRate] at he ⊢
  norm_num at he
  linarith only [he,hl]

theorem fiber_c2_time_coupled_lower {z : ℝ} (hz : z ∈ Icc (1/2 : ℝ) (3/5)) :
    423/1250 - (471/1000)*(69/100) ≤ fiberCoupledRate (27/250) (48/125) (69/100) z := by
  have hm : AntitoneOn (fiberCoupledRate (27/250) (48/125) (69/100)) (Icc (1/2) (3/5)) :=
    fiber_coupled_rate_antitone (by norm_num) (by norm_num) (by norm_num)
  have he := hm hz (by norm_num : (3/5 : ℝ) ∈ Icc (1/2) (3/5)) hz.2
  have hl := fiber_corner_log_upper .y8_5
  norm_num [fiberCornerLogById,lowMeanFractionReal] at hl
  dsimp [fiberCoupledRate] at he ⊢
  norm_num at he
  linarith only [he,hl]

end Erdos993Lean.Analytic.V213
