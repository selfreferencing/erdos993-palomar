module

public import F4Heavy.Analysis.TailSourceBounds
public import F4Heavy.Analysis.CapLogGeometry

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def tailCurvature (r : Row) (lam Y : ℝ) : ℝ :=
  (gamma r lam - delta r lam) * (1 + Real.exp Y / lam) - Y * tailP1 r lam (p lam Y)

def tailCurvatureSlope (r : Row) (lam Y : ℝ) : ℝ :=
  (gamma r lam - delta r lam) * Real.exp Y / lam - tailP1 r lam (p lam Y) -
    Y * p lam Y * (1 - p lam Y) * (1 + gamma r lam / 2 + gamma r lam * p lam Y / 6)

def tailCurvatureSecond (r : Row) (lam Y : ℝ) : ℝ :=
  (gamma r lam - delta r lam) * Real.exp Y / lam -
    2 * p lam Y * (1 - p lam Y) * (1 + gamma r lam / 2 + gamma r lam * p lam Y / 6) +
    Y * p lam Y * (1 - p lam Y) *
      ((1 - 2 * p lam Y) * (1 + gamma r lam / 2 + gamma r lam * p lam Y / 6) +
        gamma r lam * p lam Y * (1 - p lam Y) / 6)

theorem tail_curvature_identity (r : Row) (lam Y : ℝ) (hl : 0 < lam) :
    tailCurvature r lam Y = (gamma r lam - delta r lam) / p lam Y - Y * tailP1 r lam (p lam Y) := by
  unfold tailCurvature
  rw [← cap_parent_probability_inverse lam Y hl]
  ring

theorem tail_curvature_derivative (r : Row) (lam Y : ℝ) (hl : 0 < lam) :
    HasDerivAt (tailCurvature r lam) (tailCurvatureSlope r lam Y) Y := by
  have he := (((Real.hasDerivAt_exp Y).div_const lam).const_add 1).const_mul (gamma r lam - delta r lam)
  have h := he.sub ((hasDerivAt_id Y).mul (tail_p1_derivative r lam Y hl))
  convert h using 1
  · rfl
  · dsimp
    unfold tailCurvatureSlope
    ring

theorem tail_curvature_second_derivative (r : Row) (lam Y : ℝ) (hl : 0 < lam) :
    HasDerivAt (tailCurvatureSlope r lam) (tailCurvatureSecond r lam Y) Y := by
  have hp := tail_parent_probability_derivative lam Y hl
  have ha := ((hp.const_mul (gamma r lam)).div_const 6).const_add (1 + gamma r lam / 2)
  have he := ((Real.hasDerivAt_exp Y).const_mul (gamma r lam - delta r lam)).div_const lam
  have h := (he.sub (tail_p1_derivative r lam Y hl)).sub
    ((((hasDerivAt_id Y).mul hp).mul (hp.const_sub 1)).mul ha)
  convert h using 1
  · rfl
  · dsimp
    unfold tailCurvatureSecond
    ring

theorem tail_curvature_threshold_slope (r : Row) (lam : ℝ) (hl : 0 < lam) :
    tailCurvatureSlope r lam (tailTau r lam) = tailEStar r lam -
      tailP1 r lam (tailPStar r lam) - tailTau r lam * tailPStar r lam *
        (1 - tailPStar r lam) * tailAStar r lam := by
  have harg : 0 < tailScale r * (1 + lam) := mul_pos (tail_scale_positive r) (by linarith)
  unfold tailCurvatureSlope
  rw [tail_probability_at_threshold r lam hl]
  simp only [tailTau, Real.exp_log harg]
  unfold tailEStar tailAStar
  ring

end
end F4Heavy.Analysis
