module

public import Erdos993Lean.Analytic.V22.Analysis.RootMap
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic

/-!
# Version 2.2 of the manuscript: the full root-G estimates and bonus split

Source: note Lemma 3.5(b--d) and Lemma 3.6. All lambda variables are real;
only the forward Taylor shift has `h >= 0`, and the three elementary bounds
have `lambda >= 0`. The bonus split allows arbitrary real shift and error.
Consumers: E3 activity-one estimates and E4/E5 remainder/window estimates.


`RootMap` is retained unchanged.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set
open scoped Topology ContDiff

theorem rootG_differentiable : Differentiable ℝ rootG :=
  fun lambda => (hasDerivAt_rootG lambda).differentiableAt

theorem rootGPrime_differentiable : Differentiable ℝ rootGPrime :=
  fun lambda => (hasDerivAt_rootGPrime lambda).differentiableAt

theorem rootG_continuous : Continuous rootG := rootG_differentiable.continuous

theorem rootGPrime_continuous : Continuous rootGPrime := rootGPrime_differentiable.continuous

theorem rootG_deriv_eq : deriv rootG = rootGPrime := by
  funext lambda
  exact (hasDerivAt_rootG lambda).deriv

theorem rootGPrime_deriv_eq : deriv rootGPrime = rootGSecond := by
  funext lambda
  exact (hasDerivAt_rootGPrime lambda).deriv

@[simp] theorem rootGSecond_zero : rootGSecond 0 = (1 / 2 : ℝ) := by
  norm_num [rootGSecond]

theorem rootGSecond_continuous : Continuous rootGSecond := by
  unfold rootGSecond
  apply continuous_const.div
    ((continuous_const.add rootMap_continuous).mul (continuous_const.add rootMap_continuous))
  intro lambda
  apply mul_ne_zero
  · dsimp only [Pi.add_apply]
    exact ne_of_gt (by linarith [rootMap_gt_neg_one lambda])
  · dsimp only [Pi.add_apply]
    exact ne_of_gt (by linarith [rootMap_gt_neg_one lambda])

theorem rootGPrime_contDiff_one : ContDiff ℝ 1 rootGPrime := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨rootGPrime_differentiable, ?_⟩
  rw [rootGPrime_deriv_eq]
  exact rootGSecond_continuous

/-- The genuine `C^2` assertion from Lemma 3.5(b), on all of R. -/
theorem rootG_contDiff_two : ContDiff ℝ 2 rootG := by
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) rootG
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨rootG_differentiable, by simp, ?_⟩
  rw [rootG_deriv_eq]
  exact rootGPrime_contDiff_one

theorem rootGPrime_strictMono : StrictMono rootGPrime :=
  strictMono_of_hasDerivAt_pos hasDerivAt_rootGPrime rootGSecond_pos

theorem rootGPrime_monotone : Monotone rootGPrime := rootGPrime_strictMono.monotone

theorem rootG_convex : ConvexOn ℝ univ rootG := by
  apply Monotone.convexOn_univ_of_deriv rootG_differentiable
  rw [rootG_deriv_eq]
  exact rootGPrime_monotone

theorem rootG_strictConvex : StrictConvexOn ℝ univ rootG := by
  apply StrictMono.strictConvexOn_univ_of_deriv rootG_continuous
  rw [rootG_deriv_eq]
  exact rootGPrime_strictMono

/-- The second derivative decreases everywhere, including negative lambda. -/
theorem rootGSecond_strictAnti : StrictAnti rootGSecond := by
  intro lambda mu hlm
  have hsm := rootMap_strictMono hlm
  have hsl : 0 < 1 + rootMap lambda := by linarith [rootMap_gt_neg_one lambda]
  have htl : 0 < 2 + rootMap lambda := by linarith
  have hsu : 0 < 1 + rootMap mu := by linarith [rootMap_gt_neg_one mu]
  have htu : 0 < 2 + rootMap mu := by linarith
  have hprod : (1 + rootMap lambda) * (2 + rootMap lambda) <
      (1 + rootMap mu) * (2 + rootMap mu) := by
    apply lt_of_lt_of_le (mul_lt_mul_of_pos_left (by linarith :
      2 + rootMap lambda < 2 + rootMap mu) hsl)
    exact mul_le_mul_of_nonneg_right (by linarith) htu.le
  unfold rootGSecond
  apply (div_lt_div_iff₀ (mul_pos hsu htu) (mul_pos hsl htl)).2
  simpa using hprod

theorem rootGSecond_antitone : Antitone rootGSecond := rootGSecond_strictAnti.antitone

theorem rootGPrime_nonpos {lambda : ℝ} (hl : lambda ≤ 0) : rootGPrime lambda ≤ 0 := by
  have hs : rootMap lambda ≤ 0 := by simpa using rootMap_monotone hl
  unfold rootGPrime
  exact div_nonpos_of_nonpos_of_nonneg hs (by linarith [rootMap_gt_neg_one lambda])

theorem rootGPrime_nonneg {lambda : ℝ} (hl : 0 ≤ lambda) : 0 ≤ rootGPrime lambda := by
  have hs : 0 ≤ rootMap lambda := (rootMap_nonneg_le hl).1
  unfold rootGPrime
  exact div_nonneg hs (by linarith [rootMap_gt_neg_one lambda])

theorem rootG_antitoneOn_nonpos : AntitoneOn rootG (Iic 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0) rootG_continuous.continuousOn
    (fun lambda _ => (hasDerivAt_rootG lambda).hasDerivWithinAt)
  intro lambda hl
  exact rootGPrime_nonpos (by
    simpa only [mem_Iic] using (interior_subset hl : lambda ∈ Iic 0))

theorem rootG_monotoneOn_nonneg : MonotoneOn rootG (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) rootG_continuous.continuousOn
    (fun lambda _ => (hasDerivAt_rootG lambda).hasDerivWithinAt)
  intro lambda hl
  exact rootGPrime_nonneg (by
    simpa only [mem_Ici] using (interior_subset hl : lambda ∈ Ici 0))

/-- The absolute slope decreases on the negative half-line. -/
theorem rootGPrime_abs_antitoneOn_nonpos : AntitoneOn (fun lambda => |rootGPrime lambda|) (Iic 0) := by
  intro lambda hl mu hm hlm
  change |rootGPrime mu| ≤ |rootGPrime lambda|
  rw [abs_of_nonpos (rootGPrime_nonpos hm), abs_of_nonpos (rootGPrime_nonpos hl)]
  exact neg_le_neg (rootGPrime_monotone hlm)

/-- First integrate the decreasing second derivative, retaining arbitrary
real starting lambda and nonnegative forward shift. -/
theorem rootGPrime_shift_upper (lambda h : ℝ) (hh : 0 ≤ h) :
    rootGPrime (lambda + h) ≤ rootGPrime lambda + h * rootGSecond lambda := by
  let f : ℝ → ℝ := fun x => rootGPrime lambda + x * rootGSecond lambda - rootGPrime (lambda + x)
  have hd : ∀ x, HasDerivAt f (rootGSecond lambda - rootGSecond (lambda + x)) x := by
    intro x
    convert ((hasDerivAt_const x (rootGPrime lambda)).add
      ((hasDerivAt_id x).mul_const (rootGSecond lambda))).sub
      ((hasDerivAt_rootGPrime (lambda + x)).comp x ((hasDerivAt_id x).const_add lambda)) using 1
    · funext z
      dsimp [f] <;> ring
    · norm_num <;> ring
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc.continuousOn
      (fun x _ => (hd x).hasDerivWithinAt) (fun x hx => by
        have hx0 : 0 ≤ x := by
          simpa only [mem_Ici] using (interior_subset hx : x ∈ Ici 0)
        exact sub_nonneg.mpr (rootGSecond_antitone (by linarith : lambda ≤ lambda + x)))
  have he := hm (by simp : (0 : ℝ) ∈ Ici 0) hh hh
  dsimp [f] at he
  simp only [zero_mul, add_zero, sub_self] at he
  linarith

/-- Note Lemma 3.5(c), with its exact domain and constant. -/
theorem rootG_taylor_shift_upper (lambda h : ℝ) (hh : 0 ≤ h) :
    rootG (lambda + h) ≤ rootG lambda + h * rootGPrime lambda + h ^ 2 / 2 * rootGSecond lambda := by
  let f : ℝ → ℝ := fun x => rootG lambda + x * rootGPrime lambda +
    x ^ 2 / 2 * rootGSecond lambda - rootG (lambda + x)
  have hd : ∀ x, HasDerivAt f
      (rootGPrime lambda + x * rootGSecond lambda - rootGPrime (lambda + x)) x := by
    intro x
    convert (((hasDerivAt_const x (rootG lambda)).add
      ((hasDerivAt_id x).mul_const (rootGPrime lambda))).add
      (((hasDerivAt_pow 2 x).div_const 2).mul_const (rootGSecond lambda))).sub
      ((hasDerivAt_rootG (lambda + x)).comp x ((hasDerivAt_id x).const_add lambda)) using 1
    · funext z
      dsimp [f] <;> ring
    · norm_num <;> ring
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc.continuousOn
      (fun x _ => (hd x).hasDerivWithinAt) (fun x hx => by
        have hx0 : 0 ≤ x := by
          simpa only [mem_Ici] using (interior_subset hx : x ∈ Ici 0)
        exact sub_nonneg.mpr (rootGPrime_shift_upper lambda x hx0))
  have he := hm (by simp : (0 : ℝ) ∈ Ici 0) hh hh
  dsimp [f] at he
  norm_num at he
  linarith

/-- Note Lemma 3.5(d), the quadratic bound. -/
theorem rootG_le_quarter_sq {lambda : ℝ} (hl : 0 ≤ lambda) :
    rootG lambda ≤ lambda ^ 2 / 4 := by
  have ht := rootG_taylor_shift_upper 0 lambda hl
  simp only [zero_add, rootG_zero, rootGPrime_zero, rootGSecond_zero, mul_zero] at ht
  nlinarith

/-- Note Lemma 3.5(d), the linear bound. -/
theorem rootG_le_lambda {lambda : ℝ} (hl : 0 ≤ lambda) : rootG lambda ≤ lambda := by
  obtain ⟨hs0, hsl⟩ := rootMap_nonneg_le hl
  have hs : 0 < 1 + rootMap lambda := by linarith
  have hGs : rootG lambda ≤ rootMap lambda := by
    unfold rootG
    apply (div_le_iff₀ hs).2
    nlinarith
  exact hGs.trans hsl

theorem rootGPrime_le_lambda_fraction {lambda : ℝ} (hl : 0 ≤ lambda) :
    rootGPrime lambda ≤ lambda / (1 + lambda) := by
  obtain ⟨hs0, hsl⟩ := rootMap_nonneg_le hl
  have hs : 0 < 1 + rootMap lambda := by linarith
  unfold rootGPrime
  apply (div_le_div_iff₀ hs (by linarith : 0 < 1 + lambda)).2
  nlinarith

/-- Note Lemma 3.5(d), including the useful logarithmic improvement. -/
theorem rootG_le_lambda_sub_log {lambda : ℝ} (hl : 0 ≤ lambda) :
    rootG lambda ≤ lambda - Real.log (1 + lambda) := by
  let f : ℝ → ℝ := fun x => x - Real.log (1 + x) - rootG x
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f (x / (1 + x) - rootGPrime x) x := by
    intro x hx
    have hx0 : 0 ≤ x := by simpa only [mem_Ici] using hx
    have hs : 1 + x ≠ 0 := ne_of_gt (by linarith)
    convert ((hasDerivAt_id x).sub (((hasDerivAt_id x).const_add 1).log hs)).sub
      (hasDerivAt_rootG x) using 1
    · funext z
      dsimp [f]
    · simp only [id_eq]
      field_simp [hs] <;> ring
  have hc : ContinuousOn f (Ici 0) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => sub_nonneg.mpr (rootGPrime_le_lambda_fraction (by
        simpa only [mem_Ici] using (interior_subset hx : x ∈ Ici 0))))
  have he := hm (by simp : (0 : ℝ) ∈ Ici 0) hl hl
  dsimp [f] at he
  norm_num only [add_zero, Real.log_one, rootG_zero, sub_zero] at he
  linarith

/-- The supporting-line inequality in the direction used by the bonus split;
it permits either sign of the displacement. -/
theorem rootG_tangent_upper (x y : ℝ) :
    rootG y ≤ rootG x + (y - x) * rootGPrime y := by
  rcases le_total x y with hxy | hyx
  · have he := (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le
      rootG_continuous.continuousOn rootG_differentiable.differentiableOn
      (fun z hz => by
        rw [rootG_deriv_eq]
        exact rootGPrime_monotone (interior_subset hz : z ∈ Icc x y).2)
      x ⟨le_rfl, hxy⟩ y ⟨hxy, le_rfl⟩ hxy
    nlinarith
  · have he := (convex_Icc y x).mul_sub_le_image_sub_of_le_deriv
      rootG_continuous.continuousOn rootG_differentiable.differentiableOn
      (fun z hz => by
        rw [rootG_deriv_eq]
        exact rootGPrime_monotone (interior_subset hz : z ∈ Icc y x).1)
      y ⟨le_rfl, hyx⟩ x ⟨hyx, le_rfl⟩ hyx
    nlinarith

/-- Note Lemma 3.6, the shift may be any real number. -/
theorem rootG_shift_linear_upper (lambda h : ℝ) :
    rootG (lambda + h) ≤ rootG lambda + h * rootGPrime (lambda + h) := by
  have ht := rootG_tangent_upper lambda (lambda + h)
  simpa only [add_sub_cancel_left] using ht

/-- Note Lemma 3.6's exact bonus split with gamma = 1 + Delta. -/
theorem rootG_bonus_split (lambda0 Delta e rho : ℝ) (hrho : 0 < rho) (_hDelta : 0 ≤ Delta) :
    let sigma := rootGPrime (lambda0 + (rho / 2 * Delta + e))
    1 + Delta - 2 / rho * rootG (lambda0 + (rho / 2 * Delta + e)) ≥
      1 - 2 / rho * rootG lambda0 + Delta * (1 - sigma) - 2 / rho * e * sigma := by
  dsimp only
  have ht := rootG_shift_linear_upper lambda0 (rho / 2 * Delta + e)
  have hm := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 2 / rho by positivity)
  calc
    1 + Delta - 2 / rho * rootG (lambda0 + (rho / 2 * Delta + e)) ≥
        1 + Delta - 2 / rho * (rootG lambda0 +
          (rho / 2 * Delta + e) * rootGPrime (lambda0 + (rho / 2 * Delta + e))) :=
      sub_le_sub_left hm _
    _ = 1 - 2 / rho * rootG lambda0 +
        Delta * (1 - rootGPrime (lambda0 + (rho / 2 * Delta + e))) -
        2 / rho * e * rootGPrime (lambda0 + (rho / 2 * Delta + e)) := by
      field_simp [hrho.ne']
      ring

/-- The split retains a nonnegative actual bonus term. -/
theorem rootG_bonus_term_nonneg (lambda Delta : ℝ) (hDelta : 0 ≤ Delta) :
    0 ≤ Delta * (1 - rootGPrime lambda) :=
  mul_nonneg hDelta (sub_nonneg.mpr (rootGPrime_lt_one lambda).le)

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.rootG_differentiable
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_differentiable
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_differentiable
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_differentiable
#check Erdos993Lean.Analytic.V22.Analysis.rootG_continuous
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_continuous
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_continuous
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_continuous
#check Erdos993Lean.Analytic.V22.Analysis.rootG_deriv_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_deriv_eq
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_deriv_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_deriv_eq
#check Erdos993Lean.Analytic.V22.Analysis.rootGSecond_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGSecond_zero
#check Erdos993Lean.Analytic.V22.Analysis.rootGSecond_continuous
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGSecond_continuous
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_contDiff_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_contDiff_one
#check Erdos993Lean.Analytic.V22.Analysis.rootG_contDiff_two
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_contDiff_two
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_strictMono
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_strictMono
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_monotone
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_monotone
#check Erdos993Lean.Analytic.V22.Analysis.rootG_convex
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_convex
#check Erdos993Lean.Analytic.V22.Analysis.rootG_strictConvex
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_strictConvex
#check Erdos993Lean.Analytic.V22.Analysis.rootGSecond_strictAnti
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGSecond_strictAnti
#check Erdos993Lean.Analytic.V22.Analysis.rootGSecond_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGSecond_antitone
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_nonpos
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_nonpos
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.rootG_antitoneOn_nonpos
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_antitoneOn_nonpos
#check Erdos993Lean.Analytic.V22.Analysis.rootG_monotoneOn_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_monotoneOn_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_abs_antitoneOn_nonpos
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_abs_antitoneOn_nonpos
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_shift_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_shift_upper
#check Erdos993Lean.Analytic.V22.Analysis.rootG_taylor_shift_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_taylor_shift_upper
#check Erdos993Lean.Analytic.V22.Analysis.rootG_le_quarter_sq
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_le_quarter_sq
#check Erdos993Lean.Analytic.V22.Analysis.rootG_le_lambda
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_le_lambda
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_le_lambda_fraction
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_le_lambda_fraction
#check Erdos993Lean.Analytic.V22.Analysis.rootG_le_lambda_sub_log
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_le_lambda_sub_log
#check Erdos993Lean.Analytic.V22.Analysis.rootG_tangent_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_tangent_upper
#check Erdos993Lean.Analytic.V22.Analysis.rootG_shift_linear_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_shift_linear_upper
#check Erdos993Lean.Analytic.V22.Analysis.rootG_bonus_split
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_bonus_split
#check Erdos993Lean.Analytic.V22.Analysis.rootG_bonus_term_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_bonus_term_nonneg
