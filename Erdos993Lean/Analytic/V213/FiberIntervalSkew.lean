module

public import Erdos993Lean.Analytic.V213.FiberDefinitions

/-!
Exact endpoint absolute-skew maximum and monotone skew cost on a
closed probability interval. These are actual endpoint formulas, not
replacement endpoint data. The original q remains the probability in
all moment and Laplace factors.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberInputSkewHigh (qlo qhi : ℝ) : ℝ :=
  max |fiberSkew qlo| |fiberSkew qhi|

theorem fiber_skew_interval_bound {q qlo qhi : ℝ} (hq : q ∈ Set.Icc qlo qhi) :
    |fiberSkew q| ≤ fiberInputSkewHigh qlo qhi := by
  have hL : -fiberInputSkewHigh qlo qhi ≤ fiberSkew qlo := by
    calc
      _ ≤ -|fiberSkew qlo| := neg_le_neg (le_max_left _ _)
      _ ≤ _ := neg_abs_le _
  have hR : fiberSkew qhi ≤ fiberInputSkewHigh qlo qhi :=
    (le_abs_self _).trans (le_max_right _ _)
  apply abs_le.mpr
  unfold fiberSkew at hL hR ⊢
  constructor
  · linarith only [hL,hq.1]
  · linarith only [hR,hq.2]

theorem fiber_skew_abs_half {q : ℝ} (hq : q ∈ Set.Icc (1 / 4) (3 / 4)) :
    |fiberSkew q| ≤ 1 / 2 := by
  apply abs_le.mpr
  unfold fiberSkew
  constructor <;> linarith only [hq.1,hq.2]

theorem fiber_skew_high_nonneg (qlo qhi : ℝ) : 0 ≤ fiberInputSkewHigh qlo qhi :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem fiber_skew_high_half {qlo qhi : ℝ}
    (hlo : qlo ∈ Set.Icc (1 / 4) (3 / 4)) (hhi : qhi ∈ Set.Icc (1 / 4) (3 / 4)) :
    fiberInputSkewHigh qlo qhi ≤ 1 / 2 :=
  max_le (fiber_skew_abs_half hlo) (fiber_skew_abs_half hhi)

theorem fiber_skew_ratio_monotone {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hsh : s ≤ 1 / 2) :
    r ^ 2 / (1 - r ^ 2) ≤ s ^ 2 / (1 - s ^ 2) := by
  have hs := hr.trans hrs
  have hrh := hrs.trans hsh
  have hor : 0 < 1 - r ^ 2 := by nlinarith only [hr,hrh]
  have hos : 0 < 1 - s ^ 2 := by nlinarith only [hs,hsh]
  have hsq := (sq_le_sq₀ hr hs).2 hrs
  apply (div_le_div_iff₀ hor hos).2
  nlinarith only [hsq]

theorem fiber_skew_interval_cost {q qlo qhi mu : ℝ}
    (hlo : qlo ∈ Set.Icc (1 / 4) (3 / 4)) (hhi : qhi ∈ Set.Icc (1 / 4) (3 / 4))
    (hq : q ∈ Set.Icc qlo qhi) (hmu : 0 < mu) :
    fiberSkew q ^ 2 / ((1 - fiberSkew q ^ 2) * mu) ≤
      fiberInputSkewHigh qlo qhi ^ 2 / ((1 - fiberInputSkewHigh qlo qhi ^ 2) * mu) := by
  have hs := fiber_skew_interval_bound hq
  have hh := fiber_skew_high_half hlo hhi
  have h := fiber_skew_ratio_monotone (abs_nonneg (fiberSkew q)) hs hh
  rw [sq_abs] at h
  have hd := div_le_div_of_nonneg_right h hmu.le
  convert hd using 1 <;> rw [div_div]

end Erdos993Lean.Analytic.V213
