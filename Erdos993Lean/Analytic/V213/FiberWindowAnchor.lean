module

public import Erdos993Lean.Analytic.V213.FiberWindowInverseBounds
public import Erdos993Lean.Analytic.V213.FiberWindowParameters

/-!
Eq90/102: the literal degree-five exponential sum and printed anchor
produce a strictly positive capped inverse input. Its comparison to the
actual exponential and actual root holds over the full real domain.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

noncomputable def fiberWindowTaylor5 (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120

noncomputable def fiberWindowAnchor (l v gain : ℝ) : ℝ :=
  min 1 (2 * v * l ^ 3 / (l + v ^ 2) * fiberWindowTaylor5 (1 + gain))

noncomputable def fiberWindowX (a b N0 l v : ℝ) : ℝ :=
  let w := fiberWindowInverse (fiberWindowAnchor l v (fiberRationalGain a b N0))
  1 + fiberWindowDelta a N0 - 2 * (1 - w) ^ 2 / (fiberWindowRho b N0 * w)

theorem fiber_window_taylor5_sum (x : ℝ) :
    fiberWindowTaylor5 x = ∑ j ∈ Finset.range 6, x ^ j / (j.factorial : ℝ) := by
  norm_num [fiberWindowTaylor5,Finset.sum_range_succ,Nat.factorial]

theorem fiber_window_taylor5_lower {x : ℝ} (hx : 0 ≤ x) :
    fiberWindowTaylor5 x ≤ Real.exp x := by
  rw [fiber_window_taylor5_sum]
  exact Real.sum_le_exp_of_nonneg hx 6

theorem fiber_window_taylor5_positive {x : ℝ} (hx : 0 ≤ x) : 0 < fiberWindowTaylor5 x := by
  unfold fiberWindowTaylor5
  positivity

/-- Both literal Eq90 square-root inequalities, with their printed domains. -/
theorem fiber_window_anchor_sqrt {x v : ℝ} (hx : 0 ≤ x) (hv : 0 < v) :
    2 * v * x / (x + v ^ 2) ≤ Real.sqrt x ∧ Real.sqrt x ≤ (x + v ^ 2) / (2 * v) := by
  have hs := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg x
  have hd : 0 < x + v ^ 2 := by positivity
  constructor
  · apply (div_le_iff₀ hd).2
    have h := mul_nonneg hs0 (sq_nonneg (Real.sqrt x - v))
    have he : Real.sqrt x * (Real.sqrt x - v) ^ 2 =
        Real.sqrt x * (x + v ^ 2) - 2 * v * x := by
      calc
        _ = Real.sqrt x * (Real.sqrt x) ^ 2 - 2 * v * (Real.sqrt x) ^ 2 +
          Real.sqrt x * v ^ 2 := by ring
        _ = _ := by rw [hs]; ring
    rw [he] at h
    linarith only [h]
  · apply (le_div_iff₀ (by positivity : 0 < 2 * v)).2
    nlinarith only [sq_nonneg (Real.sqrt x - v),hs]

theorem fiber_window_five_halves_exp {l : ℝ} (hl : 0 < l) :
    Real.exp ((5 / 2) * Real.log l) = l ^ 2 * Real.sqrt l := by
  apply (sq_eq_sq₀ (Real.exp_nonneg _) (by positivity : 0 ≤ l ^ 2 * Real.sqrt l)).1
  have he : (Real.exp ((5 / 2) * Real.log l)) ^ 2 = Real.exp (5 * Real.log l) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he,show (5 : ℝ) = (5 : ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hl,
    mul_pow,Real.sq_sqrt hl.le]
  ring

theorem fiber_window_anchor_domain {l v gain : ℝ} (hl : 0 < l) (hv : 0 < v)
    (hg : 0 ≤ 1 + gain) :
    0 < fiberWindowAnchor l v gain ∧ fiberWindowAnchor l v gain ≤ 1 := by
  have hp := fiber_window_taylor5_positive hg
  unfold fiberWindowAnchor
  exact ⟨lt_min (by norm_num) (by positivity),min_le_left _ _⟩

theorem fiber_window_anchor_exponential {l v gain omega : ℝ} (hl : 0 < l) (hv : 0 < v)
    (hg : 0 ≤ 1 + gain) (homega : (5 / 2) * Real.log l + gain ≤ omega) :
    fiberWindowAnchor l v gain ≤ Real.exp (1 + omega) := by
  have hs := (fiber_window_anchor_sqrt hl.le hv).1
  have hp := fiber_window_taylor5_positive hg
  have ht := fiber_window_taylor5_lower hg
  have hmul := mul_le_mul_of_nonneg_right hs
    (by positivity : 0 ≤ l ^ 2 * fiberWindowTaylor5 (1 + gain))
  have hleft : (2 * v * l / (l + v ^ 2)) *
      (l ^ 2 * fiberWindowTaylor5 (1 + gain)) =
        2 * v * l ^ 3 / (l + v ^ 2) * fiberWindowTaylor5 (1 + gain) := by ring
  rw [hleft] at hmul
  have hexp := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ l ^ 2 * Real.sqrt l)
  have he : (l ^ 2 * Real.sqrt l) * Real.exp (1 + gain) =
      Real.exp (1 + ((5 / 2) * Real.log l + gain)) := by
    rw [← fiber_window_five_halves_exp hl,← Real.exp_add]
    congr 1
    ring
  have hr : Real.sqrt l * (l ^ 2 * fiberWindowTaylor5 (1 + gain)) =
      (l ^ 2 * Real.sqrt l) * fiberWindowTaylor5 (1 + gain) := by ring
  rw [hr] at hmul
  rw [he] at hexp
  exact (min_le_right _ _).trans
    ((hmul.trans hexp).trans (Real.exp_le_exp.mpr (by linarith only [homega])))

theorem fiber_window_anchor_root {l v gain omega : ℝ} (hl : 0 < l) (hv : 0 < v)
    (hg : 0 ≤ 1 + gain) (homega : (5 / 2) * Real.log l + gain ≤ omega) :
    fiberWindowInverse (fiberWindowAnchor l v gain) ≤ 1 + V22.rootMap omega := by
  exact fiber_window_inverse_root (fiber_window_anchor_domain hl hv hg).1
    (fiber_window_anchor_exponential hl hv hg homega)

end Erdos993Lean.Analytic.V213
