module

public import Erdos993Lean.Analytic.V22.Analysis.GaussianCalculus

/-!
Entropy bounds for the actual `I` in `r12:eq69`.
The upper bound supplies the odd-row
correction in the actual central prefactor. No finite data is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_artanh_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Erdos993Lean.Analytic.V22.artanh x ≤ x / (1 - x ^ 2) := by
  have hd : 0 < 1 - x ^ 2 := shared_one_sub_sq_pos (by linarith) hx1
  have h := (sharedAHat_bounds hx0 hx1).2
  change Erdos993Lean.Analytic.V22.artanh x - x ≤ _ at h
  have hsmall : x ^ 3 / (3 * (1 - x ^ 2)) ≤ x ^ 3 / (1 - x ^ 2) := by
    exact div_le_div_of_nonneg_left (by positivity) hd (by linarith)
  have heq : x + x ^ 3 / (1 - x ^ 2) = x / (1 - x ^ 2) := by
    field_simp [hd.ne']
    ring
  linarith

theorem fiber_entropy_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    sharedKLI x ≤ x ^ 2 / (2 * (1 - x)) := by
  let f : ℝ → ℝ := fun y => y ^ 2 / (2 * (1 - y)) - sharedKLI y
  have hd : ∀ y ∈ Icc (0 : ℝ) x,
      HasDerivAt f
        (y * (2 - y) / (2 * (1 - y) ^ 2) -
          Erdos993Lean.Analytic.V22.artanh y) y := by
    intro y hy
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hx1
    have hne : 2 * (1 - y) ≠ 0 := by positivity
    convert (((hasDerivAt_pow 2 y).div
      (((hasDerivAt_id y).const_sub 1).const_mul 2) hne).sub
      (hasDerivAt_sharedKLI (by linarith [hy.1]) hy1)) using 1
    · funext z
      simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply,
        id_eq]
      rfl
    · dsimp
      field_simp [hne]
      ring
  have hc : ContinuousOn f (Icc (0 : ℝ) x) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc (0 : ℝ) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x) hc
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => by
        have hy' : y ∈ Icc (0 : ℝ) x := interior_subset hy
        have hy1 : y < 1 := lt_of_le_of_lt hy'.2 hx1
        have hn : 0 < 1 - y := by linarith
        have hs : 0 < 1 - y ^ 2 := shared_one_sub_sq_pos (by linarith [hy'.1]) hy1
        have ha := fiber_artanh_upper hy'.1 hy1
        have hrat : y / (1 - y ^ 2) ≤ y * (2 - y) / (2 * (1 - y) ^ 2) := by
          apply (div_le_div_iff₀ hs (by positivity)).2
          have hprod : 0 ≤ (1 - y) * (3 - y) :=
            mul_nonneg hn.le (by linarith)
          nlinarith [mul_nonneg (sq_nonneg y) hprod]
        linarith)
  have h := hm ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
  dsimp [f] at h
  simp only [zero_pow, zero_div, sharedKLI_zero, sub_self] at h
  linarith

theorem fiber_odd_entropy_correction {N : ℝ} (hN : 0 < N) :
    (N + 1) * sharedKLI (1 / (N + 1)) ≤ 1 / (2 * N) := by
  have hm : 0 < N + 1 := by linarith
  have hx1 : 1 / (N + 1) < 1 := (div_lt_one hm).2 (by linarith)
  have h := mul_le_mul_of_nonneg_left
    (fiber_entropy_upper (by positivity) hx1) hm.le
  have heq : (N + 1) * ((1 / (N + 1)) ^ 2 / (2 * (1 - 1 / (N + 1)))) =
      1 / (2 * N) := by
    field_simp [hN.ne', hm.ne']
    ring
  rwa [heq] at h

end Erdos993Lean.Analytic.V213
