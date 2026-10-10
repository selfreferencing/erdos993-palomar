module

public import Mathlib

/-!
# Binary Pinsker inequality

O1 by the two-generation reserve.
Source: the sharp first-four reserve proof ("the exact entropy
identity (3a) ... and `KL(Bernoulli(p) ‖ Bernoulli(s)) ≥ 2(p − s)²`").


For `p, s ∈ (0, 1)`,

  `KL(Ber p ‖ Ber s) = p (log p − log s) + (1 − p)(log (1 − p) − log (1 − s)) ≥ 2 (p − s)²`.

Proof (one variable, first derivative only): for fixed `p`, the defect
`f(x) = KL(Ber p ‖ Ber x) − 2 (p − x)²` has `f(p) = 0` and
`f'(x) = (x − p)(1 − 2x)² / (x (1 − x))` on `(0, 1)`, so `f` decreases on `(0, p]` and increases on
`[p, 1)`.

* `Entropy.pinsker_hasDerivAt`: the derivative of the defect.
* `Entropy.binary_pinsker`: the inequality.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve.Entropy

open Real

/-- The derivative of the binary Pinsker defect `x ↦ KL(Ber p ‖ Ber x) − 2 (p − x)²` on `(0, 1)`. -/
theorem pinsker_hasDerivAt {p x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => p * (log p - log x) + (1 - p) * (log (1 - p) - log (1 - x)) -
      2 * (p - x) ^ 2) ((x - p) * (1 - 2 * x) ^ 2 / (x * (1 - x))) x := by
  have h1 : HasDerivAt (fun x => log x) x⁻¹ x := Real.hasDerivAt_log hx0.ne'
  have h2 : HasDerivAt (fun x => log (1 - x)) (-1 / (1 - x)) x := by
    have := ((hasDerivAt_id x).const_sub 1).log (by simp; linarith)
    simpa using this
  have h3 := ((((hasDerivAt_const x (log p)).sub h1).const_mul p).add
      (((hasDerivAt_const x (log (1 - p))).sub h2).const_mul (1 - p))).sub
      ((((hasDerivAt_const x p).sub (hasDerivAt_id x)).pow 2).const_mul 2)
  convert h3 using 1
  · ext y
    rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    have hx1' : (1 - x) ≠ 0 := by linarith
    field_simp [hx0.ne', hx1']
    ring

/-- **Binary Pinsker**: `KL(Ber p ‖ Ber s) ≥ 2 (p − s)²` for `p, s ∈ (0, 1)`. -/
theorem binary_pinsker {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    2 * (p - s) ^ 2 ≤ p * (log p - log s) + (1 - p) * (log (1 - p) - log (1 - s)) := by
  let f : ℝ → ℝ := fun x => p * (log p - log x) + (1 - p) * (log (1 - p) - log (1 - x)) -
      2 * (p - x) ^ 2
  have hfp : f p = 0 := by simp only [f]; ring
  have hfs : f s = p * (log p - log s) + (1 - p) * (log (1 - p) - log (1 - s)) -
      2 * (p - s) ^ 2 := rfl
  rcases le_total p s with hps | hsp
  · have hmono : MonotoneOn f (Set.Icc p s) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p s)
      · intro x hx
        exact (pinsker_hasDerivAt (p := p) (by linarith [hx.1])
          (by linarith [hx.2])).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (pinsker_hasDerivAt (p := p) (by linarith [hx.1])
          (by linarith [hx.2])).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        apply div_nonneg
        · exact mul_nonneg (by linarith [hx.1]) (sq_nonneg _)
        · exact mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
    have := hmono ⟨le_refl p, hps⟩ ⟨hps, le_refl s⟩ hps
    linarith
  · have hanti : AntitoneOn f (Set.Icc s p) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s p)
      · intro x hx
        exact (pinsker_hasDerivAt (p := p) (by linarith [hx.1])
          (by linarith [hx.2])).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (pinsker_hasDerivAt (p := p) (by linarith [hx.1])
          (by linarith [hx.2])).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (sq_nonneg _)
        · exact mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
    have := hanti ⟨le_refl s, hsp⟩ ⟨hsp, le_refl p⟩ hsp
    linarith

end Erdos993Lean.Analytic.Reserve.Entropy
