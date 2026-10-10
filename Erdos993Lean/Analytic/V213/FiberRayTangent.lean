module

public import Erdos993Lean.Analytic.V213.FiberRootCalculus

/-!
The literal H_u polynomial, its actual first/second derivatives,
and the closed tangent bound at any positive N0. The tangent point need
not be a valid record width. No finite record is consumed here.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberRayHPolynomial (C A K delta u N : ℝ) : ℝ :=
  C + A * u * Real.sqrt N + (K + delta) * u ^ 2 * N - delta * u ^ 2 * N ^ 2

noncomputable def fiberRayHPrime (A K delta u N : ℝ) : ℝ :=
  A * u / (2 * Real.sqrt N) + (K + delta) * u ^ 2 - 2 * delta * u ^ 2 * N

noncomputable def fiberRayHSecond (A delta u N : ℝ) : ℝ :=
  -A * u / (4 * N * Real.sqrt N) - 2 * delta * u ^ 2

theorem fiber_ray_H_hasDerivAt (C A K delta u : ℝ) {N : ℝ} (hN : 0 < N) :
    HasDerivAt (fiberRayHPolynomial C A K delta u) (fiberRayHPrime A K delta u N) N := by
  have hs := (Real.hasDerivAt_sqrt hN.ne').const_mul (A * u)
  have hl := (hasDerivAt_id N).const_mul ((K + delta) * u ^ 2)
  have hq := ((hasDerivAt_id N).pow 2).const_mul (delta * u ^ 2)
  convert (((hasDerivAt_const N C).add hs).add hl).sub hq using 1
  · funext x
    dsimp [fiberRayHPolynomial] <;> ring
  · dsimp [fiberRayHPrime] <;> ring

theorem fiber_ray_HPrime_hasDerivAt (A K delta u : ℝ) {N : ℝ} (hN : 0 < N) :
    HasDerivAt (fiberRayHPrime A K delta u) (fiberRayHSecond A delta u N) N := by
  have hs0 := Real.sqrt_pos.mpr hN
  have hs := (hasDerivAt_const N (A * u)).div
    ((Real.hasDerivAt_sqrt hN.ne').const_mul 2) (by positivity : 2 * Real.sqrt N ≠ 0)
  have hl := (hasDerivAt_id N).const_mul (2 * delta * u ^ 2)
  convert (hs.add (hasDerivAt_const N ((K + delta) * u ^ 2))).sub hl using 1
  · funext x
    dsimp [fiberRayHPrime] <;> ring
  · dsimp [fiberRayHSecond]
    have hsq := Real.sq_sqrt hN.le
    field_simp [hs0.ne',hN.ne']
    linear_combination (-4 * A * u) * hsq

theorem fiber_ray_HSecond_nonpos {A delta u N : ℝ}
    (hA : 0 ≤ A) (hd : 0 ≤ delta) (hu : 0 ≤ u) (hN : 0 < N) :
    fiberRayHSecond A delta u N ≤ 0 := by
  have hs0 := Real.sqrt_pos.mpr hN
  unfold fiberRayHSecond
  have h1 : 0 ≤ A * u / (4 * N * Real.sqrt N) := by positivity
  have h2 : 0 ≤ 2 * delta * u ^ 2 := by positivity
  simp only [neg_mul,neg_div]
  linarith only [h1,h2]

/-- Exact nonnegative tangent remainder, including N=0. -/
theorem fiber_ray_H_tangent_identity (C A K delta u : ℝ) {N N0 : ℝ}
    (hN : 0 ≤ N) (hN0 : 0 < N0) :
    fiberRayHPolynomial C A K delta u N0 + fiberRayHPrime A K delta u N0 * (N - N0) -
      fiberRayHPolynomial C A K delta u N =
      A * u * (Real.sqrt N - Real.sqrt N0) ^ 2 / (2 * Real.sqrt N0) +
        delta * u ^ 2 * (N - N0) ^ 2 := by
  have hs0 := Real.sqrt_pos.mpr hN0
  have hs := Real.sq_sqrt hN
  have hs' := Real.sq_sqrt hN0.le
  unfold fiberRayHPolynomial fiberRayHPrime
  field_simp [hs0.ne']
  linear_combination A * u * hs' - A * u * hs

theorem fiber_ray_H_tangent {C A K delta u N N0 : ℝ}
    (hA : 0 ≤ A) (hd : 0 ≤ delta) (hu : 0 ≤ u) (hN : 0 ≤ N) (hN0 : 0 < N0) :
    fiberRayHPolynomial C A K delta u N ≤ fiberRayHPolynomial C A K delta u N0 +
      fiberRayHPrime A K delta u N0 * (N - N0) := by
  have hid := fiber_ray_H_tangent_identity C A K delta u hN hN0
  have hs0 := Real.sqrt_pos.mpr hN0
  have hr : 0 ≤ A * u * (Real.sqrt N - Real.sqrt N0) ^ 2 / (2 * Real.sqrt N0) +
      delta * u ^ 2 * (N - N0) ^ 2 := by positivity
  linarith only [hid,hr]

theorem fiber_ray_tangent_max {C A K delta u M m t f g : ℝ}
    (hA : 0 ≤ A) (hd : 0 ≤ delta) (hu : 0 ≤ u)
    (hM : 0 < M) (hm : 0 < m) (ht : 0 < t) (hmt : m * t ≤ M) :
    max 0 (f + g + t / M * fiberRayHPolynomial C A K delta u (M + 2)) ≤
      max 0 (max (f + g + fiberRayHPolynomial C A K delta u (m * t + 2) / m)
        (f + g + t * fiberRayHPrime A K delta u (m * t + 2))) := by
  have hN0 : 0 < m * t + 2 := by positivity
  have htan := fiber_ray_H_tangent (C := C) (K := K) hA hd hu
    (by linarith only [hM] : 0 ≤ M + 2) hN0
  have hw1 : 0 ≤ m * t / M := by positivity
  have hw2 : 0 ≤ (M - m * t) / M := div_nonneg (sub_nonneg.mpr hmt) hM.le
  have hsum : m * t / M + (M - m * t) / M = 1 := by field_simp [hM.ne'] <;> ring
  let D := f + g + fiberRayHPolynomial C A K delta u (m * t + 2) / m
  let E := f + g + t * fiberRayHPrime A K delta u (m * t + 2)
  have hid : f + g + t / M * (fiberRayHPolynomial C A K delta u (m * t + 2) +
      fiberRayHPrime A K delta u (m * t + 2) * ((M + 2) - (m * t + 2))) =
      m * t / M * D + (M - m * t) / M * E := by
    dsimp [D,E]
    field_simp [hM.ne',hm.ne']
    ring
  have hupper : f + g + t / M * fiberRayHPolynomial C A K delta u (M + 2) ≤ max D E := by
    have htM : 0 ≤ t / M := by positivity
    have h1 := mul_le_mul_of_nonneg_left htan htM
    have hD := mul_le_mul_of_nonneg_left (le_max_left D E) hw1
    have hE := mul_le_mul_of_nonneg_left (le_max_right D E) hw2
    have hends : m * t / M * D + (M - m * t) / M * E ≤ max D E := by
      calc
        _ ≤ (m * t / M + (M - m * t) / M) * max D E := by nlinarith only [hD,hE]
        _ = _ := by rw [hsum,one_mul]
    calc
      _ ≤ m * t / M * D + (M - m * t) / M * E := by linarith only [h1,hid]
      _ ≤ _ := hends
  exact max_le_max (le_refl 0) hupper

end Erdos993Lean.Analytic.V213
