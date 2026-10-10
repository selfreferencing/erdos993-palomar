module

public import Erdos993Lean.Analytic.V213.FiberUniformGain
public import Erdos993Lean.Analytic.V213.FiberAffineMonotonicity

/-!
The first two literal Eq86 width-uniform estimates.
The epsilon estimate uses the exact gamma radius,
including its r(N-1) lower bound. No finite family is consumed.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_wing_radius_bounds {r N : ℝ} (hr : 0 ≤ r) (hN : 1 ≤ N) :
    Real.sqrt N ≤ fiberUpperRadius r N ∧ r * (N - 1) ≤ fiberUpperRadius r N := by
  have hn : 0 ≤ N := by linarith
  constructor
  · unfold fiberUpperRadius
    exact Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (r * (N - 1))] : N ≤ N + r ^ 2 * (N - 1) ^ 2)
  · unfold fiberUpperRadius
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hn]

theorem fiber_wing_epsilon_ratio {r N : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 5)
    (hN : 13 ≤ N) :
    V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ≤
      2 * r * Real.sqrt N / (N + 1) + r ^ 2 * N / (3 * (N - 1)) := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have hnm : 0 < N - 1 := by linarith
  have ha : 0 < 1 - r ^ 2 := by nlinarith
  have hR := fiberUpperRadius_pos (r := r) hn
  have hRsq : (fiberUpperRadius r N) ^ 2 = N + r ^ 2 * (N - 1) ^ 2 := by
    unfold fiberUpperRadius
    rw [Real.sq_sqrt (by positivity)]
  have hg : 0 < V22.gamma r N := by
    rw [fiber_gamma_radius hr.le (by linarith) (by linarith)]
    positivity
  have hs : 0 < Real.sqrt (V22.gamma r N) := Real.sqrt_pos.2 hg
  have hss := Real.sq_sqrt hg.le
  have he := fiber_epsilon_radius hr.le (by linarith : r < 1) (by linarith : 1 < N)
  have hgamma := fiber_gamma_radius hr.le (by linarith : r < 1) (by linarith : 1 < N)
  have hid : V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) =
      (2 * r / (N + 1) + V22.aHat r) * ((1 - r ^ 2) * N) / fiberUpperRadius r N := by
    apply (div_eq_iff hs.ne').2
    apply (mul_right_cancel₀ hs.ne')
    have he' : V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) =
        (2 * r / (N + 1) + V22.aHat r) * fiberUpperRadius r N := by
      rw [he]
      unfold V22.yTilde
      field_simp [hm.ne'] <;> ring
    rw [he', mul_assoc, ← pow_two, hss, hgamma]
    field_simp [hR.ne', ha.ne', hn.ne'] <;> ring
  have hradius := fiber_wing_radius_bounds hr.le (by linarith : 1 ≤ N)
  have hsN := Real.sq_sqrt hn.le
  have hNroot : N ≤ Real.sqrt N * fiberUpperRadius r N := by
    nlinarith only [hradius.1, hsN, Real.sqrt_nonneg N]
  have hbase : (2 * r / (N + 1)) * ((1 - r ^ 2) * N) / fiberUpperRadius r N ≤
      2 * r * Real.sqrt N / (N + 1) := by
    apply (div_le_iff₀ hR).2
    have haN : (1 - r ^ 2) * N ≤ N := by nlinarith only [sq_nonneg r, hn.le]
    have hb := mul_le_mul_of_nonneg_left (haN.trans hNroot)
      (by positivity : 0 ≤ 2 * r / (N + 1))
    convert hb using 1 <;> ring
  have hA := (sharedAHat_bounds hr.le (by linarith : r < 1)).2
  have hAt := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ (1 - r ^ 2) * N)) hR.le
  have hcancel : (r ^ 3 / (3 * (1 - r ^ 2))) * ((1 - r ^ 2) * N) /
      fiberUpperRadius r N = r ^ 3 * N / (3 * fiberUpperRadius r N) := by
    field_simp [ha.ne', hR.ne'] <;> ring
  rw [hcancel] at hAt
  have hsmall : r ^ 3 * N / (3 * fiberUpperRadius r N) ≤
      r ^ 2 * N / (3 * (N - 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * fiberUpperRadius r N)
      (by positivity : 0 < 3 * (N - 1))).2
    have hp := mul_le_mul_of_nonneg_left hradius.2 (by positivity : 0 ≤ 3 * r ^ 2 * N)
    nlinarith only [hp]
  rw [hid]
  have hsplit : (2 * r / (N + 1) + V22.aHat r) * ((1 - r ^ 2) * N) /
      fiberUpperRadius r N =
      (2 * r / (N + 1)) * ((1 - r ^ 2) * N) / fiberUpperRadius r N +
      V22.aHat r * ((1 - r ^ 2) * N) / fiberUpperRadius r N := by ring
  rw [hsplit]
  linarith only [hbase, hAt, hsmall]

theorem fiber_wing_rate_uniform {N N0 r b : ℝ} (hN0 : 13 ≤ N0) (hNN : N0 ≤ N)
    (hr : 0 < r) (hrb : r ≤ b) (hbh : b ≤ 1 / 5) :
    (1 - b ^ 2) * N0 / (N0 + 1) - 2 * b * Real.sqrt N0 / (N0 + 1) -
      b ^ 2 * N0 / (3 * (N0 - 1)) ≤ V22.rhoU r N := by
  have hN : 13 ≤ N := hN0.trans hNN
  have hb : 0 ≤ b := hr.le.trans hrb
  have hrsq : r ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hr.le hb).2 hrb
  have ha : 0 ≤ 1 - b ^ 2 := by nlinarith
  have hn0 : 0 < N0 + 1 := by linarith
  have hn : 0 < N + 1 := by linarith
  have ht0 : 0 < N0 - 1 := by linarith
  have ht : 0 < N - 1 := by linarith
  have hratio : N0 / (N0 + 1) ≤ N / (N + 1) := by
    apply (div_le_div_iff₀ hn0 hn).2
    nlinarith only [hNN]
  have hbase : (1 - b ^ 2) * N0 / (N0 + 1) ≤ (1 - r ^ 2) * V22.rho N := by
    unfold V22.rho
    have h1 := mul_le_mul_of_nonneg_left hratio ha
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 1 - b ^ 2 ≤ 1 - r ^ 2)
      (by positivity : 0 ≤ N / (N + 1))
    convert h1.trans h2 using 1 <;> ring
  have hroot := fiber_sqrt_ratio_antitone (by linarith : 1 ≤ N0) hNN
  have hterm1 : 2 * r * Real.sqrt N / (N + 1) ≤ 2 * b * Real.sqrt N0 / (N0 + 1) := by
    have h1 := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 2 * r)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * r ≤ 2 * b)
      (by positivity : 0 ≤ Real.sqrt N0 / (N0 + 1))
    convert h1.trans h2 using 1 <;> ring
  have hrational : N / (N - 1) ≤ N0 / (N0 - 1) := by
    apply (div_le_div_iff₀ ht ht0).2
    nlinarith only [hNN]
  have hterm2 : r ^ 2 * N / (3 * (N - 1)) ≤ b ^ 2 * N0 / (3 * (N0 - 1)) := by
    have h1 := mul_le_mul_of_nonneg_left hrational (by positivity : 0 ≤ r ^ 2 / 3)
    have h2 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hrsq (by norm_num : (0 : ℝ) ≤ 3))
      (by positivity : 0 ≤ N0 / (N0 - 1))
    convert h1.trans h2 using 1 <;> field_simp [ht.ne', ht0.ne'] <;> ring
  have he := fiber_wing_epsilon_ratio hr (hrb.trans hbh) hN
  unfold V22.rhoU
  linarith only [hbase, he, hterm1, hterm2]

theorem fiber_wing_bonus_uniform {N N0 a r : ℝ} (hN0 : 13 ≤ N0) (hNN : N0 ≤ N)
    (ha : 0 < a) (har : a ≤ r) (hrh : r ≤ 1 / 5) :
    a ^ 2 * (N0 - 1) ≤ V22.Delta r N := by
  have hr : 0 < r := ha.trans_le har
  have hn : 0 < N := by linarith
  have hnm : 0 ≤ N - 1 := by linarith
  have hab : 0 < 1 - r ^ 2 := by nlinarith
  have hs : a ^ 2 ≤ r ^ 2 := (sq_le_sq₀ ha.le hr.le).2 har
  have h1 := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ N0 - 1)
  have h2 := mul_le_mul_of_nonneg_left (by linarith : N0 - 1 ≤ N - 1) (sq_nonneg r)
  have h3 : r ^ 2 * (N - 1) ≤ V22.Delta r N := by
    unfold V22.Delta
    apply (le_div_iff₀ (mul_pos hab hn)).2
    have he : (r ^ 2 * (N - 1)) * ((1 - r ^ 2) * N) ≤ r ^ 2 * (N - 1) * N := by
      have h := mul_le_mul_of_nonneg_left (by nlinarith : 1 - r ^ 2 ≤ 1)
        (by positivity : 0 ≤ r ^ 2 * (N - 1) * N)
      nlinarith only [h]
    nlinarith only [he]
  exact (h1.trans h2).trans h3

end Erdos993Lean.Analytic.V213
