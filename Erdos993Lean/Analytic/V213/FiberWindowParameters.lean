module

public import Erdos993Lean.Analytic.V213.FiberRationalGainCalculus
public import Erdos993Lean.Analytic.V213.FiberRationalGainBinding
public import Erdos993Lean.Analytic.V213.FiberCoefficientBounds

/-!
Eq102: literal window rate and bonus parameters. The rate comparison
uses the printed square identity; its full-domain monotonicity and 29/65
floor are proved, not supplied by a sampled window. Delta monotonicity
follows directly from its actual definition. The two cross-multiplication
proofs are adapted from an earlier development,
without importing any old conditional finite-window route.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberWindowRho (b N : ℝ) : ℝ :=
  (1 - b ^ 2) * N / (N + 1) -
    (2 / (N + 1) + b ^ 2 / (3 * (1 - b ^ 2))) * (2 * N - 1) / (2 * (N - 1))

noncomputable def fiberWindowDelta (a N : ℝ) : ℝ :=
  a ^ 2 * (N ^ 2 - N + 1) / ((1 - a ^ 2) * N)

theorem fiber_window_rho_reciprocal_form {b N : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hN : 1 < N) :
    fiberWindowRho b N =
      (1 - b ^ 2) - b ^ 2 / (3 * (1 - b ^ 2)) -
        ((1 - b ^ 2) + 3 / 2) / (N + 1) -
          (1 / 2 + b ^ 2 / (6 * (1 - b ^ 2))) / (N - 1) := by
  have hp : N + 1 ≠ 0 := ne_of_gt (by linarith : 0 < N + 1)
  have hm : N - 1 ≠ 0 := ne_of_gt (by linarith : 0 < N - 1)
  have ho : 1 - b ^ 2 ≠ 0 := ne_of_gt (by nlinarith : 0 < 1 - b ^ 2)
  unfold fiberWindowRho
  field_simp [hp,hm,ho] <;> ring

theorem fiber_window_rho_width_mono {b N0 N : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hN0 : 1 < N0) (hN : N0 ≤ N) : fiberWindowRho b N0 ≤ fiberWindowRho b N := by
  have ho : 0 < 1 - b ^ 2 := by nlinarith
  have hplus := div_le_div_of_nonneg_left (show 0 ≤ (1 - b ^ 2) + 3 / 2 by linarith)
    (show 0 < N0 + 1 by linarith) (show N0 + 1 ≤ N + 1 by linarith)
  have hminus := div_le_div_of_nonneg_left (show 0 ≤ 1 / 2 + b ^ 2 / (6 * (1 - b ^ 2)) by positivity)
    (show 0 < N0 - 1 by linarith) (show N0 - 1 ≤ N - 1 by linarith)
  rw [fiber_window_rho_reciprocal_form hb0 hbh hN0,
    fiber_window_rho_reciprocal_form hb0 hbh (by linarith : 1 < N)]
  linarith only [hplus,hminus]

theorem fiber_window_rho_skew_antitone {a b N : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbh : b ≤ 1 / 2) (hN : 1 < N) : fiberWindowRho b N ≤ fiberWindowRho a N := by
  have hs : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha0 (ha0.trans hab)).2 hab
  have hfirst := mul_le_mul_of_nonneg_right (show 1 - b ^ 2 ≤ 1 - a ^ 2 by linarith)
    (show 0 ≤ N / (N + 1) by apply div_nonneg <;> linarith)
  have hf := fiber_rational_skew_fraction ha0 hab hbh
  have hthird := div_le_div_of_nonneg_right hf (by norm_num : (0 : ℝ) ≤ 3)
  have hthird' : a ^ 2 / (3 * (1 - a ^ 2)) ≤ b ^ 2 / (3 * (1 - b ^ 2)) := by
    simpa only [div_div,mul_comm] using hthird
  have hfactor : 0 ≤ (2 * N - 1) / (2 * (N - 1)) := by
    apply div_nonneg <;> linarith
  have hsecond := mul_le_mul_of_nonneg_right
    (add_le_add_left hthird' (2 / (N + 1))) hfactor
  unfold fiberWindowRho
  simp only [div_eq_mul_inv] at hfirst hsecond ⊢
  nlinarith only [hfirst,hsecond]

theorem fiber_window_rho_floor {b N : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hN : 14 ≤ N) : 29 / 65 ≤ fiberWindowRho b N := by
  have hwidth := fiber_window_rho_width_mono (b := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num : (1 : ℝ) < 14) hN
  have hskew := fiber_window_rho_skew_antitone hb0 hbh (le_refl (1 / 2 : ℝ))
    (by linarith : 1 < N)
  have he : fiberWindowRho (1 / 2) 14 = (29 / 65 : ℝ) := by norm_num [fiberWindowRho]
  rw [he] at hwidth
  exact hwidth.trans hskew

theorem fiber_window_rho_strict {b N : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hN : 14 ≤ N) : 2 / 5 < fiberWindowRho b N := by
  have h := fiber_window_rho_floor hb0 hbh hN
  linarith

theorem fiber_window_rho_square_identity {N : ℝ} (hN : 1 < N) :
    ((2 * N - 1) / (2 * (N - 1))) ^ 2 * (1 - 1 / N) =
      1 + 1 / (4 * N * (N - 1)) := by
  have hn : N ≠ 0 := ne_of_gt (by linarith : 0 < N)
  have hm : N - 1 ≠ 0 := ne_of_gt (by linarith : 0 < N - 1)
  field_simp [hn,hm] <;> ring

theorem fiber_window_rho_star {b N : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hN : 1 < N) : fiberWindowRho b N ≤ V22.rhoStar N b := by
  have hn : 0 < N := by linarith
  have hm : 0 < N - 1 := by linarith
  have ho : 0 < 1 - b ^ 2 := by nlinarith
  have hc : 0 < 1 - 1 / N := by
    have h := (div_lt_one hn).2 hN
    linarith
  have hs : 0 < Real.sqrt (1 - 1 / N) := Real.sqrt_pos.2 hc
  have hp : 0 ≤ (2 * N - 1) / (2 * (N - 1)) := by
    apply div_nonneg <;> linarith
  have he := fiber_window_rho_square_identity hN
  have hsq := Real.sq_sqrt hc.le
  have hprod : 1 ≤ ((2 * N - 1) / (2 * (N - 1)) * Real.sqrt (1 - 1 / N)) ^ 2 := by
    rw [mul_pow,hsq,he]
    have hh : 0 ≤ 1 / (4 * N * (N - 1)) := by positivity
    linarith
  have hroot : 1 ≤ (2 * N - 1) / (2 * (N - 1)) * Real.sqrt (1 - 1 / N) := by
    nlinarith only [hprod,mul_nonneg hp hs.le]
  have hinv : 1 / Real.sqrt (1 - 1 / N) ≤ (2 * N - 1) / (2 * (N - 1)) :=
    (div_le_iff₀ hs).2 hroot
  have hk : 0 ≤ 2 / (N + 1) + b ^ 2 / (3 * (1 - b ^ 2)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hinv hk
  rw [fiber_rhoStar_formula]
  unfold fiberWindowRho V22.rho
  simp only [div_eq_mul_inv,one_mul] at hmul ⊢
  nlinarith only [hmul]

theorem fiber_window_delta_actual (a N : ℝ) : fiberWindowDelta a N = V22.Delta a N := rfl

theorem fiber_window_delta_skew_mono {a r N : ℝ} (ha : 0 ≤ a) (har : a ≤ r)
    (hrh : r ≤ 1 / 2) (hN : 1 ≤ N) : V22.Delta a N ≤ V22.Delta r N := by
  have hn : 0 < N := by linarith
  have hda := shared_one_sub_sq_pos (by linarith : -1 < a) (by linarith : a < 1)
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hs : a ^ 2 ≤ r ^ 2 := by nlinarith
  have hp : 0 ≤ N ^ 2 - N + 1 := by nlinarith [sq_nonneg (N - 1)]
  unfold V22.Delta
  apply (div_le_div_iff₀ (mul_pos hda hn) (mul_pos hdr hn)).2
  have h := mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg hp hn.le)
  nlinarith only [h]

theorem fiber_window_delta_width_mono {r N0 N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hN0 : 1 ≤ N0) (hN : N0 ≤ N) : V22.Delta r N0 ≤ V22.Delta r N := by
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have h0 : 0 < N0 := by linarith
  have hn : 0 < N := by linarith
  unfold V22.Delta
  apply (div_le_div_iff₀ (mul_pos hd h0) (mul_pos hd hn)).2
  have hpay := mul_nonneg (show 0 ≤ (N - N0) * (N * N0 - 1) from
    mul_nonneg (sub_nonneg.mpr hN) (by nlinarith)) (mul_nonneg (sq_nonneg r) hd.le)
  nlinarith only [hpay]

end Erdos993Lean.Analytic.V213
