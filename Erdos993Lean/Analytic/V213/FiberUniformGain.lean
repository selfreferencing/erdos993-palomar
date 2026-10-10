module

public import Erdos993Lean.Analytic.V213.FiberUpperDefinitions

/-!
Uniform gain: the exact real-width Eq78 formula. The radius cancellation
proof is adapted from an earlier development,
without importing its old conditional finite-certificate route. The actual
Phi definition and all domains are the quantities of version 2.13 of the manuscript.
No finite DF10 family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberUpperRadius (r N : ℝ) : ℝ := Real.sqrt (N + r ^ 2 * (N - 1) ^ 2)

noncomputable def fiberPhiExplicit (r m : ℝ) : ℝ :=
  (71 / 20) / m + r ^ 2 / 2 * (m - 4 + 4 / m) -
    (2 * r / m + V22.aHat r) * fiberUpperRadius r (m - 1) - m * V22.cr r +
      2 * r ^ 2 / m + 2 * r * V22.aHat r + (V22.aHat r) ^ 2 * m / 2

theorem fiberUpperRadius_pos {r N : ℝ} (hN : 0 < N) : 0 < fiberUpperRadius r N := by
  unfold fiberUpperRadius
  apply Real.sqrt_pos.2
  positivity

theorem fiber_gamma_radius {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 1 < N) :
    V22.gamma r N = (fiberUpperRadius r N) ^ 2 / ((1 - r ^ 2) * N) := by
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hn : 0 < N := by linarith
  unfold fiberUpperRadius
  rw [Real.sq_sqrt (by positivity : 0 ≤ N + r ^ 2 * (N - 1) ^ 2)]
  unfold V22.gamma V22.Delta
  field_simp [hd.ne', hn.ne'] <;> ring

/-- The exact combined epsilon term, retaining the actual bonus radius. -/
theorem fiber_epsilon_radius {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 1 < N) :
    V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) =
      2 * V22.yTilde r N * fiberUpperRadius r N / (N + 1) := by
  have hn : 0 < N := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hR := fiberUpperRadius_pos (r := r) hn
  have hgamma : 0 < V22.gamma r N := by
    unfold V22.gamma
    have hD := delta_nonneg (by linarith : 1 ≤ N) (by linarith [shared_one_sub_sq_pos (by linarith : -1 < r) hr1] : r ^ 2 < 1)
    linarith
  have hs := shared_sN_sq hr0 hr1 hn
  have hsN : 0 ≤ V22.sN r N := by
    unfold V22.sN
    exact Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt hgamma.le
  have hprod : (2 * V22.sN r N * Real.sqrt (V22.gamma r N)) ^ 2 = (fiberUpperRadius r N) ^ 2 := by
    rw [mul_pow, mul_pow, hs, hsq, fiber_gamma_radius hr0 hr1 hN]
    unfold V22.varianceR
    field_simp [(shared_one_sub_sq_pos (by linarith : -1 < r) hr1).ne', hn.ne'] <;> ring
  have he : 2 * V22.sN r N * Real.sqrt (V22.gamma r N) = fiberUpperRadius r N :=
    (sq_eq_sq₀ (by positivity) hR.le).1 hprod
  unfold V22.epsilonPrime
  calc
    (4 * V22.yTilde r N * V22.sN r N / (N + 1)) * Real.sqrt (V22.gamma r N) =
        2 * V22.yTilde r N * (2 * V22.sN r N * Real.sqrt (V22.gamma r N)) / (N + 1) := by ring
    _ = _ := by rw [he]

/-- Current Lemma 6.10 / Eq78's explicit expression, on its analytic real domain. -/
theorem fiber_phi_formula {r N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 1 < N) :
    V22.phiR r N = fiberPhiExplicit r (N + 1) := by
  have hr1 : r < 1 := by linarith
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hn : 0 < N := by linarith
  have hD := delta_nonneg (by linarith : 1 ≤ N) (by nlinarith : r ^ 2 < 1)
  have hg : 0 < V22.gamma r N := by unfold V22.gamma; linarith
  have hs := Real.sqrt_pos.2 hg
  have hsq := Real.sq_sqrt hg.le
  have heps := fiber_epsilon_radius hr0 hr1 hN
  have hN1 : 0 < N + 1 := by linarith
  have hdeltaSq : V22.Delta r N = (Real.sqrt (V22.gamma r N)) ^ 2 - 1 := by
    rw [hsq]
    unfold V22.gamma
    ring
  have hEpsilonCancel :
      (V22.epsilonPrime r N / Real.sqrt (V22.gamma r N)) / 2 * V22.Delta r N +
        V22.epsilonPrime r N / 2 *
          (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N)) =
      V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) := by
    rw [hdeltaSq]
    field_simp [hs.ne'] <;> ring
  have hQuadraticCancel :
      ((1 - r ^ 2) * V22.rho N) / 2 * V22.Delta r N - r ^ 2 * V22.rho N / 2 =
        r ^ 2 * (N - 1) ^ 2 / (2 * (N + 1)) := by
    unfold V22.rho V22.Delta
    field_simp [hd.ne', hn.ne', hN1.ne'] <;> ring
  have hbase : V22.phiR r N = (71 / 20 : ℝ) / (N + 1) +
      r ^ 2 * (N - 1) ^ 2 / (2 * (N + 1)) - V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) -
        (N + 1) * V22.cr r + 2 * (V22.yTilde r N) ^ 2 / (N + 1) := by
    calc
      V22.phiR r N = (71 / 20 : ℝ) / (N + 1) +
          (((1 - r ^ 2) * V22.rho N) / 2 * V22.Delta r N - r ^ 2 * V22.rho N / 2) -
          ((V22.epsilonPrime r N / Real.sqrt (V22.gamma r N)) / 2 * V22.Delta r N +
            V22.epsilonPrime r N / 2 *
              (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N))) -
          (N + 1) * V22.cr r + 2 * (V22.yTilde r N) ^ 2 / (N + 1) := by
        unfold V22.phiR V22.rhoU V22.eU V22.c0Prime
        ring
      _ = _ := by rw [hQuadraticCancel, hEpsilonCancel]
  rw [hbase, heps]
  unfold fiberPhiExplicit V22.yTilde
  norm_num only [add_sub_cancel_right]
  field_simp [ne_of_gt (by linarith : 0 < N + 1)] <;> ring

noncomputable def fiberGainD (m : ℝ) : ℝ := 61 / (20 * m) - 1 / (2 * (m - 2))

noncomputable def fiberGainC (b m : ℝ) : ℝ :=
  ((1 - b ^ 2 / (3 * (1 - b ^ 2))) * m - 4) ^ 2 / (2 * m) -
    (m - 1) / (6 * (1 - b ^ 2) * (m - 2)) - b ^ 2 * m / (12 * (1 - b ^ 2) ^ 2)

theorem fiber_gain_D_lower {m : ℝ} (hm : 11 ≤ m) :
    439 / (180 * m) ≤ fiberGainD m := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hx : 1 / (m - 2) ≤ (1 / 9 : ℝ) := by
    apply (div_le_iff₀ hm2).2
    linarith
  have he : fiberGainD m = (51 / 20 - 1 / (m - 2)) / m := by
    unfold fiberGainD
    field_simp [hm0.ne', hm2.ne'] <;> ring
  rw [he]
  apply (le_div_iff₀ hm0).2
  field_simp
  linarith

theorem fiber_gain_C_half_formula {m : ℝ} (hm : 11 ≤ m) :
    fiberGainC (1 / 2) m = 29 * m / 81 - 34 / 9 + 8 / m - 2 / (9 * (m - 2)) := by
  unfold fiberGainC
  norm_num
  field_simp [ne_of_gt (by linarith : 0 < m), ne_of_gt (by linarith : 0 < m - 2)] <;> ring

theorem fiber_gain_C_half_lower {m : ℝ} (hm : 11 ≤ m) :
    769 / 891 ≤ fiberGainC (1 / 2) m := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hx : 8 / (11 * m) ≤ (8 / 121 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 11 * m)).2
    linarith
  have hf : 0 < 29 / 81 - 8 / (11 * m) + 2 / (81 * (m - 2)) := by
    have hp : 0 ≤ 2 / (81 * (m - 2)) := by positivity
    linarith
  have he : fiberGainC (1 / 2) m - 769 / 891 =
      (m - 11) * (29 / 81 - 8 / (11 * m) + 2 / (81 * (m - 2))) := by
    rw [fiber_gain_C_half_formula hm]
    field_simp [hm0.ne', hm2.ne'] <;> ring
  have hp := mul_nonneg (sub_nonneg.mpr hm) hf.le
  rw [← he] at hp
  linarith

theorem fiber_gain_C_lower {b m : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hm : 11 ≤ m) : fiberGainC (1 / 2) m ≤ fiberGainC b m := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have ha : 3 / 4 ≤ 1 - b ^ 2 := by nlinarith
  have ha0 : 0 < 1 - b ^ 2 := by linarith
  have hp : 8 / 9 ≤ 1 - b ^ 2 / (3 * (1 - b ^ 2)) := by
    have hx : b ^ 2 / (3 * (1 - b ^ 2)) ≤ (1 / 9 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - b ^ 2))).2
      nlinarith
    linarith
  have hpm : 0 ≤ 8 * m / 9 - 4 := by linarith
  have hsq : (8 * m / 9 - 4) ^ 2 ≤
      ((1 - b ^ 2 / (3 * (1 - b ^ 2))) * m - 4) ^ 2 := by
    apply (sq_le_sq₀ hpm (by nlinarith)).2
    nlinarith
  have hterm1 := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2 * m)
  have hterm2 : (m - 1) / (6 * (1 - b ^ 2) * (m - 2)) ≤
      2 * (m - 1) / (9 * (m - 2)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 6 * (1 - b ^ 2) * (m - 2))
      (by positivity : 0 < 9 * (m - 2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ m - 1)
      (mul_nonneg (by linarith : 0 ≤ m - 2) (by linarith : 0 ≤ 4 * (1 - b ^ 2) - 3))]
  have hterm3 : b ^ 2 * m / (12 * (1 - b ^ 2) ^ 2) ≤ m / 27 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 12 * (1 - b ^ 2) ^ 2)
      (by norm_num : (0 : ℝ) < 27)).2
    have hs : (3 / 4 : ℝ) ^ 2 ≤ (1 - b ^ 2) ^ 2 :=
      (sq_le_sq₀ (by norm_num) ha0.le).2 ha
    nlinarith [mul_le_mul_of_nonneg_right hs hm0.le,
      mul_le_mul_of_nonneg_right (by nlinarith : b ^ 2 ≤ (1 / 4 : ℝ)) hm0.le]
  rw [fiber_gain_C_half_formula hm]
  unfold fiberGainC
  have he : (8 * m / 9 - 4) ^ 2 / (2 * m) -
      2 * (m - 1) / (9 * (m - 2)) - m / 27 =
      29 * m / 81 - 34 / 9 + 8 / m - 2 / (9 * (m - 2)) := by
    field_simp [hm0.ne', hm2.ne'] <;> ring
  linarith

theorem fiber_phi_radius_upper {r m : ℝ} (hr : 0 < r) (hm : 2 < m) :
    fiberUpperRadius r (m - 1) ≤ r * (m - 2) + (m - 1) / (2 * r * (m - 2)) := by
  have ht : 0 < r * (m - 2) := mul_pos hr (by linarith)
  have hnum : 0 ≤ m - 1 := by linarith
  have hb : 0 ≤ (m - 1) / (2 * r * (m - 2)) := by positivity
  have he : 2 * (r * (m - 2)) * ((m - 1) / (2 * r * (m - 2))) = m - 1 := by
    field_simp [hr.ne', ne_of_gt (by linarith : 0 < m - 2)] <;> ring
  unfold fiberUpperRadius
  apply Real.sqrt_le_iff.2
  constructor
  · positivity
  · nlinarith [sq_nonneg ((m - 1) / (2 * r * (m - 2)))]

theorem fiber_phi_completed_square {r N : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2)
    (hN : 10 ≤ N) :
    71 / (20 * (N + 1)) + (r * (N + 1 - 4) - (N + 1) * V22.aHat r) ^ 2 /
        (2 * (N + 1)) - N / ((N + 1) * (N + 1 - 2)) -
      V22.aHat r * N / (2 * r * (N + 1 - 2)) - (N + 1) * V22.cr r ≤ V22.phiR r N := by
  have hn : 0 < N + 1 := by linarith
  have ht : 0 < N + 1 - 2 := by linarith
  have hcoeff : 0 ≤ 2 * r / (N + 1) + V22.aHat r :=
    add_nonneg (by positivity) (sharedAHat_bounds hr.le (by linarith)).1
  have hs := mul_le_mul_of_nonneg_left (fiber_phi_radius_upper hr (by linarith : 2 < N + 1)) hcoeff
  simp only [add_sub_cancel_right] at hs
  rw [fiber_phi_formula hr.le hrh (by linarith)]
  have he : fiberPhiExplicit r (N + 1) +
      (2 * r / (N + 1) + V22.aHat r) * fiberUpperRadius r (N + 1 - 1) -
      (2 * r / (N + 1) + V22.aHat r) *
        (r * (N + 1 - 2) + N / (2 * r * (N + 1 - 2))) =
      71 / (20 * (N + 1)) + (r * (N + 1 - 4) - (N + 1) * V22.aHat r) ^ 2 /
        (2 * (N + 1)) - N / ((N + 1) * (N + 1 - 2)) -
        V22.aHat r * N / (2 * r * (N + 1 - 2)) - (N + 1) * V22.cr r := by
    unfold fiberPhiExplicit
    field_simp [hn.ne', ht.ne', hr.ne'] <;> ring
  rw [← he]
  simp only [add_sub_cancel_right]
  linarith [hs]

theorem fiber_uniform_phi_lower_pos {r b m : ℝ} (hr : 0 < r) (hrb : r ≤ b)
    (hbh : b ≤ 1 / 2) (hm : 11 ≤ m) :
    fiberGainD m + r ^ 2 * fiberGainC b m ≤ V22.phiR r (m - 1) := by
  have hb0 : 0 ≤ b := hr.le.trans hrb
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hnum : 0 ≤ m - 1 := by linarith
  have ha : 3 / 4 ≤ 1 - b ^ 2 := by nlinarith
  have ha0 : 0 < 1 - b ^ 2 := by linarith
  have hrh : r ≤ 1 / 2 := hrb.trans hbh
  have har : 0 < 1 - r ^ 2 := by nlinarith
  have hs : r ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hr.le hb0).2 hrb
  have hA : V22.aHat r ≤ r ^ 3 / (3 * (1 - b ^ 2)) :=
    (sharedAHat_bounds hr.le (by linarith)).2.trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
  have hA2 : V22.aHat r ≤ r * b ^ 2 / (3 * (1 - b ^ 2)) :=
    hA.trans (div_le_div_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left hs hr.le]) (by positivity))
  have hcr : V22.cr r ≤ b ^ 2 * r ^ 2 / (12 * (1 - b ^ 2) ^ 2) := by
    have hden : (1 - b ^ 2) ^ 2 ≤ (1 - r ^ 2) ^ 2 :=
      (sq_le_sq₀ ha0.le har.le).2 (by linarith)
    calc
      V22.cr r ≤ r ^ 4 / (12 * (1 - r ^ 2) ^ 2) := shared_cr_quartic_bound hr.le hrh
      _ ≤ r ^ 4 / (12 * (1 - b ^ 2) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right (by
        nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg r)]) (by positivity)
  have hp : 8 / 9 ≤ 1 - b ^ 2 / (3 * (1 - b ^ 2)) := by
    have hx : b ^ 2 / (3 * (1 - b ^ 2)) ≤ (1 / 9 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - b ^ 2))).2
      nlinarith
    linarith
  have hsmall : 0 ≤ r * ((1 - b ^ 2 / (3 * (1 - b ^ 2))) * m - 4) := by
    exact mul_nonneg hr.le (by nlinarith)
  have hlinear : r * ((1 - b ^ 2 / (3 * (1 - b ^ 2))) * m - 4) ≤
      r * (m - 4) - m * V22.aHat r := by
    have h := mul_le_mul_of_nonneg_left hA2 hm0.le
    have he : r * ((1 - b ^ 2 / (3 * (1 - b ^ 2))) * m - 4) =
        r * (m - 4) - m * (r * b ^ 2 / (3 * (1 - b ^ 2))) := by ring
    rw [he]
    linarith
  have hsq : r ^ 2 * ((1 - b ^ 2 / (3 * (1 - b ^ 2))) * m - 4) ^ 2 ≤
      (r * (m - 4) - m * V22.aHat r) ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hsmall (hsmall.trans hlinear)).2 hlinear
  have hsqTerm := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2 * m)
  have hAt := mul_le_mul_of_nonneg_right hA
    (by positivity : 0 ≤ (m - 1) / (2 * r * (m - 2)))
  have hAe : (r ^ 3 / (3 * (1 - b ^ 2))) * ((m - 1) / (2 * r * (m - 2))) =
      r ^ 2 * (m - 1) / (6 * (1 - b ^ 2) * (m - 2)) := by
    field_simp [hr.ne', ha0.ne', hm2.ne'] <;> ring
  rw [hAe] at hAt
  have hCt := mul_le_mul_of_nonneg_left hcr hm0.le
  have hcomplete := fiber_phi_completed_square (N := m - 1) hr hrh (by linarith)
  simp only [sub_add_cancel] at hcomplete
  have he : fiberGainD m + r ^ 2 * fiberGainC b m =
      71 / (20 * m) + r ^ 2 * ((1 - b ^ 2 / (3 * (1 - b ^ 2))) * m - 4) ^ 2 /
        (2 * m) - (m - 1) / (m * (m - 2)) -
        r ^ 2 * (m - 1) / (6 * (1 - b ^ 2) * (m - 2)) -
        m * (b ^ 2 * r ^ 2 / (12 * (1 - b ^ 2) ^ 2)) := by
    unfold fiberGainD fiberGainC
    field_simp [hm0.ne', hm2.ne', ha0.ne'] <;> ring
  rw [he]
  have hAt' : V22.aHat r * (m - 1) / (2 * r * (m - 2)) ≤
      r ^ 2 * (m - 1) / (6 * (1 - b ^ 2) * (m - 2)) := by
    simpa only [mul_div_assoc] using hAt
  linarith

theorem fiber_uniform_phi_lower {r b N : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrb : r ≤ b) (hbh : b ≤ 1 / 2) :
    fiberGainD (N + 1) + r ^ 2 * fiberGainC b (N + 1) ≤ V22.phiR r N := by
  by_cases hr : r = 0
  · subst r
    have hn : 0 < N + 1 := by linarith
    have ht : 0 < N - 1 := by linarith
    have ht' : 0 < N + 1 - 2 := by linarith
    have he : V22.phiR 0 N = 71 / (20 * (N + 1)) := by
      simp [V22.phiR, V22.rhoU, V22.eU, V22.cr, V22.artanh,
        V22.epsilonPrime, V22.yTilde, V22.aHat, V22.c0Prime, V22.Delta]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero]
    unfold fiberGainD
    have hx : 0 ≤ 1 / (2 * (N + 1 - 2)) := by positivity
    have hy : 61 / (20 * (N + 1)) ≤ 71 / (20 * (N + 1)) := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    simpa only [add_sub_cancel_right] using
      fiber_uniform_phi_lower_pos (m := N + 1) hrp hrb hbh (by linarith)

theorem fiber_uniform_phi_strict {r b N : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrb : r ≤ b) (hbh : b ≤ 1 / 2) :
    439 / (180 * (N + 1)) + 769 * r ^ 2 / 891 ≤ V22.phiR r N ∧
      0 < V22.phiR r N := by
  have hD := fiber_gain_D_lower (m := N + 1) (by linarith)
  have hC := (fiber_gain_C_half_lower (m := N + 1) (by linarith)).trans
    (fiber_gain_C_lower (hr0.trans hrb) hbh (by linarith))
  have hCp := mul_le_mul_of_nonneg_left hC (sq_nonneg r)
  have hPhi := fiber_uniform_phi_lower hN hr0 hrb hbh
  have hmain : 439 / (180 * (N + 1)) + 769 * r ^ 2 / 891 ≤ V22.phiR r N := by
    nlinarith
  exact ⟨hmain, lt_of_lt_of_le (by positivity) hmain⟩

end Erdos993Lean.Analytic.V213
