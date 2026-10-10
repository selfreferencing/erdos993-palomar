module

public import Erdos993Lean.Analytic.V213.FiberMassEnvelope
public import Erdos993Lean.Analytic.V213.FiberMassConstants

/-!
Eq74: actual mass-error windows on the complete printed real width
ranges. The finite F01 constants are used only through their reviewed,
identity-bound Int/Nat soundness theorems; the width and skew domains are
proved here and do not remain numerical assumptions.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_width_power_upper {A c N N₀ B : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hN₀ : 2 ≤ N₀) (hN : N₀ ≤ N)
    (hB : A * Real.sqrt N₀ + c ≤ B) :
    fiberWidthPower A c N ≤ B ^ 4 / (N₀ + 1) ^ 3 := by
  calc
    _ ≤ fiberWidthPower A c N₀ :=
      fiber_width_power_antitone hA hc hN₀ (hN₀.trans hN) hN
    _ ≤ _ := by
      unfold fiberWidthPower
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hB 4) (by positivity)

theorem fiber_mass_constants_w15_n22 :
    max ((27 / 4 : ℝ) ^ 4 / (9 * (91 / 100) * 23 ^ 3)) (23 / 1008) < 1 / 40 := by
  convert fiber_mass_constants_w15_n22_reduced using 1 <;> norm_num

theorem fiber_mass_error_w15_n22 {N r : ℝ}
    (hN : 22 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    fiberMassError N r (3 / 2) ≤
      max ((27 / 4 : ℝ) ^ 4 / (9 * (91 / 100) * 23 ^ 3)) (23 / 1008) ∧
    fiberMassError N r (3 / 2) < 1 / 40 := by
  have hN0 : 0 < N := by linarith
  have hA0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hp0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) * Real.sqrt 22 := by positivity
  have hpsq : (Real.sqrt (3 / 2 : ℝ) * Real.sqrt 22) ^ 2 = 33 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 22)]
    norm_num
  have hp : Real.sqrt (3 / 2 : ℝ) * Real.sqrt 22 ≤ 23 / 4 := by nlinarith
  have he := fiber_window_envelopes hN0 hr0 hrh (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hR : fiberWidthRatio (Real.sqrt (3 / 2)) 0 N ≤ 1 / 4 := by
    calc
      _ ≤ fiberWidthRatio (Real.sqrt (3 / 2)) 0 22 :=
        fiber_width_ratio_antitone hA0 (by norm_num) (by norm_num) hN
      _ ≤ _ := by
        unfold fiberWidthRatio
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 22 + 1)).2
        linarith
  have hL : fiberWindowLeft N r (3 / 2) ≤ 3 / 10 := by
    calc
      _ ≤ fiberWidthRatio (Real.sqrt (3 / 2)) 1 N := he.2.2.2
      _ ≤ fiberWidthRatio (Real.sqrt (3 / 2)) 1 22 :=
        fiber_width_ratio_antitone hA0 (by norm_num) (by norm_num) hN
      _ ≤ _ := by
        unfold fiberWidthRatio
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 22 + 1)).2
        linarith
  have hU : r + fiberWindowRight N r (3 / 2) ≤ 3 / 4 := by linarith [he.2.1]
  have hc := fiber_mass_error_coarse hN0 hr0 hrh (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (by norm_num : (0 : ℝ) ≤ 3 / 10) (by norm_num) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num) hL hU
  have hPL := fiber_width_power_upper hA0 (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (2 : ℝ) ≤ 22) hN (by linarith : Real.sqrt (3 / 2) * Real.sqrt 22 + 1 ≤ 27 / 4)
  have hPR := fiber_width_power_upper hA0 (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (2 : ℝ) ≤ 22) hN (by linarith : Real.sqrt (3 / 2) * Real.sqrt 22 + 0 ≤ 23 / 4)
  have hb : fiberMassError N r (3 / 2) ≤
      max ((27 / 4 : ℝ) ^ 4 / (9 * (91 / 100) * 23 ^ 3)) (23 / 1008) := by
    have hh := hc.trans (max_le_max
      (div_le_div_of_nonneg_right hPL (by norm_num : (0 : ℝ) ≤ 9 * (1 - (3 / 10) ^ 2)))
      (div_le_div_of_nonneg_right hPR (by norm_num : (0 : ℝ) ≤ 9 * (1 - (3 / 4) ^ 2))))
    convert hh using 1 <;> norm_num
  exact ⟨hb, hb.trans_lt fiber_mass_constants_w15_n22⟩

theorem fiber_mass_error_w15_n32 {N r : ℝ}
    (hN : 32 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    fiberMassError N r (3 / 2) ≤
      max (4096 / (297 * 1025) : ℝ) (9604 / (297 * 2147)) ∧
    fiberMassError N r (3 / 2) < 1 / 60 := by
  have hN0 : 0 < N := by linarith
  have hA0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hp0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) * Real.sqrt 32 := by positivity
  have hpsq : (Real.sqrt (3 / 2 : ℝ) * Real.sqrt 32) ^ 2 = 48 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32)]
    norm_num
  have hp : Real.sqrt (3 / 2 : ℝ) * Real.sqrt 32 ≤ 7 := by nlinarith
  have he := fiber_window_envelopes hN0 hr0 hrh (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hR : fiberWidthRatio (Real.sqrt (3 / 2)) 0 N ≤ 7 / 33 := by
    calc
      _ ≤ fiberWidthRatio (Real.sqrt (3 / 2)) 0 32 :=
        fiber_width_ratio_antitone hA0 (by norm_num) (by norm_num) hN
      _ ≤ _ := by
        unfold fiberWidthRatio
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 32 + 1)).2
        linarith
  have hL : fiberWindowLeft N r (3 / 2) ≤ 8 / 33 := by
    calc
      _ ≤ fiberWidthRatio (Real.sqrt (3 / 2)) 1 N := he.2.2.2
      _ ≤ fiberWidthRatio (Real.sqrt (3 / 2)) 1 32 :=
        fiber_width_ratio_antitone hA0 (by norm_num) (by norm_num) hN
      _ ≤ _ := by
        unfold fiberWidthRatio
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 32 + 1)).2
        linarith
  have hU : r + fiberWindowRight N r (3 / 2) ≤ 47 / 66 := by linarith [he.2.1]
  have hc := fiber_mass_error_coarse hN0 hr0 hrh (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (by norm_num : (0 : ℝ) ≤ 8 / 33) (by norm_num) (by norm_num : (0 : ℝ) ≤ 47 / 66)
    (by norm_num) hL hU
  have hPL := fiber_width_power_upper hA0 (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (2 : ℝ) ≤ 32) hN (by linarith : Real.sqrt (3 / 2) * Real.sqrt 32 + 1 ≤ 8)
  have hPR := fiber_width_power_upper hA0 (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (2 : ℝ) ≤ 32) hN (by linarith : Real.sqrt (3 / 2) * Real.sqrt 32 + 0 ≤ 7)
  have hb : fiberMassError N r (3 / 2) ≤
      max (4096 / (297 * 1025) : ℝ) (9604 / (297 * 2147)) := by
    have hh := hc.trans (max_le_max
      (div_le_div_of_nonneg_right hPL (by norm_num : (0 : ℝ) ≤ 9 * (1 - (8 / 33) ^ 2)))
      (div_le_div_of_nonneg_right hPR (by norm_num : (0 : ℝ) ≤ 9 * (1 - (47 / 66) ^ 2))))
    convert hh using 1 <;> norm_num
  exact ⟨hb, hb.trans_lt fiber_mass_constants_w15_n32⟩


theorem fiber_mass_error_w1_n14 {N r : ℝ}
    (hN : 14 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    fiberMassError N r 1 ≤
      (1 / N) * max (4802 / 14641 : ℝ) (25 / 81) ∧
    fiberMassError N r 1 < 1 / (3 * N) := by
  have hN0 : 0 < N := by linarith
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have hs : (11 / 3 : ℝ) < Real.sqrt N := by nlinarith
  have hm : 0 < N + 1 := by linarith
  have hrec : 1 / Real.sqrt N < 3 / 11 := by
    have hh := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 11 / 3) hs
    norm_num at hh
    simpa only [one_div] using hh
  have he := fiber_window_envelopes hN0 hr0 hrh (by norm_num : (0 : ℝ) ≤ 1)
  have hR : fiberWidthRatio (Real.sqrt 1) 0 N ≤ 1 / Real.sqrt N := by
    unfold fiberWidthRatio
    simp only [Real.sqrt_one, one_mul, add_zero]
    apply (div_le_div_iff₀ hm hs0).2
    nlinarith
  have hL : fiberWindowLeft N r 1 ≤ 1 / 3 := by
    calc
      _ ≤ fiberWidthRatio (Real.sqrt 1) 1 N := he.2.2.2
      _ ≤ _ := by
        unfold fiberWidthRatio
        simp only [Real.sqrt_one, one_mul]
        apply (div_le_div_iff₀ hm (by norm_num : (0 : ℝ) < 3)).2
        have hh := mul_nonneg (le_of_lt (sub_pos.mpr hs))
          (by linarith : 0 ≤ Real.sqrt N + 2 / 3)
        nlinarith
  have hU : r + fiberWindowRight N r 1 ≤ 4 / 5 := by
    have hh := he.2.1.trans hR
    linarith
  have hc := fiber_mass_error_coarse hN0 hr0 hrh (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num) (by norm_num : (0 : ℝ) ≤ 4 / 5)
    (by norm_num) hL hU
  have hPL : N * fiberWidthPower (Real.sqrt 1) 1 N ≤ (14 / 11 : ℝ) ^ 4 := by
    have hn3 : 0 < N ^ 3 := by positivity
    have hden : N ^ 3 ≤ (N + 1) ^ 3 := pow_le_pow_left₀ hN0.le (by linarith) 3
    calc
      _ = N * (Real.sqrt N + 1) ^ 4 / (N + 1) ^ 3 := by
        unfold fiberWidthPower
        simp only [Real.sqrt_one, one_mul]
        ring
      _ ≤ N * (Real.sqrt N + 1) ^ 4 / N ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) hn3 hden
      _ = (1 + 1 / Real.sqrt N) ^ 4 := by
        generalize heq : Real.sqrt N = s at *
        field_simp [hs0.ne', hN0.ne']
        rw [← hsq]
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hPR : N * fiberWidthPower (Real.sqrt 1) 0 N ≤ 1 := by
    unfold fiberWidthPower
    simp only [Real.sqrt_one, one_mul, add_zero]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (N + 1) ^ 3)).2
    have hpow : Real.sqrt N ^ 4 = N ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hsq]
    rw [hpow]
    have hh := pow_le_pow_left₀ hN0.le (by linarith : N ≤ N + 1) 3
    nlinarith
  have hb : N * fiberMassError N r 1 ≤ max (4802 / 14641 : ℝ) (25 / 81) := by
    calc
      _ ≤ N * max
          (fiberWidthPower (Real.sqrt 1) 1 N / (9 * (1 - (1 / 3 : ℝ) ^ 2)))
          (fiberWidthPower (Real.sqrt 1) 0 N / (9 * (1 - (4 / 5 : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hc hN0.le
      _ = max ((N * fiberWidthPower (Real.sqrt 1) 1 N) / 8)
          ((N * fiberWidthPower (Real.sqrt 1) 0 N) * (25 / 81)) := by
        rw [mul_max_of_nonneg _ _ hN0.le]
        congr 1 <;> ring
      _ ≤ _ := by
        have hl := div_le_div_of_nonneg_right hPL (by norm_num : (0 : ℝ) ≤ 8)
        have hr := mul_le_mul_of_nonneg_right hPR (by norm_num : (0 : ℝ) ≤ 25 / 81)
        norm_num at hl
        simp only [one_mul] at hr
        simpa only [Real.sqrt_one] using max_le_max hl hr
  have hb' : fiberMassError N r 1 ≤ max (4802 / 14641 : ℝ) (25 / 81) / N :=
    (le_div_iff₀ hN0).2 (by simpa [mul_comm] using hb)
  refine ⟨?_, ?_⟩
  · simpa [div_eq_mul_inv, mul_comm] using hb'
  · have hh := hb'.trans_lt ((div_lt_div_iff_of_pos_right hN0).2 fiber_mass_constants_w1)
    convert hh using 1 <;> ring

end Erdos993Lean.Analytic.V213
