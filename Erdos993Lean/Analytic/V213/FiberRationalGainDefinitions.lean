module

public import Erdos993Lean.Analytic.V213.FiberUniformGain

/-!
The literal rational gain in Eq100 of version 2.13 of the manuscript. The bounds below concern
the actual formulas on their entire real domains; no finite family is consumed.
The current paper ZIP remains the authority, including both positive powers
that are retained in Lemma 6.22.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

noncomputable def fiberRationalA (b : ℝ) : ℝ :=
  1 / 2 - b ^ 2 / (3 * (1 - b ^ 2)) - b ^ 2 / (12 * (1 - b ^ 2) ^ 2)

noncomputable def fiberRationalGain (a b N : ℝ) : ℝ :=
  let m := N + 1
  a ^ 2 * (m * fiberRationalA b - 4 + 8 / m) + 71 / (20 * m) -
    (m - 1) / (m * (m - 2)) - b ^ 2 * (m - 1) / (6 * (1 - b ^ 2) * (m - 2)) +
      4 * a ^ 4 / 3 + m * a ^ 6 / 18

noncomputable def fiberRationalGainPrime (a b N : ℝ) : ℝ :=
  let m := N + 1
  a ^ 2 * (fiberRationalA b - 8 / m ^ 2) - 71 / (20 * m ^ 2) +
    1 / (2 * m ^ 2) + 1 / (2 * (m - 2) ^ 2) +
      b ^ 2 / (6 * (1 - b ^ 2) * (m - 2) ^ 2) + a ^ 6 / 18

theorem fiber_rational_A_lower {b : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2) :
    19 / 54 ≤ fiberRationalA b := by
  have ho : 3 / 4 ≤ 1 - b ^ 2 := by nlinarith
  have ho0 : 0 < 1 - b ^ 2 := by linarith
  have h1 : b ^ 2 / (3 * (1 - b ^ 2)) ≤ (1 / 9 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - b ^ 2))).2
    nlinarith
  have hs : (3 / 4 : ℝ) ^ 2 ≤ (1 - b ^ 2) ^ 2 :=
    (sq_le_sq₀ (by norm_num) ho0.le).2 ho
  have h2 : b ^ 2 / (12 * (1 - b ^ 2) ^ 2) ≤ (1 / 27 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - b ^ 2) ^ 2)).2
    nlinarith
  unfold fiberRationalA
  linarith

theorem fiber_rational_main_increasing {b m m0 : ℝ}
    (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2) (hm0 : 11 ≤ m0) (hm : m0 ≤ m) :
    m0 * fiberRationalA b - 4 + 8 / m0 ≤ m * fiberRationalA b - 4 + 8 / m := by
  have h0 : 0 < m0 := by linarith
  have h : 0 < m := by linarith
  have hprod : 121 ≤ m0 * m := by nlinarith
  have hfrac : 8 / (m0 * m) ≤ (8 / 121 : ℝ) := by
    apply (div_le_iff₀ (mul_pos h0 h)).2
    linarith
  have hA := fiber_rational_A_lower hb0 hbh
  have hcoef : 0 ≤ fiberRationalA b - 8 / (m0 * m) := by linarith
  have he : (m * fiberRationalA b - 4 + 8 / m) -
      (m0 * fiberRationalA b - 4 + 8 / m0) =
        (m - m0) * (fiberRationalA b - 8 / (m0 * m)) := by
    field_simp [h0.ne', h.ne'] <;> ring
  have hp := mul_nonneg (sub_nonneg.mpr hm) hcoef
  rw [← he] at hp
  linarith

theorem fiber_rational_main_positive {b m : ℝ}
    (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2) (hm : 11 ≤ m) :
    0 < m * fiberRationalA b - 4 + 8 / m := by
  have hA := fiber_rational_A_lower hb0 hbh
  have hf := fiber_rational_main_increasing hb0 hbh (le_refl (11 : ℝ)) hm
  norm_num at hf
  linarith

theorem fiber_rational_main_fifteen {b m : ℝ}
    (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2) (hm : 15 ≤ m) :
    163 / 90 ≤ m * fiberRationalA b - 4 + 8 / m := by
  have hA := fiber_rational_A_lower hb0 hbh
  have hf := fiber_rational_main_increasing hb0 hbh (by norm_num : (11 : ℝ) ≤ 15) hm
  norm_num at hf
  linarith

/-- The exact all-real-width lower value used in Eq101, before its strict floor. -/
theorem fiber_rational_gain_value {a b N : ℝ} (ha : 23 / 100 ≤ a)
    (hab : a ≤ b) (hbh : b ≤ 1 / 2) (hN : 14 ≤ N) :
    140317 / 3900000 ≤ fiberRationalGain a b N := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := ha0.trans hab
  have hm : 15 ≤ N + 1 := by linarith
  have hm0 : 0 < N + 1 := by linarith
  have hm2 : 0 < N + 1 - 2 := by linarith
  have ho : 3 / 4 ≤ 1 - b ^ 2 := by nlinarith
  have ho0 : 0 < 1 - b ^ 2 := by linarith
  have hf := fiber_rational_main_fifteen hb0 hbh hm
  have ha2 : (23 / 100 : ℝ) ^ 2 ≤ a ^ 2 :=
    (sq_le_sq₀ (by norm_num) ha0).2 ha
  have hmain := mul_le_mul ha2 hf (by norm_num : (0 : ℝ) ≤ 163 / 90) (sq_nonneg a)
  have hratio : (N + 1 - 1) / (N + 1 - 2) ≤ (14 / 13 : ℝ) := by
    apply (div_le_iff₀ hm2).2
    linarith
  have hcombine : 0 ≤ 71 / (20 * (N + 1)) -
      (N + 1 - 1) / ((N + 1) * (N + 1 - 2)) := by
    have hmul := div_le_div_of_nonneg_right hratio hm0.le
    have he : ((N + 1 - 1) / (N + 1 - 2)) / (N + 1) =
        (N + 1 - 1) / ((N + 1) * (N + 1 - 2)) := by
      field_simp [hm0.ne',hm2.ne'] <;> ring
    rw [he] at hmul
    have hh : (14 / 13 : ℝ) / (N + 1) ≤ (71 / 20 : ℝ) / (N + 1) :=
      div_le_div_of_nonneg_right (by norm_num) hm0.le
    have he2 : (71 / 20 : ℝ) / (N + 1) = 71 / (20 * (N + 1)) := by
      field_simp [hm0.ne'] <;> ring
    rw [he2] at hh
    exact sub_nonneg.mpr (hmul.trans hh)
  have hbfrac : b ^ 2 / (6 * (1 - b ^ 2)) ≤ (1 / 18 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 6 * (1 - b ^ 2))).2
    nlinarith
  have hratio0 : 0 ≤ (N + 1 - 1) / (N + 1 - 2) :=
    div_nonneg (by linarith) hm2.le
  have hneg := mul_le_mul hbfrac hratio hratio0
    (by norm_num : (0 : ℝ) ≤ 1 / 18)
  have he3 : (b ^ 2 / (6 * (1 - b ^ 2))) * ((N + 1 - 1) / (N + 1 - 2)) =
      b ^ 2 * (N + 1 - 1) / (6 * (1 - b ^ 2) * (N + 1 - 2)) := by
    field_simp [ho0.ne',hm2.ne'] <;> ring
  rw [he3] at hneg
  have h4 : 0 ≤ 4 * a ^ 4 / 3 := by positivity
  have h6 : 0 ≤ (N + 1) * a ^ 6 / 18 := by positivity
  unfold fiberRationalGain
  dsimp only
  linarith

theorem fiber_rational_gain_strict {a b N : ℝ} (ha : 23 / 100 ≤ a)
    (hab : a ≤ b) (hbh : b ≤ 1 / 2) (hN : 14 ≤ N) :
    1 / 30 < fiberRationalGain a b N := by
  have h := fiber_rational_gain_value ha hab hbh hN
  linarith

/-- The standalone printed Eq79 middle expression, without substituting Phi. -/
theorem fiber_middle_gain_lower {r b m : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hm : 11 ≤ m) :
    439 / (180 * m) + 769 * r ^ 2 / 891 ≤ fiberGainD m + r ^ 2 * fiberGainC b m := by
  have hD := fiber_gain_D_lower hm
  have hC := (fiber_gain_C_half_lower hm).trans (fiber_gain_C_lower hb0 hbh hm)
  have hmul := mul_le_mul_of_nonneg_left hC (sq_nonneg r)
  nlinarith only [hD, hmul]

end Erdos993Lean.Analytic.V213
