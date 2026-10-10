module

public import F4Heavy.Analysis.CapReserveLog
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def capDLogChord (lam : ℝ) : ℝ := 36 / 35 + 113 / 350 * (lam - 4 / 5)

theorem cap_log_fourteen_fifths_lower : (36 : ℝ) / 35 < Real.log (14 / 5) := by
  have h := Real.sum_range_le_log_div (show (0 : ℝ) ≤ 9 / 19 by norm_num)
    (show (9 : ℝ) / 19 < 1 by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem cap_log_thirtythree_tenths_upper : Real.log (33 / 10 : ℝ) < 6 / 5 := by
  have h := log_series_tight_upper 6 (23 / 43 : ℝ) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem cap_D_log_chord_pos (lam : ℝ) (hr : InRow .D lam) : 0 < capDLogChord lam := by
  have hlo : 4 / 5 ≤ lam := hr.1
  unfold capDLogChord
  linarith only [hlo]

theorem cap_D_log_chord_lower (lam : ℝ) (hr : InRow .D lam) :
    capDLogChord lam ≤ Real.log (lam + 2) := by
  have hlo : 4 / 5 ≤ lam := hr.1
  have hhi : lam ≤ 13 / 10 := hr.2
  let a : ℝ := 2 * (13 / 10 - lam)
  let b : ℝ := 2 * (lam - 4 / 5)
  have ha : 0 ≤ a := by dsimp [a]; linarith only [hhi]
  have hb : 0 ≤ b := by dsimp [b]; linarith only [hlo]
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (14 / 5 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (33 / 10 : ℝ) ∈ Set.Ioi 0 by norm_num) ha hb hab
  simp only [smul_eq_mul] at h
  have hx : a * (14 / 5) + b * (33 / 10) = lam + 2 := by dsimp [a, b]; ring
  rw [hx] at h
  have hA := mul_le_mul_of_nonneg_left cap_log_fourteen_fifths_lower.le ha
  have hB := mul_le_mul_of_nonneg_left cap_log_thirtythree_tenths_lower.le hb
  have hid : capDLogChord lam = a * (36 / 35) + b * (119 / 100) := by
    dsimp [capDLogChord, a, b]
    ring
  rw [hid]
  exact (add_le_add hA hB).trans h

theorem cap_D_log_upper (lam : ℝ) (hr : InRow .D lam) : Real.log (lam + 2) < 6 / 5 := by
  have hlo : 4 / 5 ≤ lam := hr.1
  have hhi : lam ≤ 13 / 10 := hr.2
  exact (Real.log_le_log (by linarith only [hlo] : 0 < lam + 2)
    (by linarith only [hhi] : lam + 2 ≤ 33 / 10)).trans_lt cap_log_thirtythree_tenths_upper

end F4Heavy.Analysis
