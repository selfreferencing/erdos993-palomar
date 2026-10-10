module

public import F4Heavy.Analysis.LogBounds

@[expose] public section
set_option autoImplicit false
open Finset

namespace F4Heavy.Analysis

noncomputable def halfLogRemainder (n : Nat) (y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)) -
    ∑ i ∈ Finset.range n, y ^ (2 * i + 1) / (2 * i + 1)

theorem logRemainder_majorant_derivative (n : Nat) (v y : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hy0 : 0 ≤ y) (hyv : y ≤ v) :
    HasDerivAt (fun z => z ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (1 - v ^ 2)) -
      halfLogRemainder n z)
      ((y ^ 2) ^ n / (1 - v ^ 2) - (y ^ 2) ^ n / (1 - y ^ 2)) y := by
  have hvd : 0 < 1 - v ^ 2 := by
    have h := mul_pos (sub_pos.mpr hv1) (show 0 < 1 + v by linarith)
    nlinarith only [h]
  have hnd : (2 * n + 1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hmain := ((hasDerivAt_id y).pow (2 * n + 1)).div_const
    ((2 * n + 1 : ℝ) * (1 - v ^ 2))
  have hrem := Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range n
    (show -1 < y by linarith) (show y < 1 by linarith)
  convert hmain.sub hrem using 1
  · rfl
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.add_sub_cancel,
      mul_one, pow_mul, id_eq]
    field_simp

theorem logRemainder_majorant_monotone (n : Nat) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    MonotoneOn (fun y => y ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (1 - v ^ 2)) -
      halfLogRemainder n y) (Set.Icc 0 v) := by
  have hvd : 0 < 1 - v ^ 2 := by
    have h := mul_pos (sub_pos.mpr hv1) (show 0 < 1 + v by linarith)
    nlinarith only [h]
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 v)
  · intro y hy
    exact (logRemainder_majorant_derivative n v y hv0 hv1 hy.1 hy.2).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Set.Icc 0 v := interior_subset hy
    exact (logRemainder_majorant_derivative n v y hv0 hv1 hy'.1 hy'.2).differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' : y ∈ Set.Icc 0 v := interior_subset hy
    rw [(logRemainder_majorant_derivative n v y hv0 hv1 hy'.1 hy'.2).deriv]
    apply sub_nonneg.mpr
    have hsq : y ^ 2 ≤ v ^ 2 := by
      have h := mul_self_le_mul_self hy'.1 hy'.2
      nlinarith only [h]
    exact div_le_div_of_nonneg_left (by positivity) hvd (by linarith)

theorem halfLogRemainder_zero (n : Nat) : halfLogRemainder n 0 = 0 := by
  simp [halfLogRemainder]

theorem log_series_tight_upper (n : Nat) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    Real.log ((1 + v) / (1 - v)) ≤
      2 * (∑ i ∈ Finset.range n, v ^ (2 * i + 1) / (2 * i + 1)) +
        2 * v ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (1 - v ^ 2)) := by
  have hm := logRemainder_majorant_monotone n v hv0 hv1
    (show (0 : ℝ) ∈ Set.Icc 0 v from ⟨le_refl 0, hv0⟩)
    (show v ∈ Set.Icc 0 v from ⟨hv0, le_refl v⟩) hv0
  dsimp only at hm
  rw [halfLogRemainder_zero] at hm
  have hz : (0 : ℝ) ^ (2 * n + 1) = 0 := by simp
  rw [hz, zero_div, sub_zero] at hm
  unfold halfLogRemainder at hm
  rw [mul_div_assoc]
  linarith only [hm]

theorem log_series_enclosure (n : Nat) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    2 * (∑ i ∈ Finset.range n, v ^ (2 * i + 1) / (2 * i + 1)) ≤
        Real.log ((1 + v) / (1 - v)) ∧
      Real.log ((1 + v) / (1 - v)) ≤
        2 * (∑ i ∈ Finset.range n, v ^ (2 * i + 1) / (2 * i + 1)) +
          2 * v ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * (1 - v ^ 2)) := by
  constructor
  · have h := Real.sum_range_le_log_div hv0 hv1 n
    linarith
  · exact log_series_tight_upper n v hv0 hv1

end F4Heavy.Analysis
