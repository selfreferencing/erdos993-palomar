module

public import F4Heavy.Finite.Metadata
public import F4Heavy.Analysis.FixedLogBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

-- Derived from metadata_0035_D_log_lower_left and fixed_log_bound_013.
theorem activity_log_D_left : 0 < (293893332451 / 500000000000 : ℝ) ∧
    (293893332451 / 500000000000 : ℝ) < Real.log (9 / 5 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0035_D_log_lower_left
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_013.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0036_D_log_lower_right and fixed_log_bound_014.
theorem activity_log_D_right : 0 < (166581824587 / 200000000000 : ℝ) ∧
    (166581824587 / 200000000000 : ℝ) < Real.log (23 / 10 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0036_D_log_lower_right
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_014.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0037_D_log_upper_midpoint and fixed_log_bound_015.
theorem activity_log_D_midpoint : Real.log (41 / 20 : ℝ) < (717839793151 / 1000000000000 : ℝ) := by
  have h := lt_of_le_of_lt fixed_log_bound_015.2
    (fraction_lt_sound _ _ metadata_0037_D_log_upper_midpoint)
  norm_num [fractionValue] at h
  exact h

-- Derived from metadata_0034_D_activity_ratio_logarithm_lower and fixed_log_bound_012.
theorem activity_log_D_ratio : 0 < (485507815781 / 1000000000000 : ℝ) ∧
    (485507815781 / 1000000000000 : ℝ) < Real.log (13 / 8 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0034_D_activity_ratio_logarithm_lower
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_012.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0086_E1_log_lower_left and fixed_log_bound_014.
theorem activity_log_E1_left : 0 < (8329091229 / 10000000000 : ℝ) ∧
    (8329091229 / 10000000000 : ℝ) < Real.log (23 / 10 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0086_E1_log_lower_left
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_014.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0087_E1_log_lower_right and fixed_log_bound_021.
theorem activity_log_E1_right : 0 < (1792176049 / 2000000000 : ℝ) ∧
    (1792176049 / 2000000000 : ℝ) < Real.log (49 / 20 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0087_E1_log_lower_right
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_021.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0088_E1_log_upper_midpoint and fixed_log_bound_026.
theorem activity_log_E1_midpoint : Real.log (19 / 8 : ℝ) < (13839959 / 16000000 : ℝ) := by
  have h := lt_of_le_of_lt fixed_log_bound_026.2
    (fraction_lt_sound _ _ metadata_0088_E1_log_upper_midpoint)
  norm_num [fractionValue] at h
  exact h

-- Derived from metadata_0124_E2_log_lower_left and fixed_log_bound_021.
theorem activity_log_E2_left : 0 < (1792176049 / 2000000000 : ℝ) ∧
    (1792176049 / 2000000000 : ℝ) < Real.log (49 / 20 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0124_E2_log_lower_left
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_021.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0125_E2_log_lower_right and fixed_log_bound_027.
theorem activity_log_E2_right : 0 < (191102289 / 200000000 : ℝ) ∧
    (191102289 / 200000000 : ℝ) < Real.log (13 / 5 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0125_E2_log_lower_right
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_027.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0126_E2_log_upper_midpoint and fixed_log_bound_032.
theorem activity_log_E2_midpoint : Real.log (101 / 40 : ℝ) < (2315602657 / 2500000000 : ℝ) := by
  have h := lt_of_le_of_lt fixed_log_bound_032.2
    (fraction_lt_sound _ _ metadata_0126_E2_log_upper_midpoint)
  norm_num [fractionValue] at h
  exact h

-- Derived from metadata_0184_H_log_lower_left and fixed_log_bound_055.
theorem activity_log_H_left : 0 < (505800455839 / 500000000000 : ℝ) ∧
    (505800455839 / 500000000000 : ℝ) < Real.log (11 / 4 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0184_H_log_lower_left
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_055.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0185_H_log_lower_right and fixed_log_bound_056.
theorem activity_log_H_right : 0 < (48158912173 / 40000000000 : ℝ) ∧
    (48158912173 / 40000000000 : ℝ) < Real.log (10 / 3 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0185_H_log_lower_right
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_056.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

-- Derived from metadata_0186_H_log_upper_midpoint and fixed_log_bound_057.
theorem activity_log_H_midpoint : Real.log (73 / 24 : ℝ) < (1112405610801 / 1000000000000 : ℝ) := by
  have h := lt_of_le_of_lt fixed_log_bound_057.2
    (fraction_lt_sound _ _ metadata_0186_H_log_upper_midpoint)
  norm_num [fractionValue] at h
  exact h

-- Derived from metadata_0183_H_activity_ratio_logarithm_lower and fixed_log_bound_054.
theorem activity_log_H_ratio : 0 < (287682072451 / 1000000000000 : ℝ) ∧
    (287682072451 / 1000000000000 : ℝ) < Real.log (4 / 3 : ℝ) := by
  have hc := Bool.and_eq_true_iff.mp metadata_0183_H_activity_ratio_logarithm_lower
  have hp := fraction_lt_sound _ _ hc.1
  have h := lt_of_lt_of_le (fraction_lt_sound _ _ hc.2) fixed_log_bound_054.1
  norm_num [fractionValue] at h
  exact ⟨by simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hp, h⟩

end F4Heavy.Analysis
