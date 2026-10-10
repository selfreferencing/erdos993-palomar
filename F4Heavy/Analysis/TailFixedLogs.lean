module

public import F4Heavy.Analysis.TailDefinitions
public import F4Heavy.Analysis.LogSeriesRemainder

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_fixed_log_D :
    tailLogLo .D < Real.log (tailScale .D * (1 + tailMid .D)) ∧
      Real.log (tailScale .D * (1 + tailMid .D)) < tailLogHi .D := by
  have h2 := log_series_enclosure 16 (1 / 3 : ℝ) (by norm_num) (by norm_num)
  have ht := log_series_enclosure 16 (8 / 33 : ℝ) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h2 ht
  have hid := Real.log_mul (show (41 / 25 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ^ 2 ≠ 0 by norm_num)
  rw [Real.log_pow] at hid
  norm_num at hid
  norm_num [tailLogLo, tailLogHi, tailScale, tailMid, rowData]
  constructor <;> linarith only [h2.1, h2.2, ht.1, ht.2, hid]

theorem tail_fixed_log_E1 :
    tailLogLo .E1 < Real.log (tailScale .E1 * (1 + tailMid .E1)) ∧
      Real.log (tailScale .E1 * (1 + tailMid .E1)) < tailLogHi .E1 := by
  have h2 := log_series_enclosure 16 (1 / 3 : ℝ) (by norm_num) (by norm_num)
  have ht := log_series_enclosure 16 (3 / 35 : ℝ) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h2 ht
  have hid := Real.log_mul (show (19 / 16 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ^ 3 ≠ 0 by norm_num)
  rw [Real.log_pow] at hid
  norm_num at hid
  norm_num [tailLogLo, tailLogHi, tailScale, tailMid, rowData]
  constructor <;> linarith only [h2.1, h2.2, ht.1, ht.2, hid]

theorem tail_fixed_log_E2 :
    tailLogLo .E2 < Real.log (tailScale .E2 * (1 + tailMid .E2)) ∧
      Real.log (tailScale .E2 * (1 + tailMid .E2)) < tailLogHi .E2 := by
  have h2 := log_series_enclosure 16 (1 / 3 : ℝ) (by norm_num) (by norm_num)
  have ht := log_series_enclosure 16 (21 / 181 : ℝ) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h2 ht
  have hid := Real.log_mul (show (101 / 80 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ^ 3 ≠ 0 by norm_num)
  rw [Real.log_pow] at hid
  norm_num at hid
  norm_num [tailLogLo, tailLogHi, tailScale, tailMid, rowData]
  constructor <;> linarith only [h2.1, h2.2, ht.1, ht.2, hid]

theorem tail_fixed_log_H :
    tailLogLo .H < Real.log (tailScale .H * (1 + tailMid .H)) ∧
      Real.log (tailScale .H * (1 + tailMid .H)) < tailLogHi .H := by
  have h2 := log_series_enclosure 16 (1 / 3 : ℝ) (by norm_num) (by norm_num)
  have ht := log_series_enclosure 16 (25 / 121 : ℝ) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h2 ht
  have hid := Real.log_mul (show (73 / 48 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ^ 3 ≠ 0 by norm_num)
  rw [Real.log_pow] at hid
  norm_num at hid
  norm_num [tailLogLo, tailLogHi, tailScale, tailMid, rowData]
  constructor <;> linarith only [h2.1, h2.2, ht.1, ht.2, hid]

theorem tail_fixed_log_bracket (r : Row) :
    tailLogLo r < Real.log (tailScale r * (1 + tailMid r)) ∧
      Real.log (tailScale r * (1 + tailMid r)) < tailLogHi r := by
  cases r with
  | D => exact tail_fixed_log_D
  | E1 => exact tail_fixed_log_E1
  | E2 => exact tail_fixed_log_E2
  | H => exact tail_fixed_log_H

end F4Heavy.Analysis
