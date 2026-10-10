module

public import Erdos993Lean.Analytic.V213.FreeCountRealLogEnvelopes

/-! Four scalar logarithm comparisons printed in T7, proved using the already
accepted artanh enclosure. No finite record family is evaluated here. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows
open Real
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

theorem log_fourteen_fifths_gt : (36 / 35 : ℝ) < log (14 / 5) := by
  have h := artanh_brackets (w := 1 / 6) (by norm_num) (by norm_num)
  have h2 := log_two_brackets
  have he : log (14 / 5 : ℝ) = log 2 + log (7 / 5 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (7 / 5 : ℝ) ≠ 0)]
    norm_num
  norm_num [seriesS, seriesT] at h
  rw [he]
  linarith [h.1, h2.1]

theorem log_sixteen_fifths_gt : (9 / 8 : ℝ) < log (16 / 5) := by
  have h := artanh_brackets (w := 3 / 13) (by norm_num) (by norm_num)
  have h2 := log_two_brackets
  have he : log (16 / 5 : ℝ) = log 2 + log (8 / 5 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (8 / 5 : ℝ) ≠ 0)]
    norm_num
  norm_num [seriesS, seriesT] at h
  rw [he]
  linarith [h.1, h2.1]

theorem log_thirtythree_tenths_gt : (119 / 100 : ℝ) < log (33 / 10) := by
  have h := artanh_brackets (w := 13 / 53) (by norm_num) (by norm_num)
  have h2 := log_two_brackets
  have he : log (33 / 10 : ℝ) = log 2 + log (33 / 20 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (33 / 20 : ℝ) ≠ 0)]
    norm_num
  norm_num [seriesS, seriesT] at h
  rw [he]
  linarith [h.1, h2.1]

theorem log_fortysix_thirtythirds_lt : log (46 / 33 : ℝ) < 1 / 3 := by
  have h := artanh_brackets (w := 13 / 79) (by norm_num) (by norm_num)
  norm_num [seriesS, seriesT] at h
  linarith [h.2]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.log_fourteen_fifths_gt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.log_fourteen_fifths_gt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.log_sixteen_fifths_gt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.log_sixteen_fifths_gt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.log_thirtythree_tenths_gt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.log_thirtythree_tenths_gt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.log_fortysix_thirtythirds_lt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.log_fortysix_thirtythirds_lt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.artanh_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.artanh_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_two_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_two_brackets
