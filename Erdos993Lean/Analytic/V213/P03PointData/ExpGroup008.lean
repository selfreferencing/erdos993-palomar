module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization002
public import Erdos993Lean.ExactComparisons.F3All.Strict019
public import Erdos993Lean.ExactComparisons.F3All.Strict020
public import Erdos993Lean.ExactComparisons.F3All.Strict021
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e112_bounds : ExpEnclosure e112 := by
  apply exp_enclosure_of_checks e112
  · have h : (1 : Rat) ≤ e112.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 47 (by change 47 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at Strict019.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict019.checked 7 (by change 7 < 16; omega)

theorem e113_bounds : ExpEnclosure e113 := by
  apply exp_enclosure_of_checks e113
  · have h : (1 : Rat) ≤ e113.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 48 (by change 48 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict019.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict019.checked 9 (by change 9 < 16; omega)

theorem e114_bounds : ExpEnclosure e114 := by
  apply exp_enclosure_of_checks e114
  · have h : (1 : Rat) ≤ e114.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 49 (by change 49 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 43 (by change 43 < 64; omega)
  · exact comparison_record_at Strict019.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict019.checked 11 (by change 11 < 16; omega)

theorem e115_bounds : ExpEnclosure e115 := by
  apply exp_enclosure_of_checks e115
  · have h : (1 : Rat) ≤ e115.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 50 (by change 50 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict019.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict019.checked 13 (by change 13 < 16; omega)

theorem e116_bounds : ExpEnclosure e116 := by
  apply exp_enclosure_of_checks e116
  · have h : (1 : Rat) ≤ e116.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 51 (by change 51 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at Strict019.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict019.checked 15 (by change 15 < 16; omega)

theorem e117_bounds : ExpEnclosure e117 := by
  apply exp_enclosure_of_checks e117
  · have h : (1 : Rat) ≤ e117.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 52 (by change 52 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict020.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict020.checked 1 (by change 1 < 16; omega)

theorem e118_bounds : ExpEnclosure e118 := by
  apply exp_enclosure_of_checks e118
  · have h : (1 : Rat) ≤ e118.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 53 (by change 53 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 47 (by change 47 < 64; omega)
  · exact comparison_record_at Strict020.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict020.checked 3 (by change 3 < 16; omega)

theorem e119_bounds : ExpEnclosure e119 := by
  apply exp_enclosure_of_checks e119
  · have h : (1 : Rat) ≤ e119.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 54 (by change 54 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict020.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict020.checked 5 (by change 5 < 16; omega)

theorem e120_bounds : ExpEnclosure e120 := by
  apply exp_enclosure_of_checks e120
  · have h : (1 : Rat) ≤ e120.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 55 (by change 55 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at Strict020.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict020.checked 7 (by change 7 < 16; omega)

theorem e121_bounds : ExpEnclosure e121 := by
  apply exp_enclosure_of_checks e121
  · have h : (1 : Rat) ≤ e121.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 56 (by change 56 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict020.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict020.checked 9 (by change 9 < 16; omega)

theorem e122_bounds : ExpEnclosure e122 := by
  apply exp_enclosure_of_checks e122
  · have h : (1 : Rat) ≤ e122.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 57 (by change 57 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 51 (by change 51 < 64; omega)
  · exact comparison_record_at Strict020.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict020.checked 11 (by change 11 < 16; omega)

theorem e123_bounds : ExpEnclosure e123 := by
  apply exp_enclosure_of_checks e123
  · have h : (1 : Rat) ≤ e123.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 58 (by change 58 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict020.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict020.checked 13 (by change 13 < 16; omega)

theorem e124_bounds : ExpEnclosure e124 := by
  apply exp_enclosure_of_checks e124
  · have h : (1 : Rat) ≤ e124.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 59 (by change 59 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at Strict020.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict020.checked 15 (by change 15 < 16; omega)

theorem e125_bounds : ExpEnclosure e125 := by
  apply exp_enclosure_of_checks e125
  · have h : (1 : Rat) ≤ e125.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 60 (by change 60 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict021.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict021.checked 1 (by change 1 < 16; omega)

theorem e126_bounds : ExpEnclosure e126 := by
  apply exp_enclosure_of_checks e126
  · have h : (1 : Rat) ≤ e126.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 61 (by change 61 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 55 (by change 55 < 64; omega)
  · exact comparison_record_at Strict021.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict021.checked 3 (by change 3 < 16; omega)

theorem e127_bounds : ExpEnclosure e127 := by
  apply exp_enclosure_of_checks e127
  · have h : (1 : Rat) ≤ e127.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 62 (by change 62 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict021.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict021.checked 5 (by change 5 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e113_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e113_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e114_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e114_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e115_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e115_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e117_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e117_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e118_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e118_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e119_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e119_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e121_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e121_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e122_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e122_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e123_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e123_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e125_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e125_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e127_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e127_bounds
