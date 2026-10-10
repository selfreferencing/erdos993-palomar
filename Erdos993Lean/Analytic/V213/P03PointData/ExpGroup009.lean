module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization002
public import Erdos993Lean.ExactComparisons.F3All.Normalization003
public import Erdos993Lean.ExactComparisons.F3All.Strict021
public import Erdos993Lean.ExactComparisons.F3All.Strict022
public import Erdos993Lean.ExactComparisons.F3All.Validity025
public import Erdos993Lean.ExactComparisons.F3All.Validity026

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e128_bounds : ExpEnclosure e128 := by
  apply exp_enclosure_of_checks e128
  · have h : (1 : Rat) ≤ e128.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 63 (by change 63 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at Strict021.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict021.checked 7 (by change 7 < 16; omega)

theorem e129_bounds : ExpEnclosure e129 := by
  apply exp_enclosure_of_checks e129
  · have h : (1 : Rat) ≤ e129.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 0 (by change 0 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict021.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict021.checked 9 (by change 9 < 16; omega)

theorem e130_bounds : ExpEnclosure e130 := by
  apply exp_enclosure_of_checks e130
  · have h : (1 : Rat) ≤ e130.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 1 (by change 1 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 59 (by change 59 < 64; omega)
  · exact comparison_record_at Strict021.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict021.checked 11 (by change 11 < 16; omega)

theorem e131_bounds : ExpEnclosure e131 := by
  apply exp_enclosure_of_checks e131
  · have h : (1 : Rat) ≤ e131.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 2 (by change 2 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict021.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict021.checked 13 (by change 13 < 16; omega)

theorem e132_bounds : ExpEnclosure e132 := by
  apply exp_enclosure_of_checks e132
  · have h : (1 : Rat) ≤ e132.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 3 (by change 3 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at Strict021.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict021.checked 15 (by change 15 < 16; omega)

theorem e133_bounds : ExpEnclosure e133 := by
  apply exp_enclosure_of_checks e133
  · have h : (1 : Rat) ≤ e133.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 4 (by change 4 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict022.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict022.checked 1 (by change 1 < 16; omega)

theorem e134_bounds : ExpEnclosure e134 := by
  apply exp_enclosure_of_checks e134
  · have h : (1 : Rat) ≤ e134.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 5 (by change 5 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 63 (by change 63 < 64; omega)
  · exact comparison_record_at Strict022.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict022.checked 3 (by change 3 < 16; omega)

theorem e135_bounds : ExpEnclosure e135 := by
  apply exp_enclosure_of_checks e135
  · have h : (1 : Rat) ≤ e135.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 6 (by change 6 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity026.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict022.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict022.checked 5 (by change 5 < 16; omega)

theorem e136_bounds : ExpEnclosure e136 := by
  apply exp_enclosure_of_checks e136
  · have h : (1 : Rat) ≤ e136.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 7 (by change 7 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity026.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at Strict022.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict022.checked 7 (by change 7 < 16; omega)

theorem e137_bounds : ExpEnclosure e137 := by
  apply exp_enclosure_of_checks e137
  · have h : (1 : Rat) ≤ e137.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 8 (by change 8 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity026.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict022.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict022.checked 9 (by change 9 < 16; omega)

theorem e138_bounds : ExpEnclosure e138 := by
  apply exp_enclosure_of_checks e138
  · have h : (1 : Rat) ≤ e138.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 9 (by change 9 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity026.checked 3 (by change 3 < 64; omega)
  · exact comparison_record_at Strict022.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict022.checked 11 (by change 11 < 16; omega)

theorem e139_bounds : ExpEnclosure e139 := by
  apply exp_enclosure_of_checks e139
  · have h : (1 : Rat) ≤ e139.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 10 (by change 10 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity026.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict022.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict022.checked 13 (by change 13 < 16; omega)

theorem e140_bounds : ExpEnclosure e140 := by
  apply exp_enclosure_of_checks e140
  · have h : (1 : Rat) ≤ e140.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization003.checked 11 (by change 11 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity026.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at Strict022.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict022.checked 15 (by change 15 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e129_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e129_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e131_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e131_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e133_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e133_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e135_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e135_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e137_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e137_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e139_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e139_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
