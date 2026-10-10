module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization002
public import Erdos993Lean.ExactComparisons.F3All.Strict015
public import Erdos993Lean.ExactComparisons.F3All.Strict016
public import Erdos993Lean.ExactComparisons.F3All.Strict017
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e080_bounds : ExpEnclosure e080 := by
  apply exp_enclosure_of_checks e080
  · have h : (1 : Rat) ≤ e080.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 15 (by change 15 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at Strict015.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict015.checked 7 (by change 7 < 16; omega)

theorem e081_bounds : ExpEnclosure e081 := by
  apply exp_enclosure_of_checks e081
  · have h : (1 : Rat) ≤ e081.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 16 (by change 16 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict015.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict015.checked 9 (by change 9 < 16; omega)

theorem e082_bounds : ExpEnclosure e082 := by
  apply exp_enclosure_of_checks e082
  · have h : (1 : Rat) ≤ e082.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 17 (by change 17 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 11 (by change 11 < 64; omega)
  · exact comparison_record_at Strict015.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict015.checked 11 (by change 11 < 16; omega)

theorem e083_bounds : ExpEnclosure e083 := by
  apply exp_enclosure_of_checks e083
  · have h : (1 : Rat) ≤ e083.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 18 (by change 18 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict015.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict015.checked 13 (by change 13 < 16; omega)

theorem e084_bounds : ExpEnclosure e084 := by
  apply exp_enclosure_of_checks e084
  · have h : (1 : Rat) ≤ e084.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 19 (by change 19 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at Strict015.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict015.checked 15 (by change 15 < 16; omega)

theorem e085_bounds : ExpEnclosure e085 := by
  apply exp_enclosure_of_checks e085
  · have h : (1 : Rat) ≤ e085.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 20 (by change 20 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict016.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict016.checked 1 (by change 1 < 16; omega)

theorem e086_bounds : ExpEnclosure e086 := by
  apply exp_enclosure_of_checks e086
  · have h : (1 : Rat) ≤ e086.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 21 (by change 21 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 15 (by change 15 < 64; omega)
  · exact comparison_record_at Strict016.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict016.checked 3 (by change 3 < 16; omega)

theorem e087_bounds : ExpEnclosure e087 := by
  apply exp_enclosure_of_checks e087
  · have h : (1 : Rat) ≤ e087.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 22 (by change 22 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict016.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict016.checked 5 (by change 5 < 16; omega)

theorem e088_bounds : ExpEnclosure e088 := by
  apply exp_enclosure_of_checks e088
  · have h : (1 : Rat) ≤ e088.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 23 (by change 23 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at Strict016.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict016.checked 7 (by change 7 < 16; omega)

theorem e089_bounds : ExpEnclosure e089 := by
  apply exp_enclosure_of_checks e089
  · have h : (1 : Rat) ≤ e089.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 24 (by change 24 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict016.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict016.checked 9 (by change 9 < 16; omega)

theorem e090_bounds : ExpEnclosure e090 := by
  apply exp_enclosure_of_checks e090
  · have h : (1 : Rat) ≤ e090.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 25 (by change 25 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 19 (by change 19 < 64; omega)
  · exact comparison_record_at Strict016.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict016.checked 11 (by change 11 < 16; omega)

theorem e091_bounds : ExpEnclosure e091 := by
  apply exp_enclosure_of_checks e091
  · have h : (1 : Rat) ≤ e091.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 26 (by change 26 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict016.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict016.checked 13 (by change 13 < 16; omega)

theorem e092_bounds : ExpEnclosure e092 := by
  apply exp_enclosure_of_checks e092
  · have h : (1 : Rat) ≤ e092.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 27 (by change 27 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at Strict016.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict016.checked 15 (by change 15 < 16; omega)

theorem e093_bounds : ExpEnclosure e093 := by
  apply exp_enclosure_of_checks e093
  · have h : (1 : Rat) ≤ e093.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 28 (by change 28 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict017.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict017.checked 1 (by change 1 < 16; omega)

theorem e094_bounds : ExpEnclosure e094 := by
  apply exp_enclosure_of_checks e094
  · have h : (1 : Rat) ≤ e094.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 29 (by change 29 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 23 (by change 23 < 64; omega)
  · exact comparison_record_at Strict017.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict017.checked 3 (by change 3 < 16; omega)

theorem e095_bounds : ExpEnclosure e095 := by
  apply exp_enclosure_of_checks e095
  · have h : (1 : Rat) ≤ e095.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 30 (by change 30 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict017.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict017.checked 5 (by change 5 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e080_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e080_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e081_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e081_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e082_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e082_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e083_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e083_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e084_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e084_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e085_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e085_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e086_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e086_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e087_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e087_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e089_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e089_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e090_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e090_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e091_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e091_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e092_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e092_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e093_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e093_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e094_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e094_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e095_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e095_bounds
