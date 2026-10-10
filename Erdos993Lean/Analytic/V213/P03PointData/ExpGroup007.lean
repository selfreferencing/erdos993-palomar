module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization002
public import Erdos993Lean.ExactComparisons.F3All.Strict017
public import Erdos993Lean.ExactComparisons.F3All.Strict018
public import Erdos993Lean.ExactComparisons.F3All.Strict019
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e096_bounds : ExpEnclosure e096 := by
  apply exp_enclosure_of_checks e096
  · have h : (1 : Rat) ≤ e096.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 31 (by change 31 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at Strict017.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict017.checked 7 (by change 7 < 16; omega)

theorem e097_bounds : ExpEnclosure e097 := by
  apply exp_enclosure_of_checks e097
  · have h : (1 : Rat) ≤ e097.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 32 (by change 32 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict017.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict017.checked 9 (by change 9 < 16; omega)

theorem e098_bounds : ExpEnclosure e098 := by
  apply exp_enclosure_of_checks e098
  · have h : (1 : Rat) ≤ e098.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 33 (by change 33 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 27 (by change 27 < 64; omega)
  · exact comparison_record_at Strict017.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict017.checked 11 (by change 11 < 16; omega)

theorem e099_bounds : ExpEnclosure e099 := by
  apply exp_enclosure_of_checks e099
  · have h : (1 : Rat) ≤ e099.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 34 (by change 34 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict017.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict017.checked 13 (by change 13 < 16; omega)

theorem e100_bounds : ExpEnclosure e100 := by
  apply exp_enclosure_of_checks e100
  · have h : (1 : Rat) ≤ e100.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 35 (by change 35 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at Strict017.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict017.checked 15 (by change 15 < 16; omega)

theorem e101_bounds : ExpEnclosure e101 := by
  apply exp_enclosure_of_checks e101
  · have h : (1 : Rat) ≤ e101.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 36 (by change 36 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict018.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict018.checked 1 (by change 1 < 16; omega)

theorem e102_bounds : ExpEnclosure e102 := by
  apply exp_enclosure_of_checks e102
  · have h : (1 : Rat) ≤ e102.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 37 (by change 37 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 31 (by change 31 < 64; omega)
  · exact comparison_record_at Strict018.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict018.checked 3 (by change 3 < 16; omega)

theorem e103_bounds : ExpEnclosure e103 := by
  apply exp_enclosure_of_checks e103
  · have h : (1 : Rat) ≤ e103.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 38 (by change 38 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict018.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict018.checked 5 (by change 5 < 16; omega)

theorem e104_bounds : ExpEnclosure e104 := by
  apply exp_enclosure_of_checks e104
  · have h : (1 : Rat) ≤ e104.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 39 (by change 39 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at Strict018.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict018.checked 7 (by change 7 < 16; omega)

theorem e105_bounds : ExpEnclosure e105 := by
  apply exp_enclosure_of_checks e105
  · have h : (1 : Rat) ≤ e105.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 40 (by change 40 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict018.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict018.checked 9 (by change 9 < 16; omega)

theorem e106_bounds : ExpEnclosure e106 := by
  apply exp_enclosure_of_checks e106
  · have h : (1 : Rat) ≤ e106.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 41 (by change 41 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 35 (by change 35 < 64; omega)
  · exact comparison_record_at Strict018.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict018.checked 11 (by change 11 < 16; omega)

theorem e107_bounds : ExpEnclosure e107 := by
  apply exp_enclosure_of_checks e107
  · have h : (1 : Rat) ≤ e107.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 42 (by change 42 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict018.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict018.checked 13 (by change 13 < 16; omega)

theorem e108_bounds : ExpEnclosure e108 := by
  apply exp_enclosure_of_checks e108
  · have h : (1 : Rat) ≤ e108.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 43 (by change 43 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at Strict018.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict018.checked 15 (by change 15 < 16; omega)

theorem e109_bounds : ExpEnclosure e109 := by
  apply exp_enclosure_of_checks e109
  · have h : (1 : Rat) ≤ e109.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 44 (by change 44 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict019.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict019.checked 1 (by change 1 < 16; omega)

theorem e110_bounds : ExpEnclosure e110 := by
  apply exp_enclosure_of_checks e110
  · have h : (1 : Rat) ≤ e110.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 45 (by change 45 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 39 (by change 39 < 64; omega)
  · exact comparison_record_at Strict019.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict019.checked 3 (by change 3 < 16; omega)

theorem e111_bounds : ExpEnclosure e111 := by
  apply exp_enclosure_of_checks e111
  · have h : (1 : Rat) ≤ e111.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 46 (by change 46 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict019.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict019.checked 5 (by change 5 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e096_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e096_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e098_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e098_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e099_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e099_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e100_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e100_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e101_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e101_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e102_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e102_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e104_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e104_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e105_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e105_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e106_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e106_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e107_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e107_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e109_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e109_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e110_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e110_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e111_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e111_bounds
