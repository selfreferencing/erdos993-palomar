module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization001
public import Erdos993Lean.ExactComparisons.F3All.Strict011
public import Erdos993Lean.ExactComparisons.F3All.Strict012
public import Erdos993Lean.ExactComparisons.F3All.Strict013
public import Erdos993Lean.ExactComparisons.F3All.Validity024

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e048_bounds : ExpEnclosure e048 := by
  apply exp_enclosure_of_checks e048
  · have h : (1 : Rat) ≤ e048.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 47 (by change 47 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at Strict011.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict011.checked 7 (by change 7 < 16; omega)

theorem e049_bounds : ExpEnclosure e049 := by
  apply exp_enclosure_of_checks e049
  · have h : (1 : Rat) ≤ e049.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 48 (by change 48 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict011.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict011.checked 9 (by change 9 < 16; omega)

theorem e050_bounds : ExpEnclosure e050 := by
  apply exp_enclosure_of_checks e050
  · have h : (1 : Rat) ≤ e050.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 49 (by change 49 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 43 (by change 43 < 64; omega)
  · exact comparison_record_at Strict011.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict011.checked 11 (by change 11 < 16; omega)

theorem e051_bounds : ExpEnclosure e051 := by
  apply exp_enclosure_of_checks e051
  · have h : (1 : Rat) ≤ e051.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 50 (by change 50 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict011.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict011.checked 13 (by change 13 < 16; omega)

theorem e052_bounds : ExpEnclosure e052 := by
  apply exp_enclosure_of_checks e052
  · have h : (1 : Rat) ≤ e052.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 51 (by change 51 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at Strict011.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict011.checked 15 (by change 15 < 16; omega)

theorem e053_bounds : ExpEnclosure e053 := by
  apply exp_enclosure_of_checks e053
  · have h : (1 : Rat) ≤ e053.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 52 (by change 52 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict012.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict012.checked 1 (by change 1 < 16; omega)

theorem e054_bounds : ExpEnclosure e054 := by
  apply exp_enclosure_of_checks e054
  · have h : (1 : Rat) ≤ e054.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 53 (by change 53 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 47 (by change 47 < 64; omega)
  · exact comparison_record_at Strict012.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict012.checked 3 (by change 3 < 16; omega)

theorem e055_bounds : ExpEnclosure e055 := by
  apply exp_enclosure_of_checks e055
  · have h : (1 : Rat) ≤ e055.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 54 (by change 54 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict012.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict012.checked 5 (by change 5 < 16; omega)

theorem e056_bounds : ExpEnclosure e056 := by
  apply exp_enclosure_of_checks e056
  · have h : (1 : Rat) ≤ e056.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 55 (by change 55 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at Strict012.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict012.checked 7 (by change 7 < 16; omega)

theorem e057_bounds : ExpEnclosure e057 := by
  apply exp_enclosure_of_checks e057
  · have h : (1 : Rat) ≤ e057.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 56 (by change 56 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict012.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict012.checked 9 (by change 9 < 16; omega)

theorem e058_bounds : ExpEnclosure e058 := by
  apply exp_enclosure_of_checks e058
  · have h : (1 : Rat) ≤ e058.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 57 (by change 57 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 51 (by change 51 < 64; omega)
  · exact comparison_record_at Strict012.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict012.checked 11 (by change 11 < 16; omega)

theorem e059_bounds : ExpEnclosure e059 := by
  apply exp_enclosure_of_checks e059
  · have h : (1 : Rat) ≤ e059.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 58 (by change 58 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict012.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict012.checked 13 (by change 13 < 16; omega)

theorem e060_bounds : ExpEnclosure e060 := by
  apply exp_enclosure_of_checks e060
  · have h : (1 : Rat) ≤ e060.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 59 (by change 59 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at Strict012.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict012.checked 15 (by change 15 < 16; omega)

theorem e061_bounds : ExpEnclosure e061 := by
  apply exp_enclosure_of_checks e061
  · have h : (1 : Rat) ≤ e061.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 60 (by change 60 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict013.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict013.checked 1 (by change 1 < 16; omega)

theorem e062_bounds : ExpEnclosure e062 := by
  apply exp_enclosure_of_checks e062
  · have h : (1 : Rat) ≤ e062.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 61 (by change 61 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 55 (by change 55 < 64; omega)
  · exact comparison_record_at Strict013.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict013.checked 3 (by change 3 < 16; omega)

theorem e063_bounds : ExpEnclosure e063 := by
  apply exp_enclosure_of_checks e063
  · have h : (1 : Rat) ≤ e063.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 62 (by change 62 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict013.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict013.checked 5 (by change 5 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e048_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e048_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e049_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e049_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e050_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e050_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e051_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e051_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e052_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e052_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e054_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e054_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e055_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e055_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e056_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e056_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e057_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e057_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e058_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e058_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e059_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e059_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e060_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e060_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e061_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e061_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e062_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e062_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e063_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e063_bounds
