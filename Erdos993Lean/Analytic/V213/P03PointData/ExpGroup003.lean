module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization001
public import Erdos993Lean.ExactComparisons.F3All.Strict009
public import Erdos993Lean.ExactComparisons.F3All.Strict010
public import Erdos993Lean.ExactComparisons.F3All.Strict011
public import Erdos993Lean.ExactComparisons.F3All.Validity024

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e032_bounds : ExpEnclosure e032 := by
  apply exp_enclosure_of_checks e032
  · have h : (1 : Rat) ≤ e032.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 31 (by change 31 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at Strict009.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict009.checked 7 (by change 7 < 16; omega)

theorem e033_bounds : ExpEnclosure e033 := by
  apply exp_enclosure_of_checks e033
  · have h : (1 : Rat) ≤ e033.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 32 (by change 32 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict009.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict009.checked 9 (by change 9 < 16; omega)

theorem e034_bounds : ExpEnclosure e034 := by
  apply exp_enclosure_of_checks e034
  · have h : (1 : Rat) ≤ e034.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 33 (by change 33 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 27 (by change 27 < 64; omega)
  · exact comparison_record_at Strict009.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict009.checked 11 (by change 11 < 16; omega)

theorem e035_bounds : ExpEnclosure e035 := by
  apply exp_enclosure_of_checks e035
  · have h : (1 : Rat) ≤ e035.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 34 (by change 34 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict009.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict009.checked 13 (by change 13 < 16; omega)

theorem e036_bounds : ExpEnclosure e036 := by
  apply exp_enclosure_of_checks e036
  · have h : (1 : Rat) ≤ e036.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 35 (by change 35 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at Strict009.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict009.checked 15 (by change 15 < 16; omega)

theorem e037_bounds : ExpEnclosure e037 := by
  apply exp_enclosure_of_checks e037
  · have h : (1 : Rat) ≤ e037.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 36 (by change 36 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict010.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict010.checked 1 (by change 1 < 16; omega)

theorem e038_bounds : ExpEnclosure e038 := by
  apply exp_enclosure_of_checks e038
  · have h : (1 : Rat) ≤ e038.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 37 (by change 37 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 31 (by change 31 < 64; omega)
  · exact comparison_record_at Strict010.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict010.checked 3 (by change 3 < 16; omega)

theorem e039_bounds : ExpEnclosure e039 := by
  apply exp_enclosure_of_checks e039
  · have h : (1 : Rat) ≤ e039.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 38 (by change 38 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict010.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict010.checked 5 (by change 5 < 16; omega)

theorem e040_bounds : ExpEnclosure e040 := by
  apply exp_enclosure_of_checks e040
  · have h : (1 : Rat) ≤ e040.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 39 (by change 39 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at Strict010.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict010.checked 7 (by change 7 < 16; omega)

theorem e041_bounds : ExpEnclosure e041 := by
  apply exp_enclosure_of_checks e041
  · have h : (1 : Rat) ≤ e041.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 40 (by change 40 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict010.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict010.checked 9 (by change 9 < 16; omega)

theorem e042_bounds : ExpEnclosure e042 := by
  apply exp_enclosure_of_checks e042
  · have h : (1 : Rat) ≤ e042.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 41 (by change 41 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 35 (by change 35 < 64; omega)
  · exact comparison_record_at Strict010.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict010.checked 11 (by change 11 < 16; omega)

theorem e043_bounds : ExpEnclosure e043 := by
  apply exp_enclosure_of_checks e043
  · have h : (1 : Rat) ≤ e043.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 42 (by change 42 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict010.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict010.checked 13 (by change 13 < 16; omega)

theorem e044_bounds : ExpEnclosure e044 := by
  apply exp_enclosure_of_checks e044
  · have h : (1 : Rat) ≤ e044.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 43 (by change 43 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at Strict010.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict010.checked 15 (by change 15 < 16; omega)

theorem e045_bounds : ExpEnclosure e045 := by
  apply exp_enclosure_of_checks e045
  · have h : (1 : Rat) ≤ e045.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 44 (by change 44 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict011.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict011.checked 1 (by change 1 < 16; omega)

theorem e046_bounds : ExpEnclosure e046 := by
  apply exp_enclosure_of_checks e046
  · have h : (1 : Rat) ≤ e046.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 45 (by change 45 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 39 (by change 39 < 64; omega)
  · exact comparison_record_at Strict011.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict011.checked 3 (by change 3 < 16; omega)

theorem e047_bounds : ExpEnclosure e047 := by
  apply exp_enclosure_of_checks e047
  · have h : (1 : Rat) ≤ e047.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 46 (by change 46 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict011.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict011.checked 5 (by change 5 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e032_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e032_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e033_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e033_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e034_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e034_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e035_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e035_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e036_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e036_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e037_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e037_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e038_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e038_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e039_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e039_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e041_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e041_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e042_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e042_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e043_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e043_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e044_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e044_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e045_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e045_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e046_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e046_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e047_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e047_bounds
