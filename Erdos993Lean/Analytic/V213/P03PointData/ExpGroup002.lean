module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization001
public import Erdos993Lean.ExactComparisons.F3All.Strict007
public import Erdos993Lean.ExactComparisons.F3All.Strict008
public import Erdos993Lean.ExactComparisons.F3All.Strict009
public import Erdos993Lean.ExactComparisons.F3All.Validity024

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e016_bounds : ExpEnclosure e016 := by
  apply exp_enclosure_of_checks e016
  · have h : (1 : Rat) ≤ e016.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 15 (by change 15 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at Strict007.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict007.checked 7 (by change 7 < 16; omega)

theorem e017_bounds : ExpEnclosure e017 := by
  apply exp_enclosure_of_checks e017
  · have h : (1 : Rat) ≤ e017.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 16 (by change 16 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict007.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict007.checked 9 (by change 9 < 16; omega)

theorem e018_bounds : ExpEnclosure e018 := by
  apply exp_enclosure_of_checks e018
  · have h : (1 : Rat) ≤ e018.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 17 (by change 17 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 11 (by change 11 < 64; omega)
  · exact comparison_record_at Strict007.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict007.checked 11 (by change 11 < 16; omega)

theorem e019_bounds : ExpEnclosure e019 := by
  apply exp_enclosure_of_checks e019
  · have h : (1 : Rat) ≤ e019.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 18 (by change 18 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict007.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict007.checked 13 (by change 13 < 16; omega)

theorem e020_bounds : ExpEnclosure e020 := by
  apply exp_enclosure_of_checks e020
  · have h : (1 : Rat) ≤ e020.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 19 (by change 19 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at Strict007.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict007.checked 15 (by change 15 < 16; omega)

theorem e021_bounds : ExpEnclosure e021 := by
  apply exp_enclosure_of_checks e021
  · have h : (1 : Rat) ≤ e021.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 20 (by change 20 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict008.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict008.checked 1 (by change 1 < 16; omega)

theorem e022_bounds : ExpEnclosure e022 := by
  apply exp_enclosure_of_checks e022
  · have h : (1 : Rat) ≤ e022.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 21 (by change 21 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 15 (by change 15 < 64; omega)
  · exact comparison_record_at Strict008.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict008.checked 3 (by change 3 < 16; omega)

theorem e023_bounds : ExpEnclosure e023 := by
  apply exp_enclosure_of_checks e023
  · have h : (1 : Rat) ≤ e023.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 22 (by change 22 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict008.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict008.checked 5 (by change 5 < 16; omega)

theorem e024_bounds : ExpEnclosure e024 := by
  apply exp_enclosure_of_checks e024
  · have h : (1 : Rat) ≤ e024.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 23 (by change 23 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at Strict008.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict008.checked 7 (by change 7 < 16; omega)

theorem e025_bounds : ExpEnclosure e025 := by
  apply exp_enclosure_of_checks e025
  · have h : (1 : Rat) ≤ e025.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 24 (by change 24 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict008.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict008.checked 9 (by change 9 < 16; omega)

theorem e026_bounds : ExpEnclosure e026 := by
  apply exp_enclosure_of_checks e026
  · have h : (1 : Rat) ≤ e026.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 25 (by change 25 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 19 (by change 19 < 64; omega)
  · exact comparison_record_at Strict008.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict008.checked 11 (by change 11 < 16; omega)

theorem e027_bounds : ExpEnclosure e027 := by
  apply exp_enclosure_of_checks e027
  · have h : (1 : Rat) ≤ e027.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 26 (by change 26 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict008.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict008.checked 13 (by change 13 < 16; omega)

theorem e028_bounds : ExpEnclosure e028 := by
  apply exp_enclosure_of_checks e028
  · have h : (1 : Rat) ≤ e028.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 27 (by change 27 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at Strict008.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict008.checked 15 (by change 15 < 16; omega)

theorem e029_bounds : ExpEnclosure e029 := by
  apply exp_enclosure_of_checks e029
  · have h : (1 : Rat) ≤ e029.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 28 (by change 28 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict009.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict009.checked 1 (by change 1 < 16; omega)

theorem e030_bounds : ExpEnclosure e030 := by
  apply exp_enclosure_of_checks e030
  · have h : (1 : Rat) ≤ e030.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 29 (by change 29 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 23 (by change 23 < 64; omega)
  · exact comparison_record_at Strict009.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict009.checked 3 (by change 3 < 16; omega)

theorem e031_bounds : ExpEnclosure e031 := by
  apply exp_enclosure_of_checks e031
  · have h : (1 : Rat) ≤ e031.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 30 (by change 30 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict009.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict009.checked 5 (by change 5 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e016_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e016_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e017_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e017_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e018_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e018_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e020_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e020_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e021_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e021_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e022_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e022_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e023_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e023_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e024_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e024_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e025_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e025_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e026_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e026_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e027_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e027_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e028_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e028_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e030_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e030_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e031_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e031_bounds
