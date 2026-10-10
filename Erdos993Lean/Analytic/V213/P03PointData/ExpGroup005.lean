module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization001
public import Erdos993Lean.ExactComparisons.F3All.Normalization002
public import Erdos993Lean.ExactComparisons.F3All.Strict013
public import Erdos993Lean.ExactComparisons.F3All.Strict014
public import Erdos993Lean.ExactComparisons.F3All.Strict015
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e064_bounds : ExpEnclosure e064 := by
  apply exp_enclosure_of_checks e064
  · have h : (1 : Rat) ≤ e064.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 63 (by change 63 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at Strict013.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict013.checked 7 (by change 7 < 16; omega)

theorem e065_bounds : ExpEnclosure e065 := by
  apply exp_enclosure_of_checks e065
  · have h : (1 : Rat) ≤ e065.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 0 (by change 0 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict013.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict013.checked 9 (by change 9 < 16; omega)

theorem e066_bounds : ExpEnclosure e066 := by
  apply exp_enclosure_of_checks e066
  · have h : (1 : Rat) ≤ e066.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 1 (by change 1 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 59 (by change 59 < 64; omega)
  · exact comparison_record_at Strict013.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict013.checked 11 (by change 11 < 16; omega)

theorem e067_bounds : ExpEnclosure e067 := by
  apply exp_enclosure_of_checks e067
  · have h : (1 : Rat) ≤ e067.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 2 (by change 2 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict013.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict013.checked 13 (by change 13 < 16; omega)

theorem e068_bounds : ExpEnclosure e068 := by
  apply exp_enclosure_of_checks e068
  · have h : (1 : Rat) ≤ e068.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 3 (by change 3 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at Strict013.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict013.checked 15 (by change 15 < 16; omega)

theorem e069_bounds : ExpEnclosure e069 := by
  apply exp_enclosure_of_checks e069
  · have h : (1 : Rat) ≤ e069.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 4 (by change 4 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict014.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict014.checked 1 (by change 1 < 16; omega)

theorem e070_bounds : ExpEnclosure e070 := by
  apply exp_enclosure_of_checks e070
  · have h : (1 : Rat) ≤ e070.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 5 (by change 5 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 63 (by change 63 < 64; omega)
  · exact comparison_record_at Strict014.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict014.checked 3 (by change 3 < 16; omega)

theorem e071_bounds : ExpEnclosure e071 := by
  apply exp_enclosure_of_checks e071
  · have h : (1 : Rat) ≤ e071.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 6 (by change 6 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict014.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict014.checked 5 (by change 5 < 16; omega)

theorem e072_bounds : ExpEnclosure e072 := by
  apply exp_enclosure_of_checks e072
  · have h : (1 : Rat) ≤ e072.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 7 (by change 7 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at Strict014.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict014.checked 7 (by change 7 < 16; omega)

theorem e073_bounds : ExpEnclosure e073 := by
  apply exp_enclosure_of_checks e073
  · have h : (1 : Rat) ≤ e073.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 8 (by change 8 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict014.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict014.checked 9 (by change 9 < 16; omega)

theorem e074_bounds : ExpEnclosure e074 := by
  apply exp_enclosure_of_checks e074
  · have h : (1 : Rat) ≤ e074.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 9 (by change 9 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 3 (by change 3 < 64; omega)
  · exact comparison_record_at Strict014.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict014.checked 11 (by change 11 < 16; omega)

theorem e075_bounds : ExpEnclosure e075 := by
  apply exp_enclosure_of_checks e075
  · have h : (1 : Rat) ≤ e075.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 10 (by change 10 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict014.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict014.checked 13 (by change 13 < 16; omega)

theorem e076_bounds : ExpEnclosure e076 := by
  apply exp_enclosure_of_checks e076
  · have h : (1 : Rat) ≤ e076.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 11 (by change 11 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at Strict014.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict014.checked 15 (by change 15 < 16; omega)

theorem e077_bounds : ExpEnclosure e077 := by
  apply exp_enclosure_of_checks e077
  · have h : (1 : Rat) ≤ e077.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 12 (by change 12 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict015.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict015.checked 1 (by change 1 < 16; omega)

theorem e078_bounds : ExpEnclosure e078 := by
  apply exp_enclosure_of_checks e078
  · have h : (1 : Rat) ≤ e078.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 13 (by change 13 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 7 (by change 7 < 64; omega)
  · exact comparison_record_at Strict015.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict015.checked 3 (by change 3 < 16; omega)

theorem e079_bounds : ExpEnclosure e079 := by
  apply exp_enclosure_of_checks e079
  · have h : (1 : Rat) ≤ e079.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization002.checked 14 (by change 14 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity025.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict015.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict015.checked 5 (by change 5 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e064_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e064_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e065_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e065_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e066_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e066_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e067_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e067_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e068_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e068_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e069_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e069_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e070_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e070_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e072_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e072_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e073_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e073_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e074_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e074_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e075_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e075_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e076_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e076_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e077_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e077_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e078_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e078_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e079_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e079_bounds
