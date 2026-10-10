module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization001
public import Erdos993Lean.ExactComparisons.F3All.Strict005
public import Erdos993Lean.ExactComparisons.F3All.Strict006
public import Erdos993Lean.ExactComparisons.F3All.Strict007
public import Erdos993Lean.ExactComparisons.F3All.Validity023
public import Erdos993Lean.ExactComparisons.F3All.Validity024

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem e000_bounds : ExpEnclosure e000 := by
  norm_num [ExpEnclosure, e000]

theorem e001_bounds : ExpEnclosure e001 := by
  apply exp_enclosure_of_checks e001
  · have h : (1 : Rat) ≤ e001.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 0 (by change 0 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity023.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict005.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict005.checked 9 (by change 9 < 16; omega)

theorem e002_bounds : ExpEnclosure e002 := by
  apply exp_enclosure_of_checks e002
  · have h : (1 : Rat) ≤ e002.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 1 (by change 1 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity023.checked 59 (by change 59 < 64; omega)
  · exact comparison_record_at Strict005.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict005.checked 11 (by change 11 < 16; omega)

theorem e003_bounds : ExpEnclosure e003 := by
  apply exp_enclosure_of_checks e003
  · have h : (1 : Rat) ≤ e003.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 2 (by change 2 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity023.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict005.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict005.checked 13 (by change 13 < 16; omega)

theorem e004_bounds : ExpEnclosure e004 := by
  apply exp_enclosure_of_checks e004
  · have h : (1 : Rat) ≤ e004.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 3 (by change 3 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity023.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at Strict005.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict005.checked 15 (by change 15 < 16; omega)

theorem e005_bounds : ExpEnclosure e005 := by
  apply exp_enclosure_of_checks e005
  · have h : (1 : Rat) ≤ e005.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 4 (by change 4 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity023.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict006.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict006.checked 1 (by change 1 < 16; omega)

theorem e006_bounds : ExpEnclosure e006 := by
  apply exp_enclosure_of_checks e006
  · have h : (1 : Rat) ≤ e006.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 5 (by change 5 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity023.checked 63 (by change 63 < 64; omega)
  · exact comparison_record_at Strict006.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict006.checked 3 (by change 3 < 16; omega)

theorem e007_bounds : ExpEnclosure e007 := by
  apply exp_enclosure_of_checks e007
  · have h : (1 : Rat) ≤ e007.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 6 (by change 6 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict006.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict006.checked 5 (by change 5 < 16; omega)

theorem e008_bounds : ExpEnclosure e008 := by
  apply exp_enclosure_of_checks e008
  · have h : (1 : Rat) ≤ e008.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 7 (by change 7 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at Strict006.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict006.checked 7 (by change 7 < 16; omega)

theorem e009_bounds : ExpEnclosure e009 := by
  apply exp_enclosure_of_checks e009
  · have h : (1 : Rat) ≤ e009.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 8 (by change 8 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict006.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict006.checked 9 (by change 9 < 16; omega)

theorem e010_bounds : ExpEnclosure e010 := by
  apply exp_enclosure_of_checks e010
  · have h : (1 : Rat) ≤ e010.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 9 (by change 9 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 3 (by change 3 < 64; omega)
  · exact comparison_record_at Strict006.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict006.checked 11 (by change 11 < 16; omega)

theorem e011_bounds : ExpEnclosure e011 := by
  apply exp_enclosure_of_checks e011
  · have h : (1 : Rat) ≤ e011.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 10 (by change 10 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict006.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict006.checked 13 (by change 13 < 16; omega)

theorem e012_bounds : ExpEnclosure e012 := by
  apply exp_enclosure_of_checks e012
  · have h : (1 : Rat) ≤ e012.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 11 (by change 11 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at Strict006.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict006.checked 15 (by change 15 < 16; omega)

theorem e013_bounds : ExpEnclosure e013 := by
  apply exp_enclosure_of_checks e013
  · have h : (1 : Rat) ≤ e013.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 12 (by change 12 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict007.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict007.checked 1 (by change 1 < 16; omega)

theorem e014_bounds : ExpEnclosure e014 := by
  apply exp_enclosure_of_checks e014
  · have h : (1 : Rat) ≤ e014.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 13 (by change 13 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 7 (by change 7 < 64; omega)
  · exact comparison_record_at Strict007.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict007.checked 3 (by change 3 < 16; omega)

theorem e015_bounds : ExpEnclosure e015 := by
  apply exp_enclosure_of_checks e015
  · have h : (1 : Rat) ≤ e015.lo := Comparison.ofRats_sound _ _ .le
      (comparison_record_at Normalization001.checked 14 (by change 14 < 64; omega))
    exact lt_of_lt_of_le (by norm_num) h
  · exact boolean_record_at Validity024.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict007.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict007.checked 5 (by change 5 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e000_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e000_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e001_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e001_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e002_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e002_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e003_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e003_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e005_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e005_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e006_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e006_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e007_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e007_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e008_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e008_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e009_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e009_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e010_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e010_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e011_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e011_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e012_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e012_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e014_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e014_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e015_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e015_bounds
