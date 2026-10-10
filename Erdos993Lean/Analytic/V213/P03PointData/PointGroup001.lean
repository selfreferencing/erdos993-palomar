module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.ExactComparisons.F3All.Normalization005
public import Erdos993Lean.ExactComparisons.F3All.Normalization006
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality007
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality008
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality009
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality011
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality012
public import Erdos993Lean.ExactComparisons.F3All.Strict037
public import Erdos993Lean.ExactComparisons.F3All.Strict039
public import Erdos993Lean.ExactComparisons.F3All.Strict040
public import Erdos993Lean.ExactComparisons.F3All.Strict044
public import Erdos993Lean.ExactComparisons.F3All.Strict045
public import Erdos993Lean.ExactComparisons.F3All.Strict047
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity019
public import Erdos993Lean.ExactComparisons.F3All.Validity020
public import Erdos993Lean.ExactComparisons.F3All.Validity021
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup001

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt001_facts : PointFacts pt001 := by
  have hz : pt001 = zeroPoint b05 := by
    norm_num [pt001, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b05
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds

theorem pt002_facts : PointFacts pt002 := by
  apply pointFacts_of_quoted_checks pt002 (((263 : Rat) / (200 : Rat))) (((15219617 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((7609807 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity003.checked 44 (by change 44 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e015.y ∧ e015.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 8 (by change 8 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e015_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 3 (by change 3 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity019.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity019.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict037.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict037.checked 15 (by change 15 < 16; omega)

theorem pt003_facts : PointFacts pt003 := by
  apply pointFacts_of_quoted_checks pt003 (((263 : Rat) / (200 : Rat))) (((18776107 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((2347013 : Rat) / (1250000 : Rat)))
  · exact boolean_record_at Validity003.checked 45 (by change 45 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e036.y ∧ e036.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 29 (by change 29 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e036_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 12 (by change 12 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity019.checked 49 (by change 49 < 64; omega)
  · exact boolean_record_at Validity019.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict039.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict039.checked 1 (by change 1 < 16; omega)

theorem pt004_facts : PointFacts pt004 := by
  apply pointFacts_of_quoted_checks pt004 (((263 : Rat) / (200 : Rat))) (((4947047 : Rat) / (2500000 : Rat))) (((263 : Rat) / (200 : Rat))) (((3957637 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity003.checked 46 (by change 46 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e043.y ∧ e043.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 36 (by change 36 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e043_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 16 (by change 16 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity019.checked 57 (by change 57 < 64; omega)
  · exact boolean_record_at Validity019.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict039.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict039.checked 9 (by change 9 < 16; omega)

theorem pt005_facts : PointFacts pt005 := by
  apply pointFacts_of_quoted_checks pt005 (((263 : Rat) / (200 : Rat))) (((20854821 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((10427409 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity003.checked 47 (by change 47 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e050.y ∧ e050.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 43 (by change 43 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e050_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 19 (by change 19 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity019.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity020.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict039.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict039.checked 15 (by change 15 < 16; omega)

theorem pt006_facts : PointFacts pt006 := by
  apply pointFacts_of_quoted_checks pt006 (((263 : Rat) / (200 : Rat))) (((439579 : Rat) / (200000 : Rat))) (((263 : Rat) / (200 : Rat))) (((21978947 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity003.checked 48 (by change 48 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e059.y ∧ e059.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 52 (by change 52 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e059_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 22 (by change 22 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity020.checked 5 (by change 5 < 64; omega)
  · exact boolean_record_at Validity020.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict040.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict040.checked 5 (by change 5 < 16; omega)

theorem pt007_facts : PointFacts pt007 := by
  apply pointFacts_of_quoted_checks pt007 (((263 : Rat) / (200 : Rat))) (((23163671 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((5790917 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity003.checked 49 (by change 49 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e070.y ∧ e070.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e070_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 25 (by change 25 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity020.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity020.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict040.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict040.checked 11 (by change 11 < 16; omega)

theorem pt008_facts : PointFacts pt008 := by
  have hz : pt008 = zeroPoint b06 := by
    norm_num [pt008, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b06
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds

theorem pt009_facts : PointFacts pt009 := by
  apply pointFacts_of_quoted_checks pt009 (((3 : Rat) / (2 : Rat))) (((15840741 : Rat) / (10000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((7920369 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity003.checked 51 (by change 51 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e018.y ∧ e018.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 11 (by change 11 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e018_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 53 (by change 53 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity021.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity021.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict044.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict044.checked 3 (by change 3 < 16; omega)

theorem pt010_facts : PointFacts pt010 := by
  apply pointFacts_of_quoted_checks pt010 (((3 : Rat) / (2 : Rat))) (((19937157 : Rat) / (10000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((9968577 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity003.checked 52 (by change 52 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e045.y ∧ e045.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 38 (by change 38 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e045_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 56 (by change 56 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity021.checked 9 (by change 9 < 64; omega)
  · exact boolean_record_at Validity021.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict044.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict044.checked 9 (by change 9 < 16; omega)

theorem pt011_facts : PointFacts pt011 := by
  apply pointFacts_of_quoted_checks pt011 (((3 : Rat) / (2 : Rat))) (((21117143 : Rat) / (10000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((1055857 : Rat) / (500000 : Rat)))
  · exact boolean_record_at Validity003.checked 53 (by change 53 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e052.y ∧ e052.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 45 (by change 45 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e052_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 57 (by change 57 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity021.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity021.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict044.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict044.checked 11 (by change 11 < 16; omega)

theorem pt012_facts : PointFacts pt012 := by
  apply pointFacts_of_quoted_checks pt012 (((3 : Rat) / (2 : Rat))) (((22366967 : Rat) / (10000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((22366963 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity003.checked 54 (by change 54 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e062.y ∧ e062.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e062_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 59 (by change 59 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity021.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity021.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict044.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict044.checked 15 (by change 15 < 16; omega)

theorem pt013_facts : PointFacts pt013 := by
  apply pointFacts_of_quoted_checks pt013 (((3 : Rat) / (2 : Rat))) (((5018581 : Rat) / (2000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((12546451 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity003.checked 55 (by change 55 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e086.y ∧ e086.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 15 (by change 15 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e086_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 61 (by change 61 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity021.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity021.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict045.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict045.checked 3 (by change 3 < 16; omega)

theorem pt014_facts : PointFacts pt014 := by
  have hz : pt014 = zeroPoint b07 := by
    norm_num [pt014, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b07
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds

theorem pt015_facts : PointFacts pt015 := by
  apply pointFacts_of_quoted_checks pt015 (((7 : Rat) / (4 : Rat))) (((16652913 : Rat) / (10000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((1665291 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity003.checked 57 (by change 57 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e023.y ∧ e023.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 16 (by change 16 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e023_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 12 (by change 12 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity021.checked 49 (by change 49 < 64; omega)
  · exact boolean_record_at Validity021.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict047.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict047.checked 1 (by change 1 < 16; omega)

theorem pt016_facts : PointFacts pt016 := by
  apply pointFacts_of_quoted_checks pt016 (((7 : Rat) / (4 : Rat))) (((18917457 : Rat) / (10000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((9458727 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity003.checked 58 (by change 58 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e038.y ∧ e038.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 31 (by change 31 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e038_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 14 (by change 14 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity021.checked 53 (by change 53 < 64; omega)
  · exact boolean_record_at Validity021.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict047.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict047.checked 5 (by change 5 < 16; omega)

def points : List Point := [pt001, pt002, pt003, pt004, pt005, pt006, pt007, pt008, pt009, pt010, pt011, pt012, pt013, pt014, pt015, pt016]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt001_facts
  · exact pt002_facts
  · exact pt003_facts
  · exact pt004_facts
  · exact pt005_facts
  · exact pt006_facts
  · exact pt007_facts
  · exact pt008_facts
  · exact pt009_facts
  · exact pt010_facts
  · exact pt011_facts
  · exact pt012_facts
  · exact pt013_facts
  · exact pt014_facts
  · exact pt015_facts
  · exact pt016_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup001

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt001_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt001_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt002_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt002_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt003_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt003_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt004_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt004_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt005_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt005_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt006_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt006_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt007_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt007_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt008_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt008_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt009_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt009_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt010_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt010_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt011_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt011_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt012_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt012_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt013_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt013_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt014_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt014_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt015_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt015_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt016_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt016_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.all_points
