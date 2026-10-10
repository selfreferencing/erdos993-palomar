module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.ExactComparisons.F3All.Normalization003
public import Erdos993Lean.ExactComparisons.F3All.Normalization004
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality002
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality003
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality004
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality005
public import Erdos993Lean.ExactComparisons.F3All.Strict028
public import Erdos993Lean.ExactComparisons.F3All.Strict029
public import Erdos993Lean.ExactComparisons.F3All.Strict030
public import Erdos993Lean.ExactComparisons.F3All.Strict031
public import Erdos993Lean.ExactComparisons.F3All.Strict032
public import Erdos993Lean.ExactComparisons.F3All.Strict033
public import Erdos993Lean.ExactComparisons.F3All.Validity005
public import Erdos993Lean.ExactComparisons.F3All.Validity017
public import Erdos993Lean.ExactComparisons.F3All.Validity018
public import Erdos993Lean.ExactComparisons.F3All.Validity023
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025
public import Erdos993Lean.ExactComparisons.F3All.Validity026

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup007

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt097_facts : PointFacts pt097 := by
  apply pointFacts_of_quoted_checks pt097 (((7 : Rat) / (8 : Rat))) (((37154509 : Rat) / (10000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 11 (by change 11 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 10 (by change 10 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity017.checked 45 (by change 45 < 64; omega)
  · exact boolean_record_at Validity017.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict030.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict030.checked 13 (by change 13 < 16; omega)

theorem pt098_facts : PointFacts pt098 := by
  apply pointFacts_of_quoted_checks pt098 (((7 : Rat) / (8 : Rat))) (((22408447 : Rat) / (5000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 12 (by change 12 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 12 (by change 12 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity017.checked 49 (by change 49 < 64; omega)
  · exact boolean_record_at Validity017.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict031.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict031.checked 1 (by change 1 < 16; omega)

theorem pt099_facts : PointFacts pt099 := by
  apply pointFacts_of_quoted_checks pt099 (((3 : Rat) / (5 : Rat))) (((6757437 : Rat) / (1250000 : Rat))) (((3 : Rat) / (5 : Rat))) (((1689359 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity005.checked 13 (by change 13 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e126.y ∧ e126.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 52 (by change 52 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity017.checked 1 (by change 1 < 64; omega)
  · exact boolean_record_at Validity017.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict028.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict028.checked 1 (by change 1 < 16; omega)

theorem pt100_facts : PointFacts pt100 := by
  apply pointFacts_of_quoted_checks pt100 (((7 : Rat) / (8 : Rat))) (((6757437 : Rat) / (1250000 : Rat))) (((7 : Rat) / (8 : Rat))) (((1689359 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity005.checked 14 (by change 14 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e126.y ∧ e126.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 14 (by change 14 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity017.checked 53 (by change 53 < 64; omega)
  · exact boolean_record_at Validity017.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict031.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict031.checked 5 (by change 5 < 16; omega)

theorem pt101_facts : PointFacts pt101 := by
  apply pointFacts_of_quoted_checks pt101 (((7 : Rat) / (8 : Rat))) (((32604103 : Rat) / (5000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity005.checked 15 (by change 15 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 15 (by change 15 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity017.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity017.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict031.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict031.checked 7 (by change 7 < 16; omega)

theorem pt102_facts : PointFacts pt102 := by
  apply pointFacts_of_quoted_checks pt102 (((7 : Rat) / (8 : Rat))) (((23719357 : Rat) / (2500000 : Rat))) (((7 : Rat) / (8 : Rat))) (((94877357 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 16 (by change 16 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e136.y ∧ e136.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 17 (by change 17 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity017.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity017.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict031.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict031.checked 11 (by change 11 < 16; omega)

theorem pt103_facts : PointFacts pt103 := by
  apply pointFacts_of_quoted_checks pt103 (((7 : Rat) / (8 : Rat))) (((100428229 : Rat) / (5000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((40171073 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity005.checked 17 (by change 17 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e140.y ∧ e140.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 19 (by change 19 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity017.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity018.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict031.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict031.checked 15 (by change 15 < 16; omega)

theorem pt104_facts : PointFacts pt104 := by
  have hz : pt104 = zeroPoint b03 := by
    norm_num [pt104, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b03
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds

theorem pt105_facts : PointFacts pt105 := by
  apply pointFacts_of_quoted_checks pt105 (((28 : Rat) / (25 : Rat))) (((376947 : Rat) / (312500 : Rat))) (((28 : Rat) / (25 : Rat))) (((12062301 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 19 (by change 19 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e004.y ∧ e004.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity023.checked 61 (by change 61 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 20 (by change 20 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity018.checked 1 (by change 1 < 64; omega)
  · exact boolean_record_at Validity018.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict032.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict032.checked 1 (by change 1 < 16; omega)

theorem pt106_facts : PointFacts pt106 := by
  apply pointFacts_of_quoted_checks pt106 (((28 : Rat) / (25 : Rat))) (((13247849 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((6623923 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 20 (by change 20 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e008.y ∧ e008.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e008_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 21 (by change 21 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity018.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity018.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict032.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict032.checked 3 (by change 3 < 16; omega)

theorem pt107_facts : PointFacts pt107 := by
  apply pointFacts_of_quoted_checks pt107 (((28 : Rat) / (25 : Rat))) (((3637479 : Rat) / (2500000 : Rat))) (((28 : Rat) / (25 : Rat))) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 21 (by change 21 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 22 (by change 22 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity018.checked 5 (by change 5 < 64; omega)
  · exact boolean_record_at Validity018.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict032.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict032.checked 5 (by change 5 < 16; omega)

theorem pt108_facts : PointFacts pt108 := by
  apply pointFacts_of_quoted_checks pt108 (((28 : Rat) / (25 : Rat))) (((15248181 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((7624089 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 22 (by change 22 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e016.y ∧ e016.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 9 (by change 9 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e016_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 23 (by change 23 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity018.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity018.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict032.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict032.checked 7 (by change 7 < 16; omega)

theorem pt109_facts : PointFacts pt109 := by
  apply pointFacts_of_quoted_checks pt109 (((28 : Rat) / (25 : Rat))) (((3994989 : Rat) / (2500000 : Rat))) (((28 : Rat) / (25 : Rat))) (((15979953 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 23 (by change 23 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e019.y ∧ e019.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 12 (by change 12 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 24 (by change 24 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity018.checked 9 (by change 9 < 64; omega)
  · exact boolean_record_at Validity018.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict032.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict032.checked 9 (by change 9 < 16; omega)

theorem pt110_facts : PointFacts pt110 := by
  apply pointFacts_of_quoted_checks pt110 (((7 : Rat) / (8 : Rat))) (((334937 : Rat) / (200000 : Rat))) (((7 : Rat) / (8 : Rat))) (((16746847 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 24 (by change 24 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e024.y ∧ e024.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e024_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 62 (by change 62 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity017.checked 21 (by change 21 < 64; omega)
  · exact boolean_record_at Validity017.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict029.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict029.checked 5 (by change 5 < 16; omega)

theorem pt111_facts : PointFacts pt111 := by
  apply pointFacts_of_quoted_checks pt111 (((28 : Rat) / (25 : Rat))) (((334937 : Rat) / (200000 : Rat))) (((28 : Rat) / (25 : Rat))) (((16746847 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 25 (by change 25 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e024.y ∧ e024.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e024_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 26 (by change 26 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity018.checked 13 (by change 13 < 64; omega)
  · exact boolean_record_at Validity018.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict032.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict032.checked 13 (by change 13 < 16; omega)

theorem pt112_facts : PointFacts pt112 := by
  apply pointFacts_of_quoted_checks pt112 (((28 : Rat) / (25 : Rat))) (((4387637 : Rat) / (2500000 : Rat))) (((28 : Rat) / (25 : Rat))) (((3510109 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity005.checked 26 (by change 26 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e029.y ∧ e029.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 28 (by change 28 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity018.checked 17 (by change 17 < 64; omega)
  · exact boolean_record_at Validity018.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict033.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict033.checked 1 (by change 1 < 16; omega)

def points : List Point := [pt097, pt098, pt099, pt100, pt101, pt102, pt103, pt104, pt105, pt106, pt107, pt108, pt109, pt110, pt111, pt112]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt097_facts
  · exact pt098_facts
  · exact pt099_facts
  · exact pt100_facts
  · exact pt101_facts
  · exact pt102_facts
  · exact pt103_facts
  · exact pt104_facts
  · exact pt105_facts
  · exact pt106_facts
  · exact pt107_facts
  · exact pt108_facts
  · exact pt109_facts
  · exact pt110_facts
  · exact pt111_facts
  · exact pt112_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup007

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt097_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt097_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt098_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt098_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt099_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt099_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt100_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt100_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt101_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt101_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt102_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt102_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt103_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt103_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt104_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt104_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt105_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt105_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt106_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt106_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt107_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt107_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt108_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt108_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt109_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt109_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt110_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt110_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt111_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt111_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt112_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt112_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.all_points
