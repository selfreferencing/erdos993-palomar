module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.ExactComparisons.F3All.Normalization003
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality001
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality002
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality003
public import Erdos993Lean.ExactComparisons.F3All.Strict025
public import Erdos993Lean.ExactComparisons.F3All.Strict027
public import Erdos993Lean.ExactComparisons.F3All.Strict028
public import Erdos993Lean.ExactComparisons.F3All.Validity004
public import Erdos993Lean.ExactComparisons.F3All.Validity016
public import Erdos993Lean.ExactComparisons.F3All.Validity017
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025
public import Erdos993Lean.ExactComparisons.F3All.Validity026

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup005

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt065_facts : PointFacts pt065 := by
  apply pointFacts_of_quoted_checks pt065 (((3 : Rat) / (5 : Rat))) (((10585001 : Rat) / (5000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 43 (by change 43 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 46 (by change 46 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity016.checked 53 (by change 53 < 64; omega)
  · exact boolean_record_at Validity016.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict027.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict027.checked 5 (by change 5 < 16; omega)

theorem pt066_facts : PointFacts pt066 := by
  apply pointFacts_of_quoted_checks pt066 (((1 : Rat) / (3 : Rat))) (((3191987 : Rat) / (1250000 : Rat))) (((1 : Rat) / (3 : Rat))) (((25535893 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 44 (by change 44 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e088.y ∧ e088.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 29 (by change 29 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity016.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity016.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict025.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict025.checked 3 (by change 3 < 16; omega)

theorem pt067_facts : PointFacts pt067 := by
  apply pointFacts_of_quoted_checks pt067 (((3 : Rat) / (5 : Rat))) (((3191987 : Rat) / (1250000 : Rat))) (((3 : Rat) / (5 : Rat))) (((25535893 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 45 (by change 45 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e088.y ∧ e088.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 48 (by change 48 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity016.checked 57 (by change 57 < 64; omega)
  · exact boolean_record_at Validity016.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict027.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict027.checked 9 (by change 9 < 16; omega)

theorem pt068_facts : PointFacts pt068 := by
  apply pointFacts_of_quoted_checks pt068 (((1 : Rat) / (3 : Rat))) (((3080217 : Rat) / (1000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 46 (by change 46 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 30 (by change 30 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity016.checked 21 (by change 21 < 64; omega)
  · exact boolean_record_at Validity016.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict025.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict025.checked 5 (by change 5 < 16; omega)

theorem pt069_facts : PointFacts pt069 := by
  apply pointFacts_of_quoted_checks pt069 (((3 : Rat) / (5 : Rat))) (((3080217 : Rat) / (1000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 47 (by change 47 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 49 (by change 49 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity016.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity016.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict027.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict027.checked 11 (by change 11 < 16; omega)

theorem pt070_facts : PointFacts pt070 := by
  apply pointFacts_of_quoted_checks pt070 (((1 : Rat) / (3 : Rat))) (((37154509 : Rat) / (10000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 48 (by change 48 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 31 (by change 31 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity016.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity016.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict025.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict025.checked 7 (by change 7 < 16; omega)

theorem pt071_facts : PointFacts pt071 := by
  apply pointFacts_of_quoted_checks pt071 (((3 : Rat) / (5 : Rat))) (((37154509 : Rat) / (10000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 49 (by change 49 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 50 (by change 50 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity016.checked 61 (by change 61 < 64; omega)
  · exact boolean_record_at Validity016.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict027.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict027.checked 13 (by change 13 < 16; omega)

theorem pt072_facts : PointFacts pt072 := by
  apply pointFacts_of_quoted_checks pt072 (((1 : Rat) / (3 : Rat))) (((22408447 : Rat) / (5000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 50 (by change 50 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 32 (by change 32 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity016.checked 25 (by change 25 < 64; omega)
  · exact boolean_record_at Validity016.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict025.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict025.checked 9 (by change 9 < 16; omega)

theorem pt073_facts : PointFacts pt073 := by
  apply pointFacts_of_quoted_checks pt073 (((3 : Rat) / (5 : Rat))) (((22408447 : Rat) / (5000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 51 (by change 51 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 51 (by change 51 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity016.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity017.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict027.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict027.checked 15 (by change 15 < 16; omega)

theorem pt074_facts : PointFacts pt074 := by
  apply pointFacts_of_quoted_checks pt074 (((1 : Rat) / (3 : Rat))) (((32604103 : Rat) / (5000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity004.checked 52 (by change 52 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 33 (by change 33 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity016.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity016.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict025.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict025.checked 11 (by change 11 < 16; omega)

theorem pt075_facts : PointFacts pt075 := by
  apply pointFacts_of_quoted_checks pt075 (((3 : Rat) / (5 : Rat))) (((32604103 : Rat) / (5000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity004.checked 53 (by change 53 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 53 (by change 53 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity017.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity017.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict028.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict028.checked 3 (by change 3 < 16; omega)

theorem pt076_facts : PointFacts pt076 := by
  apply pointFacts_of_quoted_checks pt076 (((1 : Rat) / (3 : Rat))) (((23719357 : Rat) / (2500000 : Rat))) (((1 : Rat) / (3 : Rat))) (((94877357 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 54 (by change 54 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e136.y ∧ e136.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 34 (by change 34 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity016.checked 29 (by change 29 < 64; omega)
  · exact boolean_record_at Validity016.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict025.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict025.checked 13 (by change 13 < 16; omega)

theorem pt077_facts : PointFacts pt077 := by
  apply pointFacts_of_quoted_checks pt077 (((3 : Rat) / (5 : Rat))) (((23719357 : Rat) / (2500000 : Rat))) (((3 : Rat) / (5 : Rat))) (((94877357 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 55 (by change 55 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e136.y ∧ e136.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 54 (by change 54 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity017.checked 5 (by change 5 < 64; omega)
  · exact boolean_record_at Validity017.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict028.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict028.checked 5 (by change 5 < 16; omega)

theorem pt078_facts : PointFacts pt078 := by
  apply pointFacts_of_quoted_checks pt078 (((1 : Rat) / (3 : Rat))) (((100428229 : Rat) / (5000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((40171073 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity004.checked 56 (by change 56 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e140.y ∧ e140.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 35 (by change 35 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity016.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity016.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict025.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict025.checked 15 (by change 15 < 16; omega)

theorem pt079_facts : PointFacts pt079 := by
  apply pointFacts_of_quoted_checks pt079 (((3 : Rat) / (5 : Rat))) (((100428229 : Rat) / (5000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((40171073 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity004.checked 57 (by change 57 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e140.y ∧ e140.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 55 (by change 55 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity017.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity017.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict028.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict028.checked 7 (by change 7 < 16; omega)

theorem pt080_facts : PointFacts pt080 := by
  have hz : pt080 = zeroPoint b02 := by
    norm_num [pt080, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b02
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds

def points : List Point := [pt065, pt066, pt067, pt068, pt069, pt070, pt071, pt072, pt073, pt074, pt075, pt076, pt077, pt078, pt079, pt080]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt065_facts
  · exact pt066_facts
  · exact pt067_facts
  · exact pt068_facts
  · exact pt069_facts
  · exact pt070_facts
  · exact pt071_facts
  · exact pt072_facts
  · exact pt073_facts
  · exact pt074_facts
  · exact pt075_facts
  · exact pt076_facts
  · exact pt077_facts
  · exact pt078_facts
  · exact pt079_facts
  · exact pt080_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup005

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt065_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt065_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt066_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt066_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt067_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt067_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt068_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt068_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt069_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt069_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt070_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt070_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt071_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt071_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt072_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt072_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt073_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt073_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt074_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt074_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt075_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt075_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt076_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt076_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt077_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt077_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt078_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt078_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt079_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt079_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt080_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt080_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.all_points
