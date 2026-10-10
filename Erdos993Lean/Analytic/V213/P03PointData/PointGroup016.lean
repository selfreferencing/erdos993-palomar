module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.ExactComparisons.F3All.Normalization006
public import Erdos993Lean.ExactComparisons.F3All.Normalization007
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality014
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality015
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality016
public import Erdos993Lean.ExactComparisons.F3All.Strict050
public import Erdos993Lean.ExactComparisons.F3All.Strict051
public import Erdos993Lean.ExactComparisons.F3All.Strict052
public import Erdos993Lean.ExactComparisons.F3All.Strict054
public import Erdos993Lean.ExactComparisons.F3All.Validity007
public import Erdos993Lean.ExactComparisons.F3All.Validity022
public import Erdos993Lean.ExactComparisons.F3All.Validity023
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025
public import Erdos993Lean.ExactComparisons.F3All.Validity026

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup016

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt241_facts : PointFacts pt241 := by
  apply pointFacts_of_quoted_checks pt241 ((2 : Rat)) (((3080217 : Rat) / (1000000 : Rat))) ((2 : Rat)) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 27 (by change 27 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 42 (by change 42 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity022.checked 45 (by change 45 < 64; omega)
  · exact boolean_record_at Validity022.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict050.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict050.checked 13 (by change 13 < 16; omega)

theorem pt242_facts : PointFacts pt242 := by
  apply pointFacts_of_quoted_checks pt242 ((2 : Rat)) (((37154509 : Rat) / (10000000 : Rat))) ((2 : Rat)) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity007.checked 28 (by change 28 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 43 (by change 43 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity022.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity022.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict050.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict050.checked 15 (by change 15 < 16; omega)

theorem pt243_facts : PointFacts pt243 := by
  apply pointFacts_of_quoted_checks pt243 ((2 : Rat)) (((22408447 : Rat) / (5000000 : Rat))) ((2 : Rat)) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 29 (by change 29 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 44 (by change 44 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity022.checked 49 (by change 49 < 64; omega)
  · exact boolean_record_at Validity022.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict051.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict051.checked 1 (by change 1 < 16; omega)

theorem pt244_facts : PointFacts pt244 := by
  apply pointFacts_of_quoted_checks pt244 ((2 : Rat)) (((6757437 : Rat) / (1250000 : Rat))) ((2 : Rat)) (((1689359 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity007.checked 30 (by change 30 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e126.y ∧ e126.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 45 (by change 45 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity022.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity022.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict051.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict051.checked 3 (by change 3 < 16; omega)

theorem pt245_facts : PointFacts pt245 := by
  apply pointFacts_of_quoted_checks pt245 ((2 : Rat)) (((32604103 : Rat) / (5000000 : Rat))) ((2 : Rat)) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity007.checked 31 (by change 31 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 46 (by change 46 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity022.checked 53 (by change 53 < 64; omega)
  · exact boolean_record_at Validity022.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict051.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict051.checked 5 (by change 5 < 16; omega)

theorem pt246_facts : PointFacts pt246 := by
  apply pointFacts_of_quoted_checks pt246 ((2 : Rat)) (((629249 : Rat) / (80000 : Rat))) ((2 : Rat)) (((78656091 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 32 (by change 32 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e134.y ∧ e134.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 47 (by change 47 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity022.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity022.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict051.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict051.checked 7 (by change 7 < 16; omega)

theorem pt247_facts : PointFacts pt247 := by
  apply pointFacts_of_quoted_checks pt247 ((2 : Rat)) (((23719357 : Rat) / (2500000 : Rat))) ((2 : Rat)) (((94877357 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 33 (by change 33 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e136.y ∧ e136.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 48 (by change 48 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity022.checked 57 (by change 57 < 64; omega)
  · exact boolean_record_at Validity022.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict051.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict051.checked 9 (by change 9 < 16; omega)

theorem pt248_facts : PointFacts pt248 := by
  apply pointFacts_of_quoted_checks pt248 ((2 : Rat)) (((27609207 : Rat) / (2000000 : Rat))) ((2 : Rat)) (((6902287 : Rat) / (500000 : Rat)))
  · exact boolean_record_at Validity007.checked 34 (by change 34 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e138.y ∧ e138.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 3 (by change 3 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 49 (by change 49 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity022.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity022.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict051.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict051.checked 11 (by change 11 < 16; omega)

theorem pt249_facts : PointFacts pt249 := by
  apply pointFacts_of_quoted_checks pt249 ((2 : Rat)) (((100428229 : Rat) / (5000000 : Rat))) ((2 : Rat)) (((40171073 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity007.checked 35 (by change 35 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e140.y ∧ e140.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 50 (by change 50 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity022.checked 61 (by change 61 < 64; omega)
  · exact boolean_record_at Validity022.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict051.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict051.checked 13 (by change 13 < 16; omega)

theorem pt250_facts : PointFacts pt250 := by
  apply pointFacts_of_quoted_checks pt250 (((7 : Rat) / (3 : Rat))) (((3637479 : Rat) / (2500000 : Rat))) (((7 : Rat) / (3 : Rat))) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 36 (by change 36 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 52 (by change 52 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity023.checked 1 (by change 1 < 64; omega)
  · exact boolean_record_at Validity023.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict052.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict052.checked 1 (by change 1 < 16; omega)

theorem pt251_facts : PointFacts pt251 := by
  apply pointFacts_of_quoted_checks pt251 (((7 : Rat) / (3 : Rat))) (((10585001 : Rat) / (5000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 37 (by change 37 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 54 (by change 54 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity023.checked 5 (by change 5 < 64; omega)
  · exact boolean_record_at Validity023.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict052.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict052.checked 5 (by change 5 < 16; omega)

theorem pt252_facts : PointFacts pt252 := by
  apply pointFacts_of_quoted_checks pt252 (((7 : Rat) / (3 : Rat))) (((3080217 : Rat) / (1000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 38 (by change 38 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 6 (by change 6 < 16; omega))
  · exact comparison_record_at ParentLookupEquality016.checked 4 (by change 4 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 5 (by change 5 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 6 (by change 6 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 7 (by change 7 < 44; omega)
  · exact boolean_record_at Validity023.checked 37 (by change 37 < 64; omega)
  · exact boolean_record_at Validity023.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict054.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict054.checked 5 (by change 5 < 16; omega)

theorem pt253_facts : PointFacts pt253 := by
  apply pointFacts_of_quoted_checks pt253 (((7 : Rat) / (3 : Rat))) (((37154509 : Rat) / (10000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity007.checked 39 (by change 39 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 8 (by change 8 < 16; omega))
  · exact comparison_record_at ParentLookupEquality016.checked 12 (by change 12 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 13 (by change 13 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 14 (by change 14 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 15 (by change 15 < 44; omega)
  · exact boolean_record_at Validity023.checked 41 (by change 41 < 64; omega)
  · exact boolean_record_at Validity023.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict054.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict054.checked 9 (by change 9 < 16; omega)

theorem pt254_facts : PointFacts pt254 := by
  apply pointFacts_of_quoted_checks pt254 (((7 : Rat) / (3 : Rat))) (((22408447 : Rat) / (5000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 40 (by change 40 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 9 (by change 9 < 16; omega))
  · exact comparison_record_at ParentLookupEquality016.checked 16 (by change 16 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 17 (by change 17 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 18 (by change 18 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 19 (by change 19 < 44; omega)
  · exact boolean_record_at Validity023.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity023.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict054.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict054.checked 11 (by change 11 < 16; omega)

theorem pt255_facts : PointFacts pt255 := by
  apply pointFacts_of_quoted_checks pt255 (((7 : Rat) / (3 : Rat))) (((6757437 : Rat) / (1250000 : Rat))) (((7 : Rat) / (3 : Rat))) (((1689359 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity007.checked 41 (by change 41 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e126.y ∧ e126.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 10 (by change 10 < 16; omega))
  · exact comparison_record_at ParentLookupEquality016.checked 20 (by change 20 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 21 (by change 21 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 22 (by change 22 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 23 (by change 23 < 44; omega)
  · exact boolean_record_at Validity023.checked 45 (by change 45 < 64; omega)
  · exact boolean_record_at Validity023.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict054.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict054.checked 13 (by change 13 < 16; omega)

theorem pt256_facts : PointFacts pt256 := by
  apply pointFacts_of_quoted_checks pt256 (((7 : Rat) / (3 : Rat))) (((32604103 : Rat) / (5000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity007.checked 42 (by change 42 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 11 (by change 11 < 16; omega))
  · exact comparison_record_at ParentLookupEquality016.checked 24 (by change 24 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 25 (by change 25 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 26 (by change 26 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 27 (by change 27 < 44; omega)
  · exact boolean_record_at Validity023.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity023.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict054.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict054.checked 15 (by change 15 < 16; omega)

def points : List Point := [pt241, pt242, pt243, pt244, pt245, pt246, pt247, pt248, pt249, pt250, pt251, pt252, pt253, pt254, pt255, pt256]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt241_facts
  · exact pt242_facts
  · exact pt243_facts
  · exact pt244_facts
  · exact pt245_facts
  · exact pt246_facts
  · exact pt247_facts
  · exact pt248_facts
  · exact pt249_facts
  · exact pt250_facts
  · exact pt251_facts
  · exact pt252_facts
  · exact pt253_facts
  · exact pt254_facts
  · exact pt255_facts
  · exact pt256_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup016

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt241_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt241_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt242_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt242_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt243_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt243_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt244_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt244_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt245_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt245_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt246_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt246_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt247_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt247_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt248_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt248_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt249_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt249_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt250_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt250_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt251_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt251_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt252_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt252_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt253_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt253_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt254_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt254_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt255_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt255_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt256_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt256_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.all_points
