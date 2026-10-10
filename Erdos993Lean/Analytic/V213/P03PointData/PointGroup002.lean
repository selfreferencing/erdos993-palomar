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
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.ExactComparisons.F3All.Normalization006
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality012
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality013
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality014
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality015
public import Erdos993Lean.ExactComparisons.F3All.Strict047
public import Erdos993Lean.ExactComparisons.F3All.Strict048
public import Erdos993Lean.ExactComparisons.F3All.Strict049
public import Erdos993Lean.ExactComparisons.F3All.Strict050
public import Erdos993Lean.ExactComparisons.F3All.Strict051
public import Erdos993Lean.ExactComparisons.F3All.Strict052
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity004
public import Erdos993Lean.ExactComparisons.F3All.Validity021
public import Erdos993Lean.ExactComparisons.F3All.Validity022
public import Erdos993Lean.ExactComparisons.F3All.Validity023
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup002

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt017_facts : PointFacts pt017 := by
  apply pointFacts_of_quoted_checks pt017 (((7 : Rat) / (4 : Rat))) (((4297989 : Rat) / (2000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((10744971 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity003.checked 59 (by change 59 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e056.y ∧ e056.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e056_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 16 (by change 16 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity021.checked 57 (by change 57 < 64; omega)
  · exact boolean_record_at Validity021.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict047.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict047.checked 9 (by change 9 < 16; omega)

theorem pt018_facts : PointFacts pt018 := by
  apply pointFacts_of_quoted_checks pt018 (((7 : Rat) / (4 : Rat))) (((1145227 : Rat) / (500000 : Rat))) (((7 : Rat) / (4 : Rat))) (((22904537 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity003.checked 60 (by change 60 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e067.y ∧ e067.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 60 (by change 60 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e067_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 17 (by change 17 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity021.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity021.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict047.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict047.checked 11 (by change 11 < 16; omega)

theorem pt019_facts : PointFacts pt019 := by
  apply pointFacts_of_quoted_checks pt019 (((7 : Rat) / (4 : Rat))) (((6103063 : Rat) / (2500000 : Rat))) (((7 : Rat) / (4 : Rat))) (((24412249 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity003.checked 61 (by change 61 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e082.y ∧ e082.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 11 (by change 11 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e082_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 18 (by change 18 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity021.checked 61 (by change 61 < 64; omega)
  · exact boolean_record_at Validity021.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict047.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict047.checked 13 (by change 13 < 16; omega)

theorem pt020_facts : PointFacts pt020 := by
  apply pointFacts_of_quoted_checks pt020 (((7 : Rat) / (4 : Rat))) (((27731949 : Rat) / (10000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((13865973 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity003.checked 62 (by change 62 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e095.y ∧ e095.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 24 (by change 24 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e095_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 20 (by change 20 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity022.checked 1 (by change 1 < 64; omega)
  · exact boolean_record_at Validity022.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict048.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict048.checked 1 (by change 1 < 16; omega)

theorem pt021_facts : PointFacts pt021 := by
  have hz : pt021 = zeroPoint b08 := by
    norm_num [pt021, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b08
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds

theorem pt022_facts : PointFacts pt022 := by
  apply pointFacts_of_quoted_checks pt022 ((2 : Rat)) (((4333133 : Rat) / (2500000 : Rat))) ((2 : Rat)) (((17332529 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 0 (by change 0 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e027.y ∧ e027.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 20 (by change 20 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e027_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 31 (by change 31 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity022.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity022.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict049.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict049.checked 7 (by change 7 < 16; omega)

theorem pt023_facts : PointFacts pt023 := by
  apply pointFacts_of_quoted_checks pt023 ((2 : Rat)) (((1242961 : Rat) / (625000 : Rat))) ((2 : Rat)) (((19887373 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 1 (by change 1 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e044.y ∧ e044.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 37 (by change 37 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e044_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 33 (by change 33 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity022.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity022.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict049.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict049.checked 11 (by change 11 < 16; omega)

theorem pt024_facts : PointFacts pt024 := by
  apply pointFacts_of_quoted_checks pt024 ((2 : Rat)) (((21302729 : Rat) / (10000000 : Rat))) ((2 : Rat)) (((10651363 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 2 (by change 2 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e054.y ∧ e054.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 47 (by change 47 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e054_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 35 (by change 35 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity022.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity022.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict049.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict049.checked 15 (by change 15 < 16; omega)

theorem pt025_facts : PointFacts pt025 := by
  apply pointFacts_of_quoted_checks pt025 ((2 : Rat)) (((22818809 : Rat) / (10000000 : Rat))) ((2 : Rat)) (((11409403 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 3 (by change 3 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e066.y ∧ e066.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e066_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 36 (by change 36 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity022.checked 33 (by change 33 < 64; omega)
  · exact boolean_record_at Validity022.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict050.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict050.checked 1 (by change 1 < 16; omega)

theorem pt026_facts : PointFacts pt026 := by
  apply pointFacts_of_quoted_checks pt026 ((2 : Rat)) (((23616843 : Rat) / (10000000 : Rat))) ((2 : Rat)) (((590421 : Rat) / (250000 : Rat)))
  · exact boolean_record_at Validity004.checked 4 (by change 4 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e074.y ∧ e074.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 3 (by change 3 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e074_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 37 (by change 37 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity022.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity022.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict050.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict050.checked 3 (by change 3 < 16; omega)

theorem pt027_facts : PointFacts pt027 := by
  apply pointFacts_of_quoted_checks pt027 ((2 : Rat)) (((24442787 : Rat) / (10000000 : Rat))) ((2 : Rat)) (((763837 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity004.checked 5 (by change 5 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e083.y ∧ e083.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 12 (by change 12 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e083_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 38 (by change 38 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity022.checked 37 (by change 37 < 64; omega)
  · exact boolean_record_at Validity022.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict050.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict050.checked 5 (by change 5 < 16; omega)

theorem pt028_facts : PointFacts pt028 := by
  apply pointFacts_of_quoted_checks pt028 ((2 : Rat)) (((1309117 : Rat) / (500000 : Rat))) ((2 : Rat)) (((26182337 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 6 (by change 6 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e091.y ∧ e091.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 20 (by change 20 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e091_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 40 (by change 40 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity022.checked 41 (by change 41 < 64; omega)
  · exact boolean_record_at Validity022.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict050.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict050.checked 9 (by change 9 < 16; omega)

theorem pt029_facts : PointFacts pt029 := by
  apply pointFacts_of_quoted_checks pt029 ((2 : Rat)) (((15020831 : Rat) / (5000000 : Rat))) ((2 : Rat)) (((30041659 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 7 (by change 7 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e101.y ∧ e101.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 30 (by change 30 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e101_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 41 (by change 41 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity022.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity022.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict050.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict050.checked 11 (by change 11 < 16; omega)

theorem pt030_facts : PointFacts pt030 := by
  have hz : pt030 = zeroPoint b09 := by
    norm_num [pt030, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b09
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds

theorem pt031_facts : PointFacts pt031 := by
  apply pointFacts_of_quoted_checks pt031 (((7 : Rat) / (3 : Rat))) (((6766189 : Rat) / (5000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((108259 : Rat) / (80000 : Rat)))
  · exact boolean_record_at Validity004.checked 9 (by change 9 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e009.y ∧ e009.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 2 (by change 2 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e009_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 51 (by change 51 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity022.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity023.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict051.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict051.checked 15 (by change 15 < 16; omega)

theorem pt032_facts : PointFacts pt032 := by
  apply pointFacts_of_quoted_checks pt032 (((7 : Rat) / (3 : Rat))) (((4578131 : Rat) / (2500000 : Rat))) (((7 : Rat) / (3 : Rat))) (((18312521 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 10 (by change 10 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e033.y ∧ e033.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 26 (by change 26 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e033_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 53 (by change 53 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity023.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity023.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict052.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict052.checked 3 (by change 3 < 16; omega)

def points : List Point := [pt017, pt018, pt019, pt020, pt021, pt022, pt023, pt024, pt025, pt026, pt027, pt028, pt029, pt030, pt031, pt032]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt017_facts
  · exact pt018_facts
  · exact pt019_facts
  · exact pt020_facts
  · exact pt021_facts
  · exact pt022_facts
  · exact pt023_facts
  · exact pt024_facts
  · exact pt025_facts
  · exact pt026_facts
  · exact pt027_facts
  · exact pt028_facts
  · exact pt029_facts
  · exact pt030_facts
  · exact pt031_facts
  · exact pt032_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup002

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt017_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt017_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt018_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt018_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt019_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt019_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt020_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt020_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt021_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt021_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt022_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt022_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt023_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt023_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt024_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt024_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt025_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt025_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt026_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt026_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt027_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt027_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt028_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt028_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt029_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt029_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt030_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt030_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt031_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt031_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt032_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt032_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.all_points
