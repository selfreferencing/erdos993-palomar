module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.ExactComparisons.F3All.Normalization006
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality012
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality013
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality014
public import Erdos993Lean.ExactComparisons.F3All.Strict047
public import Erdos993Lean.ExactComparisons.F3All.Strict048
public import Erdos993Lean.ExactComparisons.F3All.Strict049
public import Erdos993Lean.ExactComparisons.F3All.Strict050
public import Erdos993Lean.ExactComparisons.F3All.Validity007
public import Erdos993Lean.ExactComparisons.F3All.Validity021
public import Erdos993Lean.ExactComparisons.F3All.Validity022
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025
public import Erdos993Lean.ExactComparisons.F3All.Validity026

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup015

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt225_facts : PointFacts pt225 := by
  apply pointFacts_of_quoted_checks pt225 (((7 : Rat) / (4 : Rat))) (((4387637 : Rat) / (2500000 : Rat))) (((7 : Rat) / (4 : Rat))) (((3510109 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity007.checked 11 (by change 11 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e029.y ∧ e029.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 13 (by change 13 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity021.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity021.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict047.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict047.checked 3 (by change 3 < 16; omega)

theorem pt226_facts : PointFacts pt226 := by
  apply pointFacts_of_quoted_checks pt226 (((7 : Rat) / (4 : Rat))) (((10585001 : Rat) / (5000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 12 (by change 12 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 15 (by change 15 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity021.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity021.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict047.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict047.checked 7 (by change 7 < 16; omega)

theorem pt227_facts : PointFacts pt227 := by
  apply pointFacts_of_quoted_checks pt227 (((7 : Rat) / (4 : Rat))) (((3191987 : Rat) / (1250000 : Rat))) (((7 : Rat) / (4 : Rat))) (((25535893 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 13 (by change 13 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e088.y ∧ e088.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 19 (by change 19 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity021.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity022.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict047.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict047.checked 15 (by change 15 < 16; omega)

theorem pt228_facts : PointFacts pt228 := by
  apply pointFacts_of_quoted_checks pt228 (((7 : Rat) / (4 : Rat))) (((3080217 : Rat) / (1000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 14 (by change 14 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 21 (by change 21 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity022.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity022.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict048.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict048.checked 3 (by change 3 < 16; omega)

theorem pt229_facts : PointFacts pt229 := by
  apply pointFacts_of_quoted_checks pt229 (((7 : Rat) / (4 : Rat))) (((37154509 : Rat) / (10000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity007.checked 15 (by change 15 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 22 (by change 22 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity022.checked 5 (by change 5 < 64; omega)
  · exact boolean_record_at Validity022.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict048.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict048.checked 5 (by change 5 < 16; omega)

theorem pt230_facts : PointFacts pt230 := by
  apply pointFacts_of_quoted_checks pt230 (((7 : Rat) / (4 : Rat))) (((22408447 : Rat) / (5000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 16 (by change 16 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 23 (by change 23 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity022.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity022.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict048.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict048.checked 7 (by change 7 < 16; omega)

theorem pt231_facts : PointFacts pt231 := by
  apply pointFacts_of_quoted_checks pt231 (((7 : Rat) / (4 : Rat))) (((6757437 : Rat) / (1250000 : Rat))) (((7 : Rat) / (4 : Rat))) (((1689359 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity007.checked 17 (by change 17 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e126.y ∧ e126.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 24 (by change 24 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity022.checked 9 (by change 9 < 64; omega)
  · exact boolean_record_at Validity022.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict048.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict048.checked 9 (by change 9 < 16; omega)

theorem pt232_facts : PointFacts pt232 := by
  apply pointFacts_of_quoted_checks pt232 (((7 : Rat) / (4 : Rat))) (((32604103 : Rat) / (5000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity007.checked 18 (by change 18 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 25 (by change 25 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity022.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity022.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict048.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict048.checked 11 (by change 11 < 16; omega)

theorem pt233_facts : PointFacts pt233 := by
  apply pointFacts_of_quoted_checks pt233 (((7 : Rat) / (4 : Rat))) (((629249 : Rat) / (80000 : Rat))) (((7 : Rat) / (4 : Rat))) (((78656091 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 19 (by change 19 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e134.y ∧ e134.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 26 (by change 26 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity022.checked 13 (by change 13 < 64; omega)
  · exact boolean_record_at Validity022.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict048.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict048.checked 13 (by change 13 < 16; omega)

theorem pt234_facts : PointFacts pt234 := by
  apply pointFacts_of_quoted_checks pt234 (((7 : Rat) / (4 : Rat))) (((23719357 : Rat) / (2500000 : Rat))) (((7 : Rat) / (4 : Rat))) (((94877357 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 20 (by change 20 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e136.y ∧ e136.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 27 (by change 27 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity022.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity022.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict048.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict048.checked 15 (by change 15 < 16; omega)

theorem pt235_facts : PointFacts pt235 := by
  apply pointFacts_of_quoted_checks pt235 (((7 : Rat) / (4 : Rat))) (((27609207 : Rat) / (2000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((6902287 : Rat) / (500000 : Rat)))
  · exact boolean_record_at Validity007.checked 21 (by change 21 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e138.y ∧ e138.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 3 (by change 3 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 28 (by change 28 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity022.checked 17 (by change 17 < 64; omega)
  · exact boolean_record_at Validity022.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict049.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict049.checked 1 (by change 1 < 16; omega)

theorem pt236_facts : PointFacts pt236 := by
  apply pointFacts_of_quoted_checks pt236 (((7 : Rat) / (4 : Rat))) (((100428229 : Rat) / (5000000 : Rat))) (((7 : Rat) / (4 : Rat))) (((40171073 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity007.checked 22 (by change 22 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e140.y ∧ e140.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 29 (by change 29 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity022.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity022.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict049.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict049.checked 3 (by change 3 < 16; omega)

theorem pt237_facts : PointFacts pt237 := by
  apply pointFacts_of_quoted_checks pt237 ((2 : Rat)) (((3637479 : Rat) / (2500000 : Rat))) ((2 : Rat)) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 23 (by change 23 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 30 (by change 30 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity022.checked 21 (by change 21 < 64; omega)
  · exact boolean_record_at Validity022.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict049.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict049.checked 5 (by change 5 < 16; omega)

theorem pt238_facts : PointFacts pt238 := by
  apply pointFacts_of_quoted_checks pt238 ((2 : Rat)) (((4387637 : Rat) / (2500000 : Rat))) ((2 : Rat)) (((3510109 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity007.checked 24 (by change 24 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e029.y ∧ e029.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 32 (by change 32 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity022.checked 25 (by change 25 < 64; omega)
  · exact boolean_record_at Validity022.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict049.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict049.checked 9 (by change 9 < 16; omega)

theorem pt239_facts : PointFacts pt239 := by
  apply pointFacts_of_quoted_checks pt239 ((2 : Rat)) (((10585001 : Rat) / (5000000 : Rat))) ((2 : Rat)) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 25 (by change 25 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 34 (by change 34 < 64; omega))
  · exact comparison_record_at ParentLookupEquality013.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality013.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity022.checked 29 (by change 29 < 64; omega)
  · exact boolean_record_at Validity022.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict049.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict049.checked 13 (by change 13 < 16; omega)

theorem pt240_facts : PointFacts pt240 := by
  apply pointFacts_of_quoted_checks pt240 ((2 : Rat)) (((3191987 : Rat) / (1250000 : Rat))) ((2 : Rat)) (((25535893 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 26 (by change 26 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
  · exact (show 0 ≤ e088.y ∧ e088.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 39 (by change 39 < 64; omega))
  · exact comparison_record_at ParentLookupEquality014.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality014.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity022.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity022.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict050.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict050.checked 7 (by change 7 < 16; omega)

def points : List Point := [pt225, pt226, pt227, pt228, pt229, pt230, pt231, pt232, pt233, pt234, pt235, pt236, pt237, pt238, pt239, pt240]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt225_facts
  · exact pt226_facts
  · exact pt227_facts
  · exact pt228_facts
  · exact pt229_facts
  · exact pt230_facts
  · exact pt231_facts
  · exact pt232_facts
  · exact pt233_facts
  · exact pt234_facts
  · exact pt235_facts
  · exact pt236_facts
  · exact pt237_facts
  · exact pt238_facts
  · exact pt239_facts
  · exact pt240_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup015

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt225_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt225_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt226_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt226_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt227_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt227_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt228_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt228_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt229_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt229_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt230_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt230_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt231_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt231_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt232_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt232_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt233_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt233_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt234_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt234_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt235_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt235_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt236_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt236_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt237_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt237_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt238_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt238_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt239_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt239_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt240_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt240_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.all_points
