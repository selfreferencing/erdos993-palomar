module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.ExactComparisons.F3All.Normalization004
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality003
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality004
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality005
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality006
public import Erdos993Lean.ExactComparisons.F3All.Strict029
public import Erdos993Lean.ExactComparisons.F3All.Strict030
public import Erdos993Lean.ExactComparisons.F3All.Strict033
public import Erdos993Lean.ExactComparisons.F3All.Strict034
public import Erdos993Lean.ExactComparisons.F3All.Strict035
public import Erdos993Lean.ExactComparisons.F3All.Validity005
public import Erdos993Lean.ExactComparisons.F3All.Validity017
public import Erdos993Lean.ExactComparisons.F3All.Validity018
public import Erdos993Lean.ExactComparisons.F3All.Validity019
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup008

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt113_facts : PointFacts pt113 := by
  apply pointFacts_of_quoted_checks pt113 (((7 : Rat) / (8 : Rat))) (((1149551 : Rat) / (625000 : Rat))) (((7 : Rat) / (8 : Rat))) (((18392813 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 27 (by change 27 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e034.y ∧ e034.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 27 (by change 27 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e034_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 0 (by change 0 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity017.checked 25 (by change 25 < 64; omega)
  · exact boolean_record_at Validity017.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict029.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict029.checked 9 (by change 9 < 16; omega)

theorem pt114_facts : PointFacts pt114 := by
  apply pointFacts_of_quoted_checks pt114 (((28 : Rat) / (25 : Rat))) (((1149551 : Rat) / (625000 : Rat))) (((28 : Rat) / (25 : Rat))) (((18392813 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 28 (by change 28 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e034.y ∧ e034.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 27 (by change 27 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e034_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 30 (by change 30 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity018.checked 21 (by change 21 < 64; omega)
  · exact boolean_record_at Validity018.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict033.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict033.checked 5 (by change 5 < 16; omega)

theorem pt115_facts : PointFacts pt115 := by
  apply pointFacts_of_quoted_checks pt115 (((28 : Rat) / (25 : Rat))) (((9637753 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((19275503 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 29 (by change 29 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e040.y ∧ e040.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 33 (by change 33 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 32 (by change 32 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity018.checked 25 (by change 25 < 64; omega)
  · exact boolean_record_at Validity018.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict033.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict033.checked 9 (by change 9 < 16; omega)

theorem pt116_facts : PointFacts pt116 := by
  apply pointFacts_of_quoted_checks pt116 (((7 : Rat) / (8 : Rat))) (((20200557 : Rat) / (10000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((10100277 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 30 (by change 30 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e047.y ∧ e047.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 40 (by change 40 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e047_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 2 (by change 2 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity017.checked 29 (by change 29 < 64; omega)
  · exact boolean_record_at Validity017.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict029.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict029.checked 13 (by change 13 < 16; omega)

theorem pt117_facts : PointFacts pt117 := by
  apply pointFacts_of_quoted_checks pt117 (((28 : Rat) / (25 : Rat))) (((20200557 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((10100277 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 31 (by change 31 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e047.y ∧ e047.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 40 (by change 40 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e047_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 34 (by change 34 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity018.checked 29 (by change 29 < 64; omega)
  · exact boolean_record_at Validity018.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict033.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict033.checked 13 (by change 13 < 16; omega)

theorem pt118_facts : PointFacts pt118 := by
  apply pointFacts_of_quoted_checks pt118 (((28 : Rat) / (25 : Rat))) (((10585001 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 32 (by change 32 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 36 (by change 36 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity018.checked 33 (by change 33 < 64; omega)
  · exact boolean_record_at Validity018.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict034.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict034.checked 1 (by change 1 < 16; omega)

theorem pt119_facts : PointFacts pt119 := by
  apply pointFacts_of_quoted_checks pt119 (((7 : Rat) / (8 : Rat))) (((22185971 : Rat) / (10000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((1386623 : Rat) / (625000 : Rat)))
  · exact boolean_record_at Validity005.checked 33 (by change 33 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e061.y ∧ e061.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 54 (by change 54 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e061_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 4 (by change 4 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity017.checked 33 (by change 33 < 64; omega)
  · exact boolean_record_at Validity017.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict030.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict030.checked 1 (by change 1 < 16; omega)

theorem pt120_facts : PointFacts pt120 := by
  apply pointFacts_of_quoted_checks pt120 (((28 : Rat) / (25 : Rat))) (((22185971 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((1386623 : Rat) / (625000 : Rat)))
  · exact boolean_record_at Validity005.checked 34 (by change 34 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e061.y ∧ e061.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 54 (by change 54 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e061_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 38 (by change 38 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity018.checked 37 (by change 37 < 64; omega)
  · exact boolean_record_at Validity018.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict034.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict034.checked 5 (by change 5 < 16; omega)

theorem pt121_facts : PointFacts pt121 := by
  apply pointFacts_of_quoted_checks pt121 (((28 : Rat) / (25 : Rat))) (((11625349 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((4650139 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity005.checked 35 (by change 35 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e071.y ∧ e071.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 0 (by change 0 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 40 (by change 40 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity018.checked 41 (by change 41 < 64; omega)
  · exact boolean_record_at Validity018.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict034.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict034.checked 9 (by change 9 < 16; omega)

theorem pt122_facts : PointFacts pt122 := by
  apply pointFacts_of_quoted_checks pt122 (((28 : Rat) / (25 : Rat))) (((3191987 : Rat) / (1250000 : Rat))) (((28 : Rat) / (25 : Rat))) (((25535893 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 36 (by change 36 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e088.y ∧ e088.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 43 (by change 43 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity018.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity018.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict034.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict034.checked 15 (by change 15 < 16; omega)

theorem pt123_facts : PointFacts pt123 := by
  apply pointFacts_of_quoted_checks pt123 (((7 : Rat) / (8 : Rat))) (((5609139 : Rat) / (2000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((7011423 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity005.checked 37 (by change 37 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e097.y ∧ e097.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 26 (by change 26 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 7 (by change 7 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity017.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity017.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict030.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict030.checked 7 (by change 7 < 16; omega)

theorem pt124_facts : PointFacts pt124 := by
  apply pointFacts_of_quoted_checks pt124 (((28 : Rat) / (25 : Rat))) (((5609139 : Rat) / (2000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((7011423 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity005.checked 38 (by change 38 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e097.y ∧ e097.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 26 (by change 26 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 45 (by change 45 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity018.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity018.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict035.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict035.checked 3 (by change 3 < 16; omega)

theorem pt125_facts : PointFacts pt125 := by
  apply pointFacts_of_quoted_checks pt125 (((28 : Rat) / (25 : Rat))) (((3080217 : Rat) / (1000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 39 (by change 39 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 47 (by change 47 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity018.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity018.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict035.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict035.checked 7 (by change 7 < 16; omega)

theorem pt126_facts : PointFacts pt126 := by
  apply pointFacts_of_quoted_checks pt126 (((7 : Rat) / (8 : Rat))) (((16914783 : Rat) / (5000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((16914781 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 40 (by change 40 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e108.y ∧ e108.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 37 (by change 37 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 9 (by change 9 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity017.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity017.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict030.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict030.checked 11 (by change 11 < 16; omega)

theorem pt127_facts : PointFacts pt127 := by
  apply pointFacts_of_quoted_checks pt127 (((28 : Rat) / (25 : Rat))) (((16914783 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((16914781 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 41 (by change 41 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e108.y ∧ e108.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 37 (by change 37 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 49 (by change 49 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity018.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity018.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict035.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict035.checked 11 (by change 11 < 16; omega)

theorem pt128_facts : PointFacts pt128 := by
  apply pointFacts_of_quoted_checks pt128 (((28 : Rat) / (25 : Rat))) (((37154509 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 42 (by change 42 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 51 (by change 51 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity018.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity019.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict035.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict035.checked 15 (by change 15 < 16; omega)

def points : List Point := [pt113, pt114, pt115, pt116, pt117, pt118, pt119, pt120, pt121, pt122, pt123, pt124, pt125, pt126, pt127, pt128]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt113_facts
  · exact pt114_facts
  · exact pt115_facts
  · exact pt116_facts
  · exact pt117_facts
  · exact pt118_facts
  · exact pt119_facts
  · exact pt120_facts
  · exact pt121_facts
  · exact pt122_facts
  · exact pt123_facts
  · exact pt124_facts
  · exact pt125_facts
  · exact pt126_facts
  · exact pt127_facts
  · exact pt128_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup008

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt113_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt113_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt114_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt114_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt115_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt115_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt116_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt116_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt117_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt117_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt118_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt118_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt119_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt119_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt120_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt120_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt121_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt121_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt122_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt122_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt123_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt123_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt124_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt124_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt125_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt125_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt126_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt126_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt127_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt127_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt128_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt128_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.all_points
