module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.ExactComparisons.F3All.Normalization004
public import Erdos993Lean.ExactComparisons.F3All.Normalization005
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality005
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality008
public import Erdos993Lean.ExactComparisons.F3All.Strict032
public import Erdos993Lean.ExactComparisons.F3All.Strict033
public import Erdos993Lean.ExactComparisons.F3All.Strict038
public import Erdos993Lean.ExactComparisons.F3All.Strict039
public import Erdos993Lean.ExactComparisons.F3All.Validity005
public import Erdos993Lean.ExactComparisons.F3All.Validity006
public import Erdos993Lean.ExactComparisons.F3All.Validity018
public import Erdos993Lean.ExactComparisons.F3All.Validity019
public import Erdos993Lean.ExactComparisons.F3All.Validity024

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup010

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt145_facts : PointFacts pt145 := by
  apply pointFacts_of_quoted_checks pt145 (((263 : Rat) / (200 : Rat))) (((3994989 : Rat) / (2500000 : Rat))) (((263 : Rat) / (200 : Rat))) (((15979953 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 59 (by change 59 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e019.y ∧ e019.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 12 (by change 12 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 5 (by change 5 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity019.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity019.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict038.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict038.checked 3 (by change 3 < 16; omega)

theorem pt146_facts : PointFacts pt146 := by
  apply pointFacts_of_quoted_checks pt146 (((28 : Rat) / (25 : Rat))) (((1635891 : Rat) / (1000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((16358907 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 60 (by change 60 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e021.y ∧ e021.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 14 (by change 14 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e021_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 25 (by change 25 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity018.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity018.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict032.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict032.checked 11 (by change 11 < 16; omega)

theorem pt147_facts : PointFacts pt147 := by
  apply pointFacts_of_quoted_checks pt147 (((263 : Rat) / (200 : Rat))) (((1635891 : Rat) / (1000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((16358907 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 61 (by change 61 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e021.y ∧ e021.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 14 (by change 14 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e021_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 6 (by change 6 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity019.checked 37 (by change 37 < 64; omega)
  · exact boolean_record_at Validity019.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict038.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict038.checked 5 (by change 5 < 16; omega)

theorem pt148_facts : PointFacts pt148 := by
  apply pointFacts_of_quoted_checks pt148 (((263 : Rat) / (200 : Rat))) (((334937 : Rat) / (200000 : Rat))) (((263 : Rat) / (200 : Rat))) (((16746847 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 62 (by change 62 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e024.y ∧ e024.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e024_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 7 (by change 7 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity019.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity019.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict038.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict038.checked 7 (by change 7 < 16; omega)

theorem pt149_facts : PointFacts pt149 := by
  apply pointFacts_of_quoted_checks pt149 (((28 : Rat) / (25 : Rat))) (((1714399 : Rat) / (1000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((17143987 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 63 (by change 63 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e026.y ∧ e026.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 19 (by change 19 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e026_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 27 (by change 27 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity018.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity018.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict032.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict032.checked 15 (by change 15 < 16; omega)

theorem pt150_facts : PointFacts pt150 := by
  apply pointFacts_of_quoted_checks pt150 (((263 : Rat) / (200 : Rat))) (((1714399 : Rat) / (1000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((17143987 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 0 (by change 0 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e026.y ∧ e026.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 19 (by change 19 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e026_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 8 (by change 8 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity019.checked 41 (by change 41 < 64; omega)
  · exact boolean_record_at Validity019.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict038.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict038.checked 9 (by change 9 < 16; omega)

theorem pt151_facts : PointFacts pt151 := by
  apply pointFacts_of_quoted_checks pt151 (((263 : Rat) / (200 : Rat))) (((4387637 : Rat) / (2500000 : Rat))) (((263 : Rat) / (200 : Rat))) (((3510109 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity006.checked 1 (by change 1 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e029.y ∧ e029.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 9 (by change 9 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity019.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity019.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict038.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict038.checked 11 (by change 11 < 16; omega)

theorem pt152_facts : PointFacts pt152 := by
  apply pointFacts_of_quoted_checks pt152 (((28 : Rat) / (25 : Rat))) (((17966747 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((2245843 : Rat) / (1250000 : Rat)))
  · exact boolean_record_at Validity006.checked 2 (by change 2 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e031.y ∧ e031.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 24 (by change 24 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e031_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 29 (by change 29 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity018.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity018.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict033.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict033.checked 3 (by change 3 < 16; omega)

theorem pt153_facts : PointFacts pt153 := by
  apply pointFacts_of_quoted_checks pt153 (((263 : Rat) / (200 : Rat))) (((17966747 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((2245843 : Rat) / (1250000 : Rat)))
  · exact boolean_record_at Validity006.checked 3 (by change 3 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e031.y ∧ e031.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 24 (by change 24 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e031_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 10 (by change 10 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity019.checked 45 (by change 45 < 64; omega)
  · exact boolean_record_at Validity019.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict038.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict038.checked 13 (by change 13 < 16; omega)

theorem pt154_facts : PointFacts pt154 := by
  apply pointFacts_of_quoted_checks pt154 (((263 : Rat) / (200 : Rat))) (((1149551 : Rat) / (625000 : Rat))) (((263 : Rat) / (200 : Rat))) (((18392813 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 4 (by change 4 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e034.y ∧ e034.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 27 (by change 27 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e034_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 11 (by change 11 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity019.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity019.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict038.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict038.checked 15 (by change 15 < 16; omega)

theorem pt155_facts : PointFacts pt155 := by
  apply pointFacts_of_quoted_checks pt155 (((28 : Rat) / (25 : Rat))) (((18828989 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((9414493 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 5 (by change 5 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e037.y ∧ e037.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 30 (by change 30 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e037_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 31 (by change 31 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity018.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity018.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict033.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict033.checked 7 (by change 7 < 16; omega)

theorem pt156_facts : PointFacts pt156 := by
  apply pointFacts_of_quoted_checks pt156 (((263 : Rat) / (200 : Rat))) (((18828989 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((9414493 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 6 (by change 6 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e037.y ∧ e037.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 30 (by change 30 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e037_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 13 (by change 13 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity019.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity019.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict039.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict039.checked 3 (by change 3 < 16; omega)

theorem pt157_facts : PointFacts pt157 := by
  apply pointFacts_of_quoted_checks pt157 (((263 : Rat) / (200 : Rat))) (((9637753 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((19275503 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 7 (by change 7 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e040.y ∧ e040.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 33 (by change 33 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 14 (by change 14 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity019.checked 53 (by change 53 < 64; omega)
  · exact boolean_record_at Validity019.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict039.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict039.checked 5 (by change 5 < 16; omega)

theorem pt158_facts : PointFacts pt158 := by
  apply pointFacts_of_quoted_checks pt158 (((28 : Rat) / (25 : Rat))) (((19732611 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((154161 : Rat) / (78125 : Rat)))
  · exact boolean_record_at Validity006.checked 8 (by change 8 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e042.y ∧ e042.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 35 (by change 35 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e042_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 33 (by change 33 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity018.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity018.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict033.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict033.checked 11 (by change 11 < 16; omega)

theorem pt159_facts : PointFacts pt159 := by
  apply pointFacts_of_quoted_checks pt159 (((263 : Rat) / (200 : Rat))) (((19732611 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((154161 : Rat) / (78125 : Rat)))
  · exact boolean_record_at Validity006.checked 9 (by change 9 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e042.y ∧ e042.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 35 (by change 35 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e042_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 15 (by change 15 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity019.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity019.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict039.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict039.checked 7 (by change 7 < 16; omega)

theorem pt160_facts : PointFacts pt160 := by
  apply pointFacts_of_quoted_checks pt160 (((263 : Rat) / (200 : Rat))) (((20200557 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((10100277 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 10 (by change 10 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e047.y ∧ e047.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 40 (by change 40 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e047_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 17 (by change 17 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity019.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity019.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict039.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict039.checked 11 (by change 11 < 16; omega)

def points : List Point := [pt145, pt146, pt147, pt148, pt149, pt150, pt151, pt152, pt153, pt154, pt155, pt156, pt157, pt158, pt159, pt160]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt145_facts
  · exact pt146_facts
  · exact pt147_facts
  · exact pt148_facts
  · exact pt149_facts
  · exact pt150_facts
  · exact pt151_facts
  · exact pt152_facts
  · exact pt153_facts
  · exact pt154_facts
  · exact pt155_facts
  · exact pt156_facts
  · exact pt157_facts
  · exact pt158_facts
  · exact pt159_facts
  · exact pt160_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup010

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt145_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt145_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt146_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt146_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt147_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt147_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt148_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt148_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt149_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt149_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt150_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt150_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt151_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt151_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt152_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt152_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt153_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt153_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt154_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt154_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt155_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt155_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt156_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt156_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt157_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt157_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt158_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt158_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt159_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt159_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt160_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt160_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.all_points
