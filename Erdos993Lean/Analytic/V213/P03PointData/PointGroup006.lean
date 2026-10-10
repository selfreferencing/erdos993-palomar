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
public import Erdos993Lean.ExactComparisons.F3All.Normalization003
public import Erdos993Lean.ExactComparisons.F3All.Normalization004
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality002
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality003
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality004
public import Erdos993Lean.ExactComparisons.F3All.Strict026
public import Erdos993Lean.ExactComparisons.F3All.Strict027
public import Erdos993Lean.ExactComparisons.F3All.Strict028
public import Erdos993Lean.ExactComparisons.F3All.Strict029
public import Erdos993Lean.ExactComparisons.F3All.Strict030
public import Erdos993Lean.ExactComparisons.F3All.Validity004
public import Erdos993Lean.ExactComparisons.F3All.Validity005
public import Erdos993Lean.ExactComparisons.F3All.Validity016
public import Erdos993Lean.ExactComparisons.F3All.Validity017
public import Erdos993Lean.ExactComparisons.F3All.Validity023
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup006

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt081_facts : PointFacts pt081 := by
  apply pointFacts_of_quoted_checks pt081 (((7 : Rat) / (8 : Rat))) (((376947 : Rat) / (312500 : Rat))) (((7 : Rat) / (8 : Rat))) (((12062301 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 59 (by change 59 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e004.y ∧ e004.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity023.checked 61 (by change 61 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 56 (by change 56 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity017.checked 9 (by change 9 < 64; omega)
  · exact boolean_record_at Validity017.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict028.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict028.checked 9 (by change 9 < 16; omega)

theorem pt082_facts : PointFacts pt082 := by
  apply pointFacts_of_quoted_checks pt082 (((7 : Rat) / (8 : Rat))) (((13247849 : Rat) / (10000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((6623923 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 60 (by change 60 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e008.y ∧ e008.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e008_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 57 (by change 57 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity017.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity017.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict028.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict028.checked 11 (by change 11 < 16; omega)

theorem pt083_facts : PointFacts pt083 := by
  apply pointFacts_of_quoted_checks pt083 (((3 : Rat) / (5 : Rat))) (((13883627 : Rat) / (10000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((1735453 : Rat) / (1250000 : Rat)))
  · exact boolean_record_at Validity004.checked 61 (by change 61 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e011.y ∧ e011.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 4 (by change 4 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e011_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 40 (by change 40 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity016.checked 41 (by change 41 < 64; omega)
  · exact boolean_record_at Validity016.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict026.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict026.checked 9 (by change 9 < 16; omega)

theorem pt084_facts : PointFacts pt084 := by
  apply pointFacts_of_quoted_checks pt084 (((7 : Rat) / (8 : Rat))) (((13883627 : Rat) / (10000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((1735453 : Rat) / (1250000 : Rat)))
  · exact boolean_record_at Validity004.checked 62 (by change 62 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e011.y ∧ e011.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 4 (by change 4 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e011_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 58 (by change 58 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity017.checked 13 (by change 13 < 64; omega)
  · exact boolean_record_at Validity017.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict028.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict028.checked 13 (by change 13 < 16; omega)

theorem pt085_facts : PointFacts pt085 := by
  apply pointFacts_of_quoted_checks pt085 (((7 : Rat) / (8 : Rat))) (((3637479 : Rat) / (2500000 : Rat))) (((7 : Rat) / (8 : Rat))) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 63 (by change 63 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 59 (by change 59 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity017.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity017.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict028.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict028.checked 15 (by change 15 < 16; omega)

theorem pt086_facts : PointFacts pt086 := by
  apply pointFacts_of_quoted_checks pt086 (((3 : Rat) / (5 : Rat))) (((15248181 : Rat) / (10000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((7624089 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 0 (by change 0 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e016.y ∧ e016.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 9 (by change 9 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e016_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 42 (by change 42 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity016.checked 45 (by change 45 < 64; omega)
  · exact boolean_record_at Validity016.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict026.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict026.checked 13 (by change 13 < 16; omega)

theorem pt087_facts : PointFacts pt087 := by
  apply pointFacts_of_quoted_checks pt087 (((7 : Rat) / (8 : Rat))) (((15248181 : Rat) / (10000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((7624089 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 1 (by change 1 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e016.y ∧ e016.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 9 (by change 9 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e016_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 60 (by change 60 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity017.checked 17 (by change 17 < 64; omega)
  · exact boolean_record_at Validity017.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict029.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict029.checked 1 (by change 1 < 16; omega)

theorem pt088_facts : PointFacts pt088 := by
  apply pointFacts_of_quoted_checks pt088 (((7 : Rat) / (8 : Rat))) (((3994989 : Rat) / (2500000 : Rat))) (((7 : Rat) / (8 : Rat))) (((15979953 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 2 (by change 2 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e019.y ∧ e019.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 12 (by change 12 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 61 (by change 61 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity017.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity017.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict029.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict029.checked 3 (by change 3 < 16; omega)

theorem pt089_facts : PointFacts pt089 := by
  apply pointFacts_of_quoted_checks pt089 (((7 : Rat) / (8 : Rat))) (((4387637 : Rat) / (2500000 : Rat))) (((7 : Rat) / (8 : Rat))) (((3510109 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity005.checked 3 (by change 3 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e029.y ∧ e029.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 63 (by change 63 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity017.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity017.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict029.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict029.checked 7 (by change 7 < 16; omega)

theorem pt090_facts : PointFacts pt090 := by
  apply pointFacts_of_quoted_checks pt090 (((3 : Rat) / (5 : Rat))) (((9637753 : Rat) / (5000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((19275503 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 4 (by change 4 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e040.y ∧ e040.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 33 (by change 33 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 45 (by change 45 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity016.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity016.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict027.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict027.checked 3 (by change 3 < 16; omega)

theorem pt091_facts : PointFacts pt091 := by
  apply pointFacts_of_quoted_checks pt091 (((7 : Rat) / (8 : Rat))) (((9637753 : Rat) / (5000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((19275503 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 5 (by change 5 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e040.y ∧ e040.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 33 (by change 33 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 1 (by change 1 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity017.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity017.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict029.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict029.checked 11 (by change 11 < 16; omega)

theorem pt092_facts : PointFacts pt092 := by
  apply pointFacts_of_quoted_checks pt092 (((7 : Rat) / (8 : Rat))) (((10585001 : Rat) / (5000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 6 (by change 6 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 3 (by change 3 < 64; omega))
  · exact comparison_record_at ParentLookupEquality003.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality003.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity017.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity017.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict029.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict029.checked 15 (by change 15 < 16; omega)

theorem pt093_facts : PointFacts pt093 := by
  apply pointFacts_of_quoted_checks pt093 (((3 : Rat) / (5 : Rat))) (((11625349 : Rat) / (5000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((4650139 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity005.checked 7 (by change 7 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e071.y ∧ e071.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 0 (by change 0 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 47 (by change 47 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity016.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity016.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict027.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict027.checked 7 (by change 7 < 16; omega)

theorem pt094_facts : PointFacts pt094 := by
  apply pointFacts_of_quoted_checks pt094 (((7 : Rat) / (8 : Rat))) (((11625349 : Rat) / (5000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((4650139 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity005.checked 8 (by change 8 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e071.y ∧ e071.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 0 (by change 0 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 5 (by change 5 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity017.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity017.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict030.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict030.checked 3 (by change 3 < 16; omega)

theorem pt095_facts : PointFacts pt095 := by
  apply pointFacts_of_quoted_checks pt095 (((7 : Rat) / (8 : Rat))) (((3191987 : Rat) / (1250000 : Rat))) (((7 : Rat) / (8 : Rat))) (((25535893 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 9 (by change 9 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e088.y ∧ e088.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 6 (by change 6 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity017.checked 37 (by change 37 < 64; omega)
  · exact boolean_record_at Validity017.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict030.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict030.checked 5 (by change 5 < 16; omega)

theorem pt096_facts : PointFacts pt096 := by
  apply pointFacts_of_quoted_checks pt096 (((7 : Rat) / (8 : Rat))) (((3080217 : Rat) / (1000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 10 (by change 10 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 8 (by change 8 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity017.checked 41 (by change 41 < 64; omega)
  · exact boolean_record_at Validity017.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict030.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict030.checked 9 (by change 9 < 16; omega)

def points : List Point := [pt081, pt082, pt083, pt084, pt085, pt086, pt087, pt088, pt089, pt090, pt091, pt092, pt093, pt094, pt095, pt096]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt081_facts
  · exact pt082_facts
  · exact pt083_facts
  · exact pt084_facts
  · exact pt085_facts
  · exact pt086_facts
  · exact pt087_facts
  · exact pt088_facts
  · exact pt089_facts
  · exact pt090_facts
  · exact pt091_facts
  · exact pt092_facts
  · exact pt093_facts
  · exact pt094_facts
  · exact pt095_facts
  · exact pt096_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup006

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt081_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt081_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt082_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt082_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt083_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt083_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt084_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt084_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt085_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt085_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt086_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt086_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt087_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt087_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt088_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt088_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt089_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt089_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt090_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt090_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt091_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt091_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt092_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt092_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt093_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt093_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt094_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt094_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt095_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt095_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt096_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt096_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.all_points
