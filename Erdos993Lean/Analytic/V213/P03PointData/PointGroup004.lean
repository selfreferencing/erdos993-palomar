module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.ExactComparisons.F3All.Normalization003
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality001
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality002
public import Erdos993Lean.ExactComparisons.F3All.Strict024
public import Erdos993Lean.ExactComparisons.F3All.Strict025
public import Erdos993Lean.ExactComparisons.F3All.Strict026
public import Erdos993Lean.ExactComparisons.F3All.Strict027
public import Erdos993Lean.ExactComparisons.F3All.Validity004
public import Erdos993Lean.ExactComparisons.F3All.Validity016
public import Erdos993Lean.ExactComparisons.F3All.Validity023
public import Erdos993Lean.ExactComparisons.F3All.Validity024

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup004

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt049_facts : PointFacts pt049 := by
  have hz : pt049 = zeroPoint b01 := by
    norm_num [pt049, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b01
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds

theorem pt050_facts : PointFacts pt050 := by
  apply pointFacts_of_quoted_checks pt050 (((1 : Rat) / (3 : Rat))) (((10982853 : Rat) / (10000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((219657 : Rat) / (200000 : Rat)))
  · exact boolean_record_at Validity004.checked 28 (by change 28 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e002.y ∧ e002.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity023.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e002_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 21 (by change 21 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity016.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity016.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict024.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict024.checked 3 (by change 3 < 16; omega)

theorem pt051_facts : PointFacts pt051 := by
  apply pointFacts_of_quoted_checks pt051 (((3 : Rat) / (5 : Rat))) (((10982853 : Rat) / (10000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((219657 : Rat) / (200000 : Rat)))
  · exact boolean_record_at Validity004.checked 29 (by change 29 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e002.y ∧ e002.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity023.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e002_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 36 (by change 36 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity016.checked 33 (by change 33 < 64; omega)
  · exact boolean_record_at Validity016.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict026.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict026.checked 1 (by change 1 < 16; omega)

theorem pt052_facts : PointFacts pt052 := by
  apply pointFacts_of_quoted_checks pt052 (((1 : Rat) / (3 : Rat))) (((376947 : Rat) / (312500 : Rat))) (((1 : Rat) / (3 : Rat))) (((12062301 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 30 (by change 30 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e004.y ∧ e004.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity023.checked 61 (by change 61 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 22 (by change 22 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity016.checked 5 (by change 5 < 64; omega)
  · exact boolean_record_at Validity016.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict024.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict024.checked 5 (by change 5 < 16; omega)

theorem pt053_facts : PointFacts pt053 := by
  apply pointFacts_of_quoted_checks pt053 (((3 : Rat) / (5 : Rat))) (((376947 : Rat) / (312500 : Rat))) (((3 : Rat) / (5 : Rat))) (((12062301 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 31 (by change 31 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e004.y ∧ e004.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity023.checked 61 (by change 61 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 37 (by change 37 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity016.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity016.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict026.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict026.checked 3 (by change 3 < 16; omega)

theorem pt054_facts : PointFacts pt054 := by
  apply pointFacts_of_quoted_checks pt054 (((1 : Rat) / (3 : Rat))) (((6320593 : Rat) / (5000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((12641183 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 32 (by change 32 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e006.y ∧ e006.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity023.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e006_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 23 (by change 23 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity016.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity016.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict024.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict024.checked 7 (by change 7 < 16; omega)

theorem pt055_facts : PointFacts pt055 := by
  apply pointFacts_of_quoted_checks pt055 (((3 : Rat) / (5 : Rat))) (((6320593 : Rat) / (5000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((12641183 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 33 (by change 33 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e006.y ∧ e006.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity023.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e006_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 38 (by change 38 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity016.checked 37 (by change 37 < 64; omega)
  · exact boolean_record_at Validity016.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict026.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict026.checked 5 (by change 5 < 16; omega)

theorem pt056_facts : PointFacts pt056 := by
  apply pointFacts_of_quoted_checks pt056 (((1 : Rat) / (3 : Rat))) (((13247849 : Rat) / (10000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((6623923 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 34 (by change 34 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e008.y ∧ e008.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e008_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 24 (by change 24 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity016.checked 9 (by change 9 < 64; omega)
  · exact boolean_record_at Validity016.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict024.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict024.checked 9 (by change 9 < 16; omega)

theorem pt057_facts : PointFacts pt057 := by
  apply pointFacts_of_quoted_checks pt057 (((3 : Rat) / (5 : Rat))) (((13247849 : Rat) / (10000000 : Rat))) (((3 : Rat) / (5 : Rat))) (((6623923 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 35 (by change 35 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e008.y ∧ e008.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e008_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 39 (by change 39 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity016.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity016.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict026.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict026.checked 7 (by change 7 < 16; omega)

theorem pt058_facts : PointFacts pt058 := by
  apply pointFacts_of_quoted_checks pt058 (((1 : Rat) / (3 : Rat))) (((3637479 : Rat) / (2500000 : Rat))) (((1 : Rat) / (3 : Rat))) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 36 (by change 36 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 25 (by change 25 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity016.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity016.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict024.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict024.checked 11 (by change 11 < 16; omega)

theorem pt059_facts : PointFacts pt059 := by
  apply pointFacts_of_quoted_checks pt059 (((3 : Rat) / (5 : Rat))) (((3637479 : Rat) / (2500000 : Rat))) (((3 : Rat) / (5 : Rat))) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 37 (by change 37 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 41 (by change 41 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity016.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity016.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict026.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict026.checked 11 (by change 11 < 16; omega)

theorem pt060_facts : PointFacts pt060 := by
  apply pointFacts_of_quoted_checks pt060 (((1 : Rat) / (3 : Rat))) (((3994989 : Rat) / (2500000 : Rat))) (((1 : Rat) / (3 : Rat))) (((15979953 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 38 (by change 38 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e019.y ∧ e019.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 12 (by change 12 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 26 (by change 26 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity016.checked 13 (by change 13 < 64; omega)
  · exact boolean_record_at Validity016.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict024.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict024.checked 13 (by change 13 < 16; omega)

theorem pt061_facts : PointFacts pt061 := by
  apply pointFacts_of_quoted_checks pt061 (((3 : Rat) / (5 : Rat))) (((3994989 : Rat) / (2500000 : Rat))) (((3 : Rat) / (5 : Rat))) (((15979953 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 39 (by change 39 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e019.y ∧ e019.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 12 (by change 12 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 43 (by change 43 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity016.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity016.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict026.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict026.checked 15 (by change 15 < 16; omega)

theorem pt062_facts : PointFacts pt062 := by
  apply pointFacts_of_quoted_checks pt062 (((1 : Rat) / (3 : Rat))) (((4387637 : Rat) / (2500000 : Rat))) (((1 : Rat) / (3 : Rat))) (((3510109 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity004.checked 40 (by change 40 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e029.y ∧ e029.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 27 (by change 27 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity016.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity016.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict024.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict024.checked 15 (by change 15 < 16; omega)

theorem pt063_facts : PointFacts pt063 := by
  apply pointFacts_of_quoted_checks pt063 (((3 : Rat) / (5 : Rat))) (((4387637 : Rat) / (2500000 : Rat))) (((3 : Rat) / (5 : Rat))) (((3510109 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity004.checked 41 (by change 41 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
  · exact (show 0 ≤ e029.y ∧ e029.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 44 (by change 44 < 64; omega))
  · exact comparison_record_at ParentLookupEquality002.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality002.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity016.checked 49 (by change 49 < 64; omega)
  · exact boolean_record_at Validity016.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict027.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict027.checked 1 (by change 1 < 16; omega)

theorem pt064_facts : PointFacts pt064 := by
  apply pointFacts_of_quoted_checks pt064 (((1 : Rat) / (3 : Rat))) (((10585001 : Rat) / (5000000 : Rat))) (((1 : Rat) / (3 : Rat))) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 42 (by change 42 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 28 (by change 28 < 64; omega))
  · exact comparison_record_at ParentLookupEquality001.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality001.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity016.checked 17 (by change 17 < 64; omega)
  · exact boolean_record_at Validity016.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict025.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict025.checked 1 (by change 1 < 16; omega)

def points : List Point := [pt049, pt050, pt051, pt052, pt053, pt054, pt055, pt056, pt057, pt058, pt059, pt060, pt061, pt062, pt063, pt064]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt049_facts
  · exact pt050_facts
  · exact pt051_facts
  · exact pt052_facts
  · exact pt053_facts
  · exact pt054_facts
  · exact pt055_facts
  · exact pt056_facts
  · exact pt057_facts
  · exact pt058_facts
  · exact pt059_facts
  · exact pt060_facts
  · exact pt061_facts
  · exact pt062_facts
  · exact pt063_facts
  · exact pt064_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup004

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt049_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt049_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt050_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt050_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt051_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt051_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt052_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt052_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt053_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt053_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt054_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt054_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt055_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt055_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt056_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt056_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt057_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt057_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt058_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt058_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt059_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt059_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt060_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt060_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt061_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt061_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt062_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt062_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt063_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt063_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt064_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt064_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.all_points
