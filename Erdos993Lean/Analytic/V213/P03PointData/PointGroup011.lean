module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.ExactComparisons.F3All.Normalization004
public import Erdos993Lean.ExactComparisons.F3All.Normalization005
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality005
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality006
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality008
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality009
public import Erdos993Lean.ExactComparisons.F3All.Strict033
public import Erdos993Lean.ExactComparisons.F3All.Strict034
public import Erdos993Lean.ExactComparisons.F3All.Strict035
public import Erdos993Lean.ExactComparisons.F3All.Strict039
public import Erdos993Lean.ExactComparisons.F3All.Strict040
public import Erdos993Lean.ExactComparisons.F3All.Strict041
public import Erdos993Lean.ExactComparisons.F3All.Validity006
public import Erdos993Lean.ExactComparisons.F3All.Validity018
public import Erdos993Lean.ExactComparisons.F3All.Validity019
public import Erdos993Lean.ExactComparisons.F3All.Validity020
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup011

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt161_facts : PointFacts pt161 := by
  apply pointFacts_of_quoted_checks pt161 (((28 : Rat) / (25 : Rat))) (((20679599 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((5169899 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 11 (by change 11 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e049.y ∧ e049.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 42 (by change 42 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e049_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 35 (by change 35 < 64; omega))
  · exact comparison_record_at ParentLookupEquality005.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality005.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity018.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity018.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict033.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict033.checked 15 (by change 15 < 16; omega)

theorem pt162_facts : PointFacts pt162 := by
  apply pointFacts_of_quoted_checks pt162 (((263 : Rat) / (200 : Rat))) (((20679599 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((5169899 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 12 (by change 12 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e049.y ∧ e049.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 42 (by change 42 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e049_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 18 (by change 18 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity019.checked 61 (by change 61 < 64; omega)
  · exact boolean_record_at Validity019.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict039.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict039.checked 13 (by change 13 < 16; omega)

theorem pt163_facts : PointFacts pt163 := by
  apply pointFacts_of_quoted_checks pt163 (((263 : Rat) / (200 : Rat))) (((10585001 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 13 (by change 13 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 20 (by change 20 < 64; omega))
  · exact comparison_record_at ParentLookupEquality008.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality008.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity020.checked 1 (by change 1 < 64; omega)
  · exact boolean_record_at Validity020.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict040.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict040.checked 1 (by change 1 < 16; omega)

theorem pt164_facts : PointFacts pt164 := by
  apply pointFacts_of_quoted_checks pt164 (((28 : Rat) / (25 : Rat))) (((10836017 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((21672031 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 14 (by change 14 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e057.y ∧ e057.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 50 (by change 50 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e057_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 37 (by change 37 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity018.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity018.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict034.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict034.checked 3 (by change 3 < 16; omega)

theorem pt165_facts : PointFacts pt165 := by
  apply pointFacts_of_quoted_checks pt165 (((263 : Rat) / (200 : Rat))) (((10836017 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((21672031 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 15 (by change 15 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e057.y ∧ e057.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 50 (by change 50 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e057_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 21 (by change 21 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity020.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity020.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict040.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict040.checked 3 (by change 3 < 16; omega)

theorem pt166_facts : PointFacts pt166 := by
  apply pointFacts_of_quoted_checks pt166 (((263 : Rat) / (200 : Rat))) (((22185971 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((1386623 : Rat) / (625000 : Rat)))
  · exact boolean_record_at Validity006.checked 16 (by change 16 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e061.y ∧ e061.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 54 (by change 54 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e061_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 23 (by change 23 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity020.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity020.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict040.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict040.checked 7 (by change 7 < 16; omega)

theorem pt167_facts : PointFacts pt167 := by
  apply pointFacts_of_quoted_checks pt167 (((28 : Rat) / (25 : Rat))) (((709753 : Rat) / (312500 : Rat))) (((28 : Rat) / (25 : Rat))) (((22712093 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 17 (by change 17 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e065.y ∧ e065.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 58 (by change 58 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e065_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 39 (by change 39 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity018.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity018.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict034.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict034.checked 7 (by change 7 < 16; omega)

theorem pt168_facts : PointFacts pt168 := by
  apply pointFacts_of_quoted_checks pt168 (((263 : Rat) / (200 : Rat))) (((709753 : Rat) / (312500 : Rat))) (((263 : Rat) / (200 : Rat))) (((22712093 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 18 (by change 18 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e065.y ∧ e065.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 58 (by change 58 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e065_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 24 (by change 24 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity020.checked 9 (by change 9 < 64; omega)
  · exact boolean_record_at Validity020.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict040.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict040.checked 9 (by change 9 < 16; omega)

theorem pt169_facts : PointFacts pt169 := by
  apply pointFacts_of_quoted_checks pt169 (((263 : Rat) / (200 : Rat))) (((11625349 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((4650139 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity006.checked 19 (by change 19 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e071.y ∧ e071.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 0 (by change 0 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 26 (by change 26 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity020.checked 13 (by change 13 < 64; omega)
  · exact boolean_record_at Validity020.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict040.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict040.checked 13 (by change 13 < 16; omega)

theorem pt170_facts : PointFacts pt170 := by
  apply pointFacts_of_quoted_checks pt170 (((28 : Rat) / (25 : Rat))) (((23802073 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((23802069 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 20 (by change 20 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e076.y ∧ e076.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e076_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 41 (by change 41 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity018.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity018.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict034.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict034.checked 11 (by change 11 < 16; omega)

theorem pt171_facts : PointFacts pt171 := by
  apply pointFacts_of_quoted_checks pt171 (((263 : Rat) / (200 : Rat))) (((23802073 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((23802069 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 21 (by change 21 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e076.y ∧ e076.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e076_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 27 (by change 27 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity020.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity020.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict040.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict040.checked 15 (by change 15 < 16; omega)

theorem pt172_facts : PointFacts pt172 := by
  apply pointFacts_of_quoted_checks pt172 (((28 : Rat) / (25 : Rat))) (((12183261 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((24366519 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 22 (by change 22 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e081.y ∧ e081.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 10 (by change 10 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e081_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 42 (by change 42 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity018.checked 45 (by change 45 < 64; omega)
  · exact boolean_record_at Validity018.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict034.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict034.checked 13 (by change 13 < 16; omega)

theorem pt173_facts : PointFacts pt173 := by
  apply pointFacts_of_quoted_checks pt173 (((263 : Rat) / (200 : Rat))) (((12183261 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((24366519 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 23 (by change 23 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e081.y ∧ e081.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 10 (by change 10 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e081_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 28 (by change 28 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity020.checked 17 (by change 17 < 64; omega)
  · exact boolean_record_at Validity020.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict041.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict041.checked 1 (by change 1 < 16; omega)

theorem pt174_facts : PointFacts pt174 := by
  apply pointFacts_of_quoted_checks pt174 (((263 : Rat) / (200 : Rat))) (((3191987 : Rat) / (1250000 : Rat))) (((263 : Rat) / (200 : Rat))) (((25535893 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 24 (by change 24 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e088.y ∧ e088.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 29 (by change 29 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity020.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity020.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict041.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict041.checked 3 (by change 3 < 16; omega)

theorem pt175_facts : PointFacts pt175 := by
  apply pointFacts_of_quoted_checks pt175 (((28 : Rat) / (25 : Rat))) (((26761389 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((13380693 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 25 (by change 25 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e093.y ∧ e093.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e093_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 44 (by change 44 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity018.checked 49 (by change 49 < 64; omega)
  · exact boolean_record_at Validity018.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict035.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict035.checked 1 (by change 1 < 16; omega)

theorem pt176_facts : PointFacts pt176 := by
  apply pointFacts_of_quoted_checks pt176 (((263 : Rat) / (200 : Rat))) (((26761389 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((13380693 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 26 (by change 26 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e093.y ∧ e093.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e093_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 30 (by change 30 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity020.checked 21 (by change 21 < 64; omega)
  · exact boolean_record_at Validity020.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict041.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict041.checked 5 (by change 5 < 16; omega)

def points : List Point := [pt161, pt162, pt163, pt164, pt165, pt166, pt167, pt168, pt169, pt170, pt171, pt172, pt173, pt174, pt175, pt176]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt161_facts
  · exact pt162_facts
  · exact pt163_facts
  · exact pt164_facts
  · exact pt165_facts
  · exact pt166_facts
  · exact pt167_facts
  · exact pt168_facts
  · exact pt169_facts
  · exact pt170_facts
  · exact pt171_facts
  · exact pt172_facts
  · exact pt173_facts
  · exact pt174_facts
  · exact pt175_facts
  · exact pt176_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup011

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt161_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt161_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt162_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt162_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt163_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt163_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt164_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt164_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt165_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt165_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt166_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt166_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt167_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt167_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt168_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt168_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt169_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt169_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt170_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt170_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt171_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt171_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt172_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt172_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt173_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt173_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt174_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt174_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt175_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt175_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt176_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt176_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.all_points
