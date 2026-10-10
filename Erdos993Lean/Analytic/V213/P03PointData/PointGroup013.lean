module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.ExactComparisons.F3All.Normalization004
public import Erdos993Lean.ExactComparisons.F3All.Normalization005
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality007
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality010
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality011
public import Erdos993Lean.ExactComparisons.F3All.Strict036
public import Erdos993Lean.ExactComparisons.F3All.Strict037
public import Erdos993Lean.ExactComparisons.F3All.Strict042
public import Erdos993Lean.ExactComparisons.F3All.Strict043
public import Erdos993Lean.ExactComparisons.F3All.Strict044
public import Erdos993Lean.ExactComparisons.F3All.Validity006
public import Erdos993Lean.ExactComparisons.F3All.Validity019
public import Erdos993Lean.ExactComparisons.F3All.Validity020
public import Erdos993Lean.ExactComparisons.F3All.Validity021
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025
public import Erdos993Lean.ExactComparisons.F3All.Validity026

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup013

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt193_facts : PointFacts pt193 := by
  apply pointFacts_of_quoted_checks pt193 (((28 : Rat) / (25 : Rat))) (((23483851 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((46967697 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 43 (by change 43 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e122.y ∧ e122.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 51 (by change 51 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e122_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 56 (by change 56 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity019.checked 9 (by change 9 < 64; omega)
  · exact boolean_record_at Validity019.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict036.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict036.checked 9 (by change 9 < 16; omega)

theorem pt194_facts : PointFacts pt194 := by
  apply pointFacts_of_quoted_checks pt194 (((263 : Rat) / (200 : Rat))) (((23483851 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((46967697 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 44 (by change 44 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e122.y ∧ e122.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 51 (by change 51 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e122_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 42 (by change 42 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity020.checked 45 (by change 45 < 64; omega)
  · exact boolean_record_at Validity020.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict042.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict042.checked 13 (by change 13 < 16; omega)

theorem pt195_facts : PointFacts pt195 := by
  apply pointFacts_of_quoted_checks pt195 (((263 : Rat) / (200 : Rat))) (((4922173 : Rat) / (1000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((12305431 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 45 (by change 45 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e124.y ∧ e124.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 53 (by change 53 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 43 (by change 43 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity020.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity020.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict042.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict042.checked 15 (by change 15 < 16; omega)

theorem pt196_facts : PointFacts pt196 := by
  apply pointFacts_of_quoted_checks pt196 (((263 : Rat) / (200 : Rat))) (((6757437 : Rat) / (1250000 : Rat))) (((263 : Rat) / (200 : Rat))) (((1689359 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity006.checked 46 (by change 46 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e126.y ∧ e126.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 44 (by change 44 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity020.checked 49 (by change 49 < 64; omega)
  · exact boolean_record_at Validity020.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at Strict043.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict043.checked 1 (by change 1 < 16; omega)

theorem pt197_facts : PointFacts pt197 := by
  apply pointFacts_of_quoted_checks pt197 (((28 : Rat) / (25 : Rat))) (((59372743 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((14843183 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 47 (by change 47 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e128.y ∧ e128.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 57 (by change 57 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 59 (by change 59 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity019.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity019.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict036.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict036.checked 15 (by change 15 < 16; omega)

theorem pt198_facts : PointFacts pt198 := by
  apply pointFacts_of_quoted_checks pt198 (((263 : Rat) / (200 : Rat))) (((59372743 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((14843183 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 48 (by change 48 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e128.y ∧ e128.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 57 (by change 57 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 45 (by change 45 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity020.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity020.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict043.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict043.checked 3 (by change 3 < 16; omega)

theorem pt199_facts : PointFacts pt199 := by
  apply pointFacts_of_quoted_checks pt199 (((263 : Rat) / (200 : Rat))) (((32604103 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity006.checked 49 (by change 49 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 46 (by change 46 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity020.checked 53 (by change 53 < 64; omega)
  · exact boolean_record_at Validity020.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict043.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict043.checked 5 (by change 5 < 16; omega)

theorem pt200_facts : PointFacts pt200 := by
  apply pointFacts_of_quoted_checks pt200 (((28 : Rat) / (25 : Rat))) (((71617209 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((35808593 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 50 (by change 50 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e132.y ∧ e132.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 61 (by change 61 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 61 (by change 61 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity019.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity019.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict037.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict037.checked 3 (by change 3 < 16; omega)

theorem pt201_facts : PointFacts pt201 := by
  apply pointFacts_of_quoted_checks pt201 (((263 : Rat) / (200 : Rat))) (((71617209 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((35808593 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 51 (by change 51 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e132.y ∧ e132.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 61 (by change 61 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 47 (by change 47 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity020.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity020.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at Strict043.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict043.checked 7 (by change 7 < 16; omega)

theorem pt202_facts : PointFacts pt202 := by
  apply pointFacts_of_quoted_checks pt202 (((263 : Rat) / (200 : Rat))) (((629249 : Rat) / (80000 : Rat))) (((263 : Rat) / (200 : Rat))) (((78656091 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 52 (by change 52 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e134.y ∧ e134.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 48 (by change 48 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity020.checked 57 (by change 57 < 64; omega)
  · exact boolean_record_at Validity020.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict043.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict043.checked 9 (by change 9 < 16; omega)

theorem pt203_facts : PointFacts pt203 := by
  apply pointFacts_of_quoted_checks pt203 (((263 : Rat) / (200 : Rat))) (((23719357 : Rat) / (2500000 : Rat))) (((263 : Rat) / (200 : Rat))) (((94877357 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 53 (by change 53 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e136.y ∧ e136.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 49 (by change 49 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity020.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity020.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict043.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict043.checked 11 (by change 11 < 16; omega)

theorem pt204_facts : PointFacts pt204 := by
  apply pointFacts_of_quoted_checks pt204 (((263 : Rat) / (200 : Rat))) (((27609207 : Rat) / (2000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((6902287 : Rat) / (500000 : Rat)))
  · exact boolean_record_at Validity006.checked 54 (by change 54 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e138.y ∧ e138.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 3 (by change 3 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 50 (by change 50 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity020.checked 61 (by change 61 < 64; omega)
  · exact boolean_record_at Validity020.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict043.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict043.checked 13 (by change 13 < 16; omega)

theorem pt205_facts : PointFacts pt205 := by
  apply pointFacts_of_quoted_checks pt205 (((263 : Rat) / (200 : Rat))) (((100428229 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((40171073 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity006.checked 55 (by change 55 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e140.y ∧ e140.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 51 (by change 51 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity020.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity021.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict043.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict043.checked 15 (by change 15 < 16; omega)

theorem pt206_facts : PointFacts pt206 := by
  apply pointFacts_of_quoted_checks pt206 (((3 : Rat) / (2 : Rat))) (((3637479 : Rat) / (2500000 : Rat))) (((3 : Rat) / (2 : Rat))) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 56 (by change 56 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 52 (by change 52 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity021.checked 1 (by change 1 < 64; omega)
  · exact boolean_record_at Validity021.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict044.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict044.checked 1 (by change 1 < 16; omega)

theorem pt207_facts : PointFacts pt207 := by
  apply pointFacts_of_quoted_checks pt207 (((3 : Rat) / (2 : Rat))) (((4387637 : Rat) / (2500000 : Rat))) (((3 : Rat) / (2 : Rat))) (((3510109 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity006.checked 57 (by change 57 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e029.y ∧ e029.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 22 (by change 22 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 54 (by change 54 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity021.checked 5 (by change 5 < 64; omega)
  · exact boolean_record_at Validity021.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict044.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict044.checked 5 (by change 5 < 16; omega)

theorem pt208_facts : PointFacts pt208 := by
  apply pointFacts_of_quoted_checks pt208 (((3 : Rat) / (2 : Rat))) (((9637753 : Rat) / (5000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((19275503 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 58 (by change 58 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e040.y ∧ e040.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 33 (by change 33 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 55 (by change 55 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity021.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity021.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict044.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict044.checked 7 (by change 7 < 16; omega)

def points : List Point := [pt193, pt194, pt195, pt196, pt197, pt198, pt199, pt200, pt201, pt202, pt203, pt204, pt205, pt206, pt207, pt208]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt193_facts
  · exact pt194_facts
  · exact pt195_facts
  · exact pt196_facts
  · exact pt197_facts
  · exact pt198_facts
  · exact pt199_facts
  · exact pt200_facts
  · exact pt201_facts
  · exact pt202_facts
  · exact pt203_facts
  · exact pt204_facts
  · exact pt205_facts
  · exact pt206_facts
  · exact pt207_facts
  · exact pt208_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup013

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt193_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt193_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt194_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt194_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt195_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt195_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt196_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt196_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt197_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt197_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt198_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt198_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt199_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt199_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt200_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt200_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt201_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt201_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt202_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt202_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt203_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt203_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt204_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt204_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt205_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt205_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt206_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt206_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt207_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt207_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt208_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt208_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.all_points
