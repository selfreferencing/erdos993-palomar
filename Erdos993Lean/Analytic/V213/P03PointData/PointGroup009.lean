module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.ExactComparisons.F3All.Normalization004
public import Erdos993Lean.ExactComparisons.F3All.Normalization005
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality004
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality007
public import Erdos993Lean.ExactComparisons.F3All.Strict030
public import Erdos993Lean.ExactComparisons.F3All.Strict031
public import Erdos993Lean.ExactComparisons.F3All.Strict036
public import Erdos993Lean.ExactComparisons.F3All.Strict037
public import Erdos993Lean.ExactComparisons.F3All.Strict038
public import Erdos993Lean.ExactComparisons.F3All.Validity005
public import Erdos993Lean.ExactComparisons.F3All.Validity017
public import Erdos993Lean.ExactComparisons.F3All.Validity019
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025
public import Erdos993Lean.ExactComparisons.F3All.Validity026

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup009

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt129_facts : PointFacts pt129 := by
  apply pointFacts_of_quoted_checks pt129 (((7 : Rat) / (8 : Rat))) (((20403123 : Rat) / (5000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((20403121 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 43 (by change 43 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e116.y ∧ e116.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 45 (by change 45 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 11 (by change 11 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity017.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity017.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict030.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict030.checked 15 (by change 15 < 16; omega)

theorem pt130_facts : PointFacts pt130 := by
  apply pointFacts_of_quoted_checks pt130 (((28 : Rat) / (25 : Rat))) (((20403123 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((20403121 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 44 (by change 44 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e116.y ∧ e116.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 45 (by change 45 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 53 (by change 53 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity019.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity019.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at Strict036.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict036.checked 3 (by change 3 < 16; omega)

theorem pt131_facts : PointFacts pt131 := by
  apply pointFacts_of_quoted_checks pt131 (((28 : Rat) / (25 : Rat))) (((22408447 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 45 (by change 45 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 55 (by change 55 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity019.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity019.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict036.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict036.checked 7 (by change 7 < 16; omega)

theorem pt132_facts : PointFacts pt132 := by
  apply pointFacts_of_quoted_checks pt132 (((7 : Rat) / (8 : Rat))) (((4922173 : Rat) / (1000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((12305431 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity005.checked 46 (by change 46 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e124.y ∧ e124.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 53 (by change 53 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 13 (by change 13 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity017.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity017.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at Strict031.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict031.checked 3 (by change 3 < 16; omega)

theorem pt133_facts : PointFacts pt133 := by
  apply pointFacts_of_quoted_checks pt133 (((28 : Rat) / (25 : Rat))) (((4922173 : Rat) / (1000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((12305431 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity005.checked 47 (by change 47 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e124.y ∧ e124.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 53 (by change 53 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 57 (by change 57 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity019.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity019.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict036.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict036.checked 11 (by change 11 < 16; omega)

theorem pt134_facts : PointFacts pt134 := by
  apply pointFacts_of_quoted_checks pt134 (((28 : Rat) / (25 : Rat))) (((6757437 : Rat) / (1250000 : Rat))) (((28 : Rat) / (25 : Rat))) (((1689359 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity005.checked 48 (by change 48 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e126.y ∧ e126.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 58 (by change 58 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity019.checked 13 (by change 13 < 64; omega)
  · exact boolean_record_at Validity019.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict036.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict036.checked 13 (by change 13 < 16; omega)

theorem pt135_facts : PointFacts pt135 := by
  apply pointFacts_of_quoted_checks pt135 (((28 : Rat) / (25 : Rat))) (((32604103 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity005.checked 49 (by change 49 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 60 (by change 60 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity019.checked 17 (by change 17 < 64; omega)
  · exact boolean_record_at Validity019.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict037.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict037.checked 1 (by change 1 < 16; omega)

theorem pt136_facts : PointFacts pt136 := by
  apply pointFacts_of_quoted_checks pt136 (((7 : Rat) / (8 : Rat))) (((629249 : Rat) / (80000 : Rat))) (((7 : Rat) / (8 : Rat))) (((78656091 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 50 (by change 50 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e134.y ∧ e134.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 16 (by change 16 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity017.checked 57 (by change 57 < 64; omega)
  · exact boolean_record_at Validity017.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict031.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict031.checked 9 (by change 9 < 16; omega)

theorem pt137_facts : PointFacts pt137 := by
  apply pointFacts_of_quoted_checks pt137 (((28 : Rat) / (25 : Rat))) (((629249 : Rat) / (80000 : Rat))) (((28 : Rat) / (25 : Rat))) (((78656091 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 51 (by change 51 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e134.y ∧ e134.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 62 (by change 62 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity019.checked 21 (by change 21 < 64; omega)
  · exact boolean_record_at Validity019.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict037.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict037.checked 5 (by change 5 < 16; omega)

theorem pt138_facts : PointFacts pt138 := by
  apply pointFacts_of_quoted_checks pt138 (((28 : Rat) / (25 : Rat))) (((23719357 : Rat) / (2500000 : Rat))) (((28 : Rat) / (25 : Rat))) (((94877357 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 52 (by change 52 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e136.y ∧ e136.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 63 (by change 63 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity019.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity019.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict037.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict037.checked 7 (by change 7 < 16; omega)

theorem pt139_facts : PointFacts pt139 := by
  apply pointFacts_of_quoted_checks pt139 (((7 : Rat) / (8 : Rat))) (((27609207 : Rat) / (2000000 : Rat))) (((7 : Rat) / (8 : Rat))) (((6902287 : Rat) / (500000 : Rat)))
  · exact boolean_record_at Validity005.checked 53 (by change 53 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
  · exact (show 0 ≤ e138.y ∧ e138.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 3 (by change 3 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 18 (by change 18 < 64; omega))
  · exact comparison_record_at ParentLookupEquality004.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality004.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity017.checked 61 (by change 61 < 64; omega)
  · exact boolean_record_at Validity017.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict031.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict031.checked 13 (by change 13 < 16; omega)

theorem pt140_facts : PointFacts pt140 := by
  apply pointFacts_of_quoted_checks pt140 (((28 : Rat) / (25 : Rat))) (((27609207 : Rat) / (2000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((6902287 : Rat) / (500000 : Rat)))
  · exact boolean_record_at Validity005.checked 54 (by change 54 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e138.y ∧ e138.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 3 (by change 3 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 0 (by change 0 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity019.checked 25 (by change 25 < 64; omega)
  · exact boolean_record_at Validity019.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict037.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict037.checked 9 (by change 9 < 16; omega)

theorem pt141_facts : PointFacts pt141 := by
  apply pointFacts_of_quoted_checks pt141 (((28 : Rat) / (25 : Rat))) (((100428229 : Rat) / (5000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((40171073 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity005.checked 55 (by change 55 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e140.y ∧ e140.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 1 (by change 1 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity019.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity019.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict037.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict037.checked 11 (by change 11 < 16; omega)

theorem pt142_facts : PointFacts pt142 := by
  have hz : pt142 = zeroPoint b04 := by
    norm_num [pt142, zeroPoint, e000]
  rw [hz]
  exact Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts b04
    Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds

theorem pt143_facts : PointFacts pt143 := by
  apply pointFacts_of_quoted_checks pt143 (((263 : Rat) / (200 : Rat))) (((3637479 : Rat) / (2500000 : Rat))) (((263 : Rat) / (200 : Rat))) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity005.checked 57 (by change 57 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 2 (by change 2 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity019.checked 29 (by change 29 < 64; omega)
  · exact boolean_record_at Validity019.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict037.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict037.checked 13 (by change 13 < 16; omega)

theorem pt144_facts : PointFacts pt144 := by
  apply pointFacts_of_quoted_checks pt144 (((263 : Rat) / (200 : Rat))) (((15248181 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((7624089 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity005.checked 58 (by change 58 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e016.y ∧ e016.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 9 (by change 9 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e016_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 4 (by change 4 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity019.checked 33 (by change 33 < 64; omega)
  · exact boolean_record_at Validity019.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict038.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict038.checked 1 (by change 1 < 16; omega)

def points : List Point := [pt129, pt130, pt131, pt132, pt133, pt134, pt135, pt136, pt137, pt138, pt139, pt140, pt141, pt142, pt143, pt144]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt129_facts
  · exact pt130_facts
  · exact pt131_facts
  · exact pt132_facts
  · exact pt133_facts
  · exact pt134_facts
  · exact pt135_facts
  · exact pt136_facts
  · exact pt137_facts
  · exact pt138_facts
  · exact pt139_facts
  · exact pt140_facts
  · exact pt141_facts
  · exact pt142_facts
  · exact pt143_facts
  · exact pt144_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup009

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt129_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt129_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt130_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt130_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt131_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt131_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt132_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt132_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt133_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt133_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt134_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt134_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt135_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt135_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt136_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt136_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt137_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt137_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt138_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt138_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt139_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt139_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt140_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt140_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt141_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt141_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt142_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt142_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt143_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt143_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt144_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt144_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.all_points
