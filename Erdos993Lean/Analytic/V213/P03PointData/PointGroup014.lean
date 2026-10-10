module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.ExactComparisons.F3All.Normalization005
public import Erdos993Lean.ExactComparisons.F3All.Normalization006
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality011
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality012
public import Erdos993Lean.ExactComparisons.F3All.Strict044
public import Erdos993Lean.ExactComparisons.F3All.Strict045
public import Erdos993Lean.ExactComparisons.F3All.Strict046
public import Erdos993Lean.ExactComparisons.F3All.Validity006
public import Erdos993Lean.ExactComparisons.F3All.Validity007
public import Erdos993Lean.ExactComparisons.F3All.Validity021
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025
public import Erdos993Lean.ExactComparisons.F3All.Validity026

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup014

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt209_facts : PointFacts pt209 := by
  apply pointFacts_of_quoted_checks pt209 (((3 : Rat) / (2 : Rat))) (((10585001 : Rat) / (5000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((21169999 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 59 (by change 59 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e053.y ∧ e053.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 46 (by change 46 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e053_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 58 (by change 58 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity021.checked 13 (by change 13 < 64; omega)
  · exact boolean_record_at Validity021.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict044.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict044.checked 13 (by change 13 < 16; omega)

theorem pt210_facts : PointFacts pt210 := by
  apply pointFacts_of_quoted_checks pt210 (((3 : Rat) / (2 : Rat))) (((11625349 : Rat) / (5000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((4650139 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity006.checked 60 (by change 60 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e071.y ∧ e071.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 0 (by change 0 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 60 (by change 60 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity021.checked 17 (by change 17 < 64; omega)
  · exact boolean_record_at Validity021.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict045.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict045.checked 1 (by change 1 < 16; omega)

theorem pt211_facts : PointFacts pt211 := by
  apply pointFacts_of_quoted_checks pt211 (((3 : Rat) / (2 : Rat))) (((3191987 : Rat) / (1250000 : Rat))) (((3 : Rat) / (2 : Rat))) (((25535893 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 61 (by change 61 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e088.y ∧ e088.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 17 (by change 17 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 62 (by change 62 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity021.checked 21 (by change 21 < 64; omega)
  · exact boolean_record_at Validity021.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict045.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict045.checked 5 (by change 5 < 16; omega)

theorem pt212_facts : PointFacts pt212 := by
  apply pointFacts_of_quoted_checks pt212 (((3 : Rat) / (2 : Rat))) (((5609139 : Rat) / (2000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((7011423 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 62 (by change 62 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e097.y ∧ e097.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 26 (by change 26 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 63 (by change 63 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity021.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity021.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict045.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict045.checked 7 (by change 7 < 16; omega)

theorem pt213_facts : PointFacts pt213 := by
  apply pointFacts_of_quoted_checks pt213 (((3 : Rat) / (2 : Rat))) (((3080217 : Rat) / (1000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 63 (by change 63 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 0 (by change 0 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity021.checked 25 (by change 25 < 64; omega)
  · exact boolean_record_at Validity021.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict045.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict045.checked 9 (by change 9 < 16; omega)

theorem pt214_facts : PointFacts pt214 := by
  apply pointFacts_of_quoted_checks pt214 (((3 : Rat) / (2 : Rat))) (((16914783 : Rat) / (5000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((16914781 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity007.checked 0 (by change 0 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e108.y ∧ e108.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 37 (by change 37 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 1 (by change 1 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity021.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity021.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict045.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict045.checked 11 (by change 11 < 16; omega)

theorem pt215_facts : PointFacts pt215 := by
  apply pointFacts_of_quoted_checks pt215 (((3 : Rat) / (2 : Rat))) (((37154509 : Rat) / (10000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity007.checked 1 (by change 1 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 2 (by change 2 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity021.checked 29 (by change 29 < 64; omega)
  · exact boolean_record_at Validity021.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict045.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict045.checked 13 (by change 13 < 16; omega)

theorem pt216_facts : PointFacts pt216 := by
  apply pointFacts_of_quoted_checks pt216 (((3 : Rat) / (2 : Rat))) (((20403123 : Rat) / (5000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((20403121 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity007.checked 2 (by change 2 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e116.y ∧ e116.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 45 (by change 45 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 3 (by change 3 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity021.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity021.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict045.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict045.checked 15 (by change 15 < 16; omega)

theorem pt217_facts : PointFacts pt217 := by
  apply pointFacts_of_quoted_checks pt217 (((3 : Rat) / (2 : Rat))) (((22408447 : Rat) / (5000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 3 (by change 3 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 4 (by change 4 < 64; omega))
  · exact comparison_record_at ParentLookupEquality011.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality011.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity021.checked 33 (by change 33 < 64; omega)
  · exact boolean_record_at Validity021.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict046.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict046.checked 1 (by change 1 < 16; omega)

theorem pt218_facts : PointFacts pt218 := by
  apply pointFacts_of_quoted_checks pt218 (((3 : Rat) / (2 : Rat))) (((6757437 : Rat) / (1250000 : Rat))) (((3 : Rat) / (2 : Rat))) (((1689359 : Rat) / (312500 : Rat)))
  · exact boolean_record_at Validity007.checked 4 (by change 4 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e126.y ∧ e126.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 55 (by change 55 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 5 (by change 5 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity021.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity021.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict046.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict046.checked 3 (by change 3 < 16; omega)

theorem pt219_facts : PointFacts pt219 := by
  apply pointFacts_of_quoted_checks pt219 (((3 : Rat) / (2 : Rat))) (((32604103 : Rat) / (5000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((6520819 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity007.checked 5 (by change 5 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e130.y ∧ e130.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 59 (by change 59 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e130_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 6 (by change 6 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity021.checked 37 (by change 37 < 64; omega)
  · exact boolean_record_at Validity021.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict046.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict046.checked 5 (by change 5 < 16; omega)

theorem pt220_facts : PointFacts pt220 := by
  apply pointFacts_of_quoted_checks pt220 (((3 : Rat) / (2 : Rat))) (((629249 : Rat) / (80000 : Rat))) (((3 : Rat) / (2 : Rat))) (((78656091 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 6 (by change 6 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e134.y ∧ e134.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 63 (by change 63 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 7 (by change 7 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity021.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity021.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict046.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict046.checked 7 (by change 7 < 16; omega)

theorem pt221_facts : PointFacts pt221 := by
  apply pointFacts_of_quoted_checks pt221 (((3 : Rat) / (2 : Rat))) (((23719357 : Rat) / (2500000 : Rat))) (((3 : Rat) / (2 : Rat))) (((94877357 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 7 (by change 7 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e136.y ∧ e136.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e136_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 8 (by change 8 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity021.checked 41 (by change 41 < 64; omega)
  · exact boolean_record_at Validity021.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict046.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict046.checked 9 (by change 9 < 16; omega)

theorem pt222_facts : PointFacts pt222 := by
  apply pointFacts_of_quoted_checks pt222 (((3 : Rat) / (2 : Rat))) (((27609207 : Rat) / (2000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((6902287 : Rat) / (500000 : Rat)))
  · exact boolean_record_at Validity007.checked 8 (by change 8 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e138.y ∧ e138.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 3 (by change 3 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 9 (by change 9 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity021.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity021.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict046.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict046.checked 11 (by change 11 < 16; omega)

theorem pt223_facts : PointFacts pt223 := by
  apply pointFacts_of_quoted_checks pt223 (((3 : Rat) / (2 : Rat))) (((100428229 : Rat) / (5000000 : Rat))) (((3 : Rat) / (2 : Rat))) (((40171073 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity007.checked 9 (by change 9 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
  · exact (show 0 ≤ e140.y ∧ e140.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity026.checked 5 (by change 5 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e140_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 10 (by change 10 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity021.checked 45 (by change 45 < 64; omega)
  · exact boolean_record_at Validity021.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at Strict046.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict046.checked 13 (by change 13 < 16; omega)

theorem pt224_facts : PointFacts pt224 := by
  apply pointFacts_of_quoted_checks pt224 (((7 : Rat) / (4 : Rat))) (((3637479 : Rat) / (2500000 : Rat))) (((7 : Rat) / (4 : Rat))) (((14549913 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity007.checked 10 (by change 10 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
  · exact (show 0 ≤ e013.y ∧ e013.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e013_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 11 (by change 11 < 64; omega))
  · exact comparison_record_at ParentLookupEquality012.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality012.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity021.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity021.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at Strict046.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict046.checked 15 (by change 15 < 16; omega)

def points : List Point := [pt209, pt210, pt211, pt212, pt213, pt214, pt215, pt216, pt217, pt218, pt219, pt220, pt221, pt222, pt223, pt224]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt209_facts
  · exact pt210_facts
  · exact pt211_facts
  · exact pt212_facts
  · exact pt213_facts
  · exact pt214_facts
  · exact pt215_facts
  · exact pt216_facts
  · exact pt217_facts
  · exact pt218_facts
  · exact pt219_facts
  · exact pt220_facts
  · exact pt221_facts
  · exact pt222_facts
  · exact pt223_facts
  · exact pt224_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup014

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt209_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt209_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt210_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt210_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt211_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt211_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt212_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt212_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt213_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt213_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt214_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt214_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt215_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt215_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt216_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt216_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt217_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt217_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt218_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt218_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt219_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt219_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt220_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt220_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt221_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt221_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt222_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt222_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt223_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt223_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt224_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt224_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.all_points
