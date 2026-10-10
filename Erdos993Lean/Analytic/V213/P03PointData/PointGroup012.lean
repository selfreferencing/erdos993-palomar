module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.ExactComparisons.F3All.Normalization004
public import Erdos993Lean.ExactComparisons.F3All.Normalization005
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality006
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality007
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality009
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality010
public import Erdos993Lean.ExactComparisons.F3All.Strict035
public import Erdos993Lean.ExactComparisons.F3All.Strict036
public import Erdos993Lean.ExactComparisons.F3All.Strict041
public import Erdos993Lean.ExactComparisons.F3All.Strict042
public import Erdos993Lean.ExactComparisons.F3All.Validity006
public import Erdos993Lean.ExactComparisons.F3All.Validity018
public import Erdos993Lean.ExactComparisons.F3All.Validity019
public import Erdos993Lean.ExactComparisons.F3All.Validity020
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup012

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt177_facts : PointFacts pt177 := by
  apply pointFacts_of_quoted_checks pt177 (((263 : Rat) / (200 : Rat))) (((5609139 : Rat) / (2000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((7011423 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 27 (by change 27 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e097.y ∧ e097.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 26 (by change 26 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 31 (by change 31 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity020.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity020.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict041.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict041.checked 7 (by change 7 < 16; omega)

theorem pt178_facts : PointFacts pt178 := by
  apply pointFacts_of_quoted_checks pt178 (((28 : Rat) / (25 : Rat))) (((7347909 : Rat) / (2500000 : Rat))) (((28 : Rat) / (25 : Rat))) (((29391633 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 28 (by change 28 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e100.y ∧ e100.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 29 (by change 29 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e100_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 46 (by change 46 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity018.checked 53 (by change 53 < 64; omega)
  · exact boolean_record_at Validity018.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at Strict035.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict035.checked 5 (by change 5 < 16; omega)

theorem pt179_facts : PointFacts pt179 := by
  apply pointFacts_of_quoted_checks pt179 (((263 : Rat) / (200 : Rat))) (((7347909 : Rat) / (2500000 : Rat))) (((263 : Rat) / (200 : Rat))) (((29391633 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 29 (by change 29 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e100.y ∧ e100.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 29 (by change 29 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e100_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 32 (by change 32 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity020.checked 25 (by change 25 < 64; omega)
  · exact boolean_record_at Validity020.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict041.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict041.checked 9 (by change 9 < 16; omega)

theorem pt180_facts : PointFacts pt180 := by
  apply pointFacts_of_quoted_checks pt180 (((263 : Rat) / (200 : Rat))) (((3080217 : Rat) / (1000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((30802167 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 30 (by change 30 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e103.y ∧ e103.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 32 (by change 32 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e103_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 33 (by change 33 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity020.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity020.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict041.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict041.checked 11 (by change 11 < 16; omega)

theorem pt181_facts : PointFacts pt181 := by
  apply pointFacts_of_quoted_checks pt181 (((28 : Rat) / (25 : Rat))) (((32280397 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((16140197 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 31 (by change 31 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e105.y ∧ e105.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 34 (by change 34 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e105_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 48 (by change 48 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity018.checked 57 (by change 57 < 64; omega)
  · exact boolean_record_at Validity018.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict035.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict035.checked 9 (by change 9 < 16; omega)

theorem pt182_facts : PointFacts pt182 := by
  apply pointFacts_of_quoted_checks pt182 (((263 : Rat) / (200 : Rat))) (((32280397 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((16140197 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 32 (by change 32 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e105.y ∧ e105.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 34 (by change 34 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e105_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 34 (by change 34 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity020.checked 29 (by change 29 < 64; omega)
  · exact boolean_record_at Validity020.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict041.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict041.checked 13 (by change 13 < 16; omega)

theorem pt183_facts : PointFacts pt183 := by
  apply pointFacts_of_quoted_checks pt183 (((263 : Rat) / (200 : Rat))) (((16914783 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((16914781 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 33 (by change 33 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e108.y ∧ e108.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 37 (by change 37 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 35 (by change 35 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity020.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity020.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict041.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict041.checked 15 (by change 15 < 16; omega)

theorem pt184_facts : PointFacts pt184 := by
  apply pointFacts_of_quoted_checks pt184 (((28 : Rat) / (25 : Rat))) (((35453081 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((35453077 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 34 (by change 34 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e110.y ∧ e110.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 39 (by change 39 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e110_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 50 (by change 50 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity018.checked 61 (by change 61 < 64; omega)
  · exact boolean_record_at Validity018.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict035.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict035.checked 13 (by change 13 < 16; omega)

theorem pt185_facts : PointFacts pt185 := by
  apply pointFacts_of_quoted_checks pt185 (((263 : Rat) / (200 : Rat))) (((35453081 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((35453077 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 35 (by change 35 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e110.y ∧ e110.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 39 (by change 39 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e110_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 36 (by change 36 < 64; omega))
  · exact comparison_record_at ParentLookupEquality009.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality009.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity020.checked 33 (by change 33 < 64; omega)
  · exact boolean_record_at Validity020.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict042.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict042.checked 1 (by change 1 < 16; omega)

theorem pt186_facts : PointFacts pt186 := by
  apply pointFacts_of_quoted_checks pt186 (((263 : Rat) / (200 : Rat))) (((37154509 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((18577253 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 36 (by change 36 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e112.y ∧ e112.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 41 (by change 41 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e112_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 37 (by change 37 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 3 (by change 3 < 64; omega)
  · exact boolean_record_at Validity020.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity020.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict042.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict042.checked 3 (by change 3 < 16; omega)

theorem pt187_facts : PointFacts pt187 := by
  apply pointFacts_of_quoted_checks pt187 (((28 : Rat) / (25 : Rat))) (((4867199 : Rat) / (1250000 : Rat))) (((28 : Rat) / (25 : Rat))) (((9734397 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 37 (by change 37 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e114.y ∧ e114.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 43 (by change 43 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e114_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 52 (by change 52 < 64; omega))
  · exact comparison_record_at ParentLookupEquality006.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality006.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity019.checked 1 (by change 1 < 64; omega)
  · exact boolean_record_at Validity019.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict036.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict036.checked 1 (by change 1 < 16; omega)

theorem pt188_facts : PointFacts pt188 := by
  apply pointFacts_of_quoted_checks pt188 (((263 : Rat) / (200 : Rat))) (((4867199 : Rat) / (1250000 : Rat))) (((263 : Rat) / (200 : Rat))) (((9734397 : Rat) / (2500000 : Rat)))
  · exact boolean_record_at Validity006.checked 38 (by change 38 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e114.y ∧ e114.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 43 (by change 43 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e114_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 38 (by change 38 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity020.checked 37 (by change 37 < 64; omega)
  · exact boolean_record_at Validity020.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at Strict042.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict042.checked 5 (by change 5 < 16; omega)

theorem pt189_facts : PointFacts pt189 := by
  apply pointFacts_of_quoted_checks pt189 (((263 : Rat) / (200 : Rat))) (((20403123 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((20403121 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 39 (by change 39 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e116.y ∧ e116.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 45 (by change 45 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 39 (by change 39 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity020.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity020.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict042.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict042.checked 7 (by change 7 < 16; omega)

theorem pt190_facts : PointFacts pt190 := by
  apply pointFacts_of_quoted_checks pt190 (((28 : Rat) / (25 : Rat))) (((42764579 : Rat) / (10000000 : Rat))) (((28 : Rat) / (25 : Rat))) (((21382287 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 40 (by change 40 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
  · exact (show 0 ≤ e118.y ∧ e118.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 47 (by change 47 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e118_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization004.checked 54 (by change 54 < 64; omega))
  · exact comparison_record_at ParentLookupEquality007.checked 4 (by change 4 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 5 (by change 5 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at ParentLookupEquality007.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity019.checked 5 (by change 5 < 64; omega)
  · exact boolean_record_at Validity019.checked 6 (by change 6 < 64; omega)
  · exact comparison_record_at Strict036.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict036.checked 5 (by change 5 < 16; omega)

theorem pt191_facts : PointFacts pt191 := by
  apply pointFacts_of_quoted_checks pt191 (((263 : Rat) / (200 : Rat))) (((42764579 : Rat) / (10000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((21382287 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity006.checked 41 (by change 41 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e118.y ∧ e118.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 47 (by change 47 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e118_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 40 (by change 40 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity020.checked 41 (by change 41 < 64; omega)
  · exact boolean_record_at Validity020.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at Strict042.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict042.checked 9 (by change 9 < 16; omega)

theorem pt192_facts : PointFacts pt192 := by
  apply pointFacts_of_quoted_checks pt192 (((263 : Rat) / (200 : Rat))) (((22408447 : Rat) / (5000000 : Rat))) (((263 : Rat) / (200 : Rat))) (((44816889 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity006.checked 42 (by change 42 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
  · exact (show 0 ≤ e120.y ∧ e120.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 49 (by change 49 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e120_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization005.checked 41 (by change 41 < 64; omega))
  · exact comparison_record_at ParentLookupEquality010.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality010.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity020.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity020.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at Strict042.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict042.checked 11 (by change 11 < 16; omega)

def points : List Point := [pt177, pt178, pt179, pt180, pt181, pt182, pt183, pt184, pt185, pt186, pt187, pt188, pt189, pt190, pt191, pt192]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt177_facts
  · exact pt178_facts
  · exact pt179_facts
  · exact pt180_facts
  · exact pt181_facts
  · exact pt182_facts
  · exact pt183_facts
  · exact pt184_facts
  · exact pt185_facts
  · exact pt186_facts
  · exact pt187_facts
  · exact pt188_facts
  · exact pt189_facts
  · exact pt190_facts
  · exact pt191_facts
  · exact pt192_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup012

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt177_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt177_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt178_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt178_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt179_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt179_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt180_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt180_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt181_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt181_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt182_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt182_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt183_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt183_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt184_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt184_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt185_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt185_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt186_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt186_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt187_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt187_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt188_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt188_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt189_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt189_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt190_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt190_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt191_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt191_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt192_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt192_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.all_points
