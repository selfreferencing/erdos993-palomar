module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.ExactComparisons.F3All.Normalization006
public import Erdos993Lean.ExactComparisons.F3All.Normalization007
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality015
public import Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality016
public import Erdos993Lean.ExactComparisons.F3All.Strict052
public import Erdos993Lean.ExactComparisons.F3All.Strict053
public import Erdos993Lean.ExactComparisons.F3All.Strict054
public import Erdos993Lean.ExactComparisons.F3All.Validity004
public import Erdos993Lean.ExactComparisons.F3All.Validity023
public import Erdos993Lean.ExactComparisons.F3All.Validity024
public import Erdos993Lean.ExactComparisons.F3All.Validity025

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.PointGroup003

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem pt033_facts : PointFacts pt033 := by
  apply pointFacts_of_quoted_checks pt033 (((7 : Rat) / (3 : Rat))) (((21302729 : Rat) / (10000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((10651363 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 11 (by change 11 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e054.y ∧ e054.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 47 (by change 47 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e054_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 55 (by change 55 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 9 (by change 9 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity023.checked 7 (by change 7 < 64; omega)
  · exact boolean_record_at Validity023.checked 8 (by change 8 < 64; omega)
  · exact comparison_record_at Strict052.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict052.checked 7 (by change 7 < 16; omega)

theorem pt034_facts : PointFacts pt034 := by
  apply pointFacts_of_quoted_checks pt034 (((7 : Rat) / (3 : Rat))) (((22123661 : Rat) / (10000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((11061829 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 12 (by change 12 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e060.y ∧ e060.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 53 (by change 53 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e060_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 56 (by change 56 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 13 (by change 13 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity023.checked 9 (by change 9 < 64; omega)
  · exact boolean_record_at Validity023.checked 10 (by change 10 < 64; omega)
  · exact comparison_record_at Strict052.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict052.checked 9 (by change 9 < 16; omega)

theorem pt035_facts : PointFacts pt035 := by
  apply pointFacts_of_quoted_checks pt035 (((7 : Rat) / (3 : Rat))) (((4509183 : Rat) / (2000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((2818239 : Rat) / (1250000 : Rat)))
  · exact boolean_record_at Validity004.checked 13 (by change 13 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e064.y ∧ e064.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 57 (by change 57 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e064_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 57 (by change 57 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 17 (by change 17 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity023.checked 11 (by change 11 < 64; omega)
  · exact boolean_record_at Validity023.checked 12 (by change 12 < 64; omega)
  · exact comparison_record_at Strict052.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict052.checked 11 (by change 11 < 16; omega)

theorem pt036_facts : PointFacts pt036 := by
  apply pointFacts_of_quoted_checks pt036 (((7 : Rat) / (3 : Rat))) (((22976229 : Rat) / (10000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((11488113 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 14 (by change 14 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e068.y ∧ e068.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity024.checked 61 (by change 61 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e068_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 58 (by change 58 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 21 (by change 21 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity023.checked 13 (by change 13 < 64; omega)
  · exact boolean_record_at Validity023.checked 14 (by change 14 < 64; omega)
  · exact comparison_record_at Strict052.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict052.checked 13 (by change 13 < 16; omega)

theorem pt037_facts : PointFacts pt037 := by
  apply pointFacts_of_quoted_checks pt037 (((7 : Rat) / (3 : Rat))) (((5853689 : Rat) / (2500000 : Rat))) (((7 : Rat) / (3 : Rat))) (((23414753 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 15 (by change 15 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e072.y ∧ e072.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 1 (by change 1 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e072_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 59 (by change 59 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 25 (by change 25 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity023.checked 15 (by change 15 < 64; omega)
  · exact boolean_record_at Validity023.checked 16 (by change 16 < 64; omega)
  · exact comparison_record_at Strict052.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict052.checked 15 (by change 15 < 16; omega)

theorem pt038_facts : PointFacts pt038 := by
  apply pointFacts_of_quoted_checks pt038 (((7 : Rat) / (3 : Rat))) (((5909287 : Rat) / (2500000 : Rat))) (((7 : Rat) / (3 : Rat))) (((4727429 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity004.checked 16 (by change 16 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e075.y ∧ e075.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 4 (by change 4 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e075_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 60 (by change 60 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 29 (by change 29 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity023.checked 17 (by change 17 < 64; omega)
  · exact boolean_record_at Validity023.checked 18 (by change 18 < 64; omega)
  · exact comparison_record_at Strict053.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict053.checked 1 (by change 1 < 16; omega)

theorem pt039_facts : PointFacts pt039 := by
  apply pointFacts_of_quoted_checks pt039 (((7 : Rat) / (3 : Rat))) (((5965413 : Rat) / (2500000 : Rat))) (((7 : Rat) / (3 : Rat))) (((23861649 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 17 (by change 17 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e077.y ∧ e077.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 6 (by change 6 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e077_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 61 (by change 61 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 33 (by change 33 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity023.checked 19 (by change 19 < 64; omega)
  · exact boolean_record_at Validity023.checked 20 (by change 20 < 64; omega)
  · exact comparison_record_at Strict053.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict053.checked 3 (by change 3 < 16; omega)

theorem pt040_facts : PointFacts pt040 := by
  apply pointFacts_of_quoted_checks pt040 (((7 : Rat) / (3 : Rat))) (((24088289 : Rat) / (10000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((12044143 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 18 (by change 18 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e079.y ∧ e079.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 8 (by change 8 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e079_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 62 (by change 62 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 37 (by change 37 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 38 (by change 38 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity023.checked 21 (by change 21 < 64; omega)
  · exact boolean_record_at Validity023.checked 22 (by change 22 < 64; omega)
  · exact comparison_record_at Strict053.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict053.checked 5 (by change 5 < 16; omega)

theorem pt041_facts : PointFacts pt041 := by
  apply pointFacts_of_quoted_checks pt041 (((7 : Rat) / (3 : Rat))) (((12158539 : Rat) / (5000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((972683 : Rat) / (400000 : Rat)))
  · exact boolean_record_at Validity004.checked 19 (by change 19 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e080.y ∧ e080.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 9 (by change 9 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e080_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization006.checked 63 (by change 63 < 64; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 41 (by change 41 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 42 (by change 42 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 43 (by change 43 < 64; omega)
  · exact boolean_record_at Validity023.checked 23 (by change 23 < 64; omega)
  · exact boolean_record_at Validity023.checked 24 (by change 24 < 64; omega)
  · exact comparison_record_at Strict053.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict053.checked 7 (by change 7 < 16; omega)

theorem pt042_facts : PointFacts pt042 := by
  apply pointFacts_of_quoted_checks pt042 (((7 : Rat) / (3 : Rat))) (((6195299 : Rat) / (2500000 : Rat))) (((7 : Rat) / (3 : Rat))) (((24781193 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 20 (by change 20 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e084.y ∧ e084.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 13 (by change 13 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e084_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 0 (by change 0 < 16; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 44 (by change 44 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 45 (by change 45 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 46 (by change 46 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 47 (by change 47 < 64; omega)
  · exact boolean_record_at Validity023.checked 25 (by change 25 < 64; omega)
  · exact boolean_record_at Validity023.checked 26 (by change 26 < 64; omega)
  · exact comparison_record_at Strict053.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict053.checked 9 (by change 9 < 16; omega)

theorem pt043_facts : PointFacts pt043 := by
  apply pointFacts_of_quoted_checks pt043 (((7 : Rat) / (3 : Rat))) (((25254173 : Rat) / (10000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((2525417 : Rat) / (1000000 : Rat)))
  · exact boolean_record_at Validity004.checked 21 (by change 21 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e087.y ∧ e087.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 16 (by change 16 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e087_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 1 (by change 1 < 16; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 48 (by change 48 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 49 (by change 49 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 50 (by change 50 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 51 (by change 51 < 64; omega)
  · exact boolean_record_at Validity023.checked 27 (by change 27 < 64; omega)
  · exact boolean_record_at Validity023.checked 28 (by change 28 < 64; omega)
  · exact comparison_record_at Strict053.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict053.checked 11 (by change 11 < 16; omega)

theorem pt044_facts : PointFacts pt044 := by
  apply pointFacts_of_quoted_checks pt044 (((7 : Rat) / (3 : Rat))) (((25736177 : Rat) / (10000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((12868087 : Rat) / (5000000 : Rat)))
  · exact boolean_record_at Validity004.checked 22 (by change 22 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e089.y ∧ e089.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 18 (by change 18 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e089_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 2 (by change 2 < 16; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 52 (by change 52 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 53 (by change 53 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 54 (by change 54 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 55 (by change 55 < 64; omega)
  · exact boolean_record_at Validity023.checked 29 (by change 29 < 64; omega)
  · exact boolean_record_at Validity023.checked 30 (by change 30 < 64; omega)
  · exact comparison_record_at Strict053.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict053.checked 13 (by change 13 < 16; omega)

theorem pt045_facts : PointFacts pt045 := by
  apply pointFacts_of_quoted_checks pt045 (((7 : Rat) / (3 : Rat))) (((13363979 : Rat) / (5000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((5345591 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity004.checked 23 (by change 23 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e092.y ∧ e092.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 21 (by change 21 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e092_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 3 (by change 3 < 16; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 56 (by change 56 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 57 (by change 57 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 59 (by change 59 < 64; omega)
  · exact boolean_record_at Validity023.checked 31 (by change 31 < 64; omega)
  · exact boolean_record_at Validity023.checked 32 (by change 32 < 64; omega)
  · exact comparison_record_at Strict053.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict053.checked 15 (by change 15 < 16; omega)

theorem pt046_facts : PointFacts pt046 := by
  apply pointFacts_of_quoted_checks pt046 (((7 : Rat) / (3 : Rat))) (((693949 : Rat) / (250000 : Rat))) (((7 : Rat) / (3 : Rat))) (((27757957 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 24 (by change 24 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e096.y ∧ e096.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 25 (by change 25 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e096_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 4 (by change 4 < 16; omega))
  · exact comparison_record_at ParentLookupEquality015.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at ParentLookupEquality015.checked 63 (by change 63 < 64; omega)
  · exact boolean_record_at Validity023.checked 33 (by change 33 < 64; omega)
  · exact boolean_record_at Validity023.checked 34 (by change 34 < 64; omega)
  · exact comparison_record_at Strict054.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict054.checked 1 (by change 1 < 16; omega)

theorem pt047_facts : PointFacts pt047 := by
  apply pointFacts_of_quoted_checks pt047 (((7 : Rat) / (3 : Rat))) (((14413827 : Rat) / (5000000 : Rat))) (((7 : Rat) / (3 : Rat))) (((28827651 : Rat) / (10000000 : Rat)))
  · exact boolean_record_at Validity004.checked 25 (by change 25 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e099.y ∧ e099.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 28 (by change 28 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e099_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 5 (by change 5 < 16; omega))
  · exact comparison_record_at ParentLookupEquality016.checked 0 (by change 0 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 1 (by change 1 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 2 (by change 2 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 3 (by change 3 < 44; omega)
  · exact boolean_record_at Validity023.checked 35 (by change 35 < 64; omega)
  · exact boolean_record_at Validity023.checked 36 (by change 36 < 64; omega)
  · exact comparison_record_at Strict054.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict054.checked 3 (by change 3 < 16; omega)

theorem pt048_facts : PointFacts pt048 := by
  apply pointFacts_of_quoted_checks pt048 (((7 : Rat) / (3 : Rat))) (((261991 : Rat) / (78125 : Rat))) (((7 : Rat) / (3 : Rat))) (((6706969 : Rat) / (2000000 : Rat)))
  · exact boolean_record_at Validity004.checked 26 (by change 26 < 64; omega)
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
  · exact (show 0 ≤ e107.y ∧ e107.y ≤ 3 from
      of_decide_eq_true (boolean_record_at Validity025.checked 36 (by change 36 < 64; omega))).1
  · exact Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e107_bounds
  · exact Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization007.checked 7 (by change 7 < 16; omega))
  · exact comparison_record_at ParentLookupEquality016.checked 8 (by change 8 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 9 (by change 9 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 10 (by change 10 < 44; omega)
  · exact comparison_record_at ParentLookupEquality016.checked 11 (by change 11 < 44; omega)
  · exact boolean_record_at Validity023.checked 39 (by change 39 < 64; omega)
  · exact boolean_record_at Validity023.checked 40 (by change 40 < 64; omega)
  · exact comparison_record_at Strict054.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict054.checked 7 (by change 7 < 16; omega)

def points : List Point := [pt033, pt034, pt035, pt036, pt037, pt038, pt039, pt040, pt041, pt042, pt043, pt044, pt045, pt046, pt047, pt048]

theorem all_points (p : Point) (hp : p ∈ points) : PointFacts p := by
  simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pt033_facts
  · exact pt034_facts
  · exact pt035_facts
  · exact pt036_facts
  · exact pt037_facts
  · exact pt038_facts
  · exact pt039_facts
  · exact pt040_facts
  · exact pt041_facts
  · exact pt042_facts
  · exact pt043_facts
  · exact pt044_facts
  · exact pt045_facts
  · exact pt046_facts
  · exact pt047_facts
  · exact pt048_facts

end Erdos993Lean.Analytic.V213.P03PointData.PointGroup003

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt033_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt033_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt034_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt034_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt035_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt035_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt036_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt036_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt037_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt037_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt038_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt038_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt039_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt039_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt040_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt040_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt041_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt041_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt042_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt042_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt043_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt043_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt044_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt044_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt045_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt045_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt046_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt046_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt047_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt047_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt048_facts
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt048_facts
#check Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.all_points
#print axioms Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.all_points
