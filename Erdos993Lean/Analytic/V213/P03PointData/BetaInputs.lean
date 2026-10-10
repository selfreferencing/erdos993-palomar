module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.ExactComparisons.F3All.Normalization003
public import Erdos993Lean.ExactComparisons.F3All.Strict023
public import Erdos993Lean.ExactComparisons.F3All.Strict024
public import Erdos993Lean.ExactComparisons.F3All.Validity015
public import Erdos993Lean.ExactComparisons.F3All.Validity016

/-! Generated point interpretation.
No comparison is rerun. Original checked records are selected by list index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03PointData.BetaInputs

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem b01_activity_pos : (0 : Rat) < b01.lam := by norm_num [b01]

theorem b01_bounds : BetaEnclosure b01 := by
  apply beta_enclosure_of_checks b01
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 12 (by change 12 < 64; omega))
  · exact boolean_record_at Validity015.checked 58 (by change 58 < 64; omega)
  · exact comparison_record_at Strict023.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict023.checked 1 (by change 1 < 16; omega)

theorem b02_activity_pos : (0 : Rat) < b02.lam := by norm_num [b02]

theorem b02_bounds : BetaEnclosure b02 := by
  apply beta_enclosure_of_checks b02
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 13 (by change 13 < 64; omega))
  · exact boolean_record_at Validity015.checked 59 (by change 59 < 64; omega)
  · exact comparison_record_at Strict023.checked 2 (by change 2 < 16; omega)
  · exact comparison_record_at Strict023.checked 3 (by change 3 < 16; omega)

theorem b03_activity_pos : (0 : Rat) < b03.lam := by norm_num [b03]

theorem b03_bounds : BetaEnclosure b03 := by
  apply beta_enclosure_of_checks b03
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 14 (by change 14 < 64; omega))
  · exact boolean_record_at Validity015.checked 60 (by change 60 < 64; omega)
  · exact comparison_record_at Strict023.checked 4 (by change 4 < 16; omega)
  · exact comparison_record_at Strict023.checked 5 (by change 5 < 16; omega)

theorem b04_activity_pos : (0 : Rat) < b04.lam := by norm_num [b04]

theorem b04_bounds : BetaEnclosure b04 := by
  apply beta_enclosure_of_checks b04
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 15 (by change 15 < 64; omega))
  · exact boolean_record_at Validity015.checked 61 (by change 61 < 64; omega)
  · exact comparison_record_at Strict023.checked 6 (by change 6 < 16; omega)
  · exact comparison_record_at Strict023.checked 7 (by change 7 < 16; omega)

theorem b05_activity_pos : (0 : Rat) < b05.lam := by norm_num [b05]

theorem b05_bounds : BetaEnclosure b05 := by
  apply beta_enclosure_of_checks b05
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 16 (by change 16 < 64; omega))
  · exact boolean_record_at Validity015.checked 62 (by change 62 < 64; omega)
  · exact comparison_record_at Strict023.checked 8 (by change 8 < 16; omega)
  · exact comparison_record_at Strict023.checked 9 (by change 9 < 16; omega)

theorem b06_activity_pos : (0 : Rat) < b06.lam := by norm_num [b06]

theorem b06_bounds : BetaEnclosure b06 := by
  apply beta_enclosure_of_checks b06
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 17 (by change 17 < 64; omega))
  · exact boolean_record_at Validity015.checked 63 (by change 63 < 64; omega)
  · exact comparison_record_at Strict023.checked 10 (by change 10 < 16; omega)
  · exact comparison_record_at Strict023.checked 11 (by change 11 < 16; omega)

theorem b07_activity_pos : (0 : Rat) < b07.lam := by norm_num [b07]

theorem b07_bounds : BetaEnclosure b07 := by
  apply beta_enclosure_of_checks b07
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 18 (by change 18 < 64; omega))
  · exact boolean_record_at Validity016.checked 0 (by change 0 < 64; omega)
  · exact comparison_record_at Strict023.checked 12 (by change 12 < 16; omega)
  · exact comparison_record_at Strict023.checked 13 (by change 13 < 16; omega)

theorem b08_activity_pos : (0 : Rat) < b08.lam := by norm_num [b08]

theorem b08_bounds : BetaEnclosure b08 := by
  apply beta_enclosure_of_checks b08
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 19 (by change 19 < 64; omega))
  · exact boolean_record_at Validity016.checked 1 (by change 1 < 64; omega)
  · exact comparison_record_at Strict023.checked 14 (by change 14 < 16; omega)
  · exact comparison_record_at Strict023.checked 15 (by change 15 < 16; omega)

theorem b09_activity_pos : (0 : Rat) < b09.lam := by norm_num [b09]

theorem b09_bounds : BetaEnclosure b09 := by
  apply beta_enclosure_of_checks b09
  · exact Comparison.ofRats_sound _ _ .lt (comparison_record_at Normalization003.checked 20 (by change 20 < 64; omega))
  · exact boolean_record_at Validity016.checked 2 (by change 2 < 64; omega)
  · exact comparison_record_at Strict024.checked 0 (by change 0 < 16; omega)
  · exact comparison_record_at Strict024.checked 1 (by change 1 < 16; omega)


end Erdos993Lean.Analytic.V213.P03PointData.BetaInputs

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b01_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b02_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b03_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b04_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b05_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b06_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b07_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b08_bounds
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_activity_pos
#check Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
#print axioms Erdos993Lean.Analytic.V213.P03PointData.BetaInputs.b09_bounds
