module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup014
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup015
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup016
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput006
public import Erdos993Lean.ExactComparisons.F3All.Strict076
public import Erdos993Lean.ExactComparisons.F3All.Strict077
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity014
public import Erdos993Lean.ExactComparisons.F3All.Validity015

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows018

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a137_certificate : ARowCertificate a137 := by
  have hf : ARowFacts a137 := ⟨(boolean_record_at Validity014.checked 50 (by change 50 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt224_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt225_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt238_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds)⟩
  have hm := parent_positive_of_checks a137 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 23 (by change 23 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 22 (by change 22 < 64; omega)))
    (comparison_record_at Strict076.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict076.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 8 (by change 8 < 64; omega)),
    cellM0_positive_of_check a137 (boolean_record_at Validity014.checked 51 (by change 51 < 64; omega)), hm.1, hm.2⟩

theorem a138_certificate : ARowCertificate a138 := by
  have hf : ARowFacts a138 := ⟨(boolean_record_at Validity014.checked 53 (by change 53 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt225_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt226_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt239_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds)⟩
  have hm := parent_positive_of_checks a138 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 25 (by change 25 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 24 (by change 24 < 64; omega)))
    (comparison_record_at Strict077.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict077.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 9 (by change 9 < 64; omega)),
    cellM0_positive_of_check a138 (boolean_record_at Validity014.checked 54 (by change 54 < 64; omega)), hm.1, hm.2⟩

theorem a139_certificate : ARowCertificate a139 := by
  have hf : ARowFacts a139 := ⟨(boolean_record_at Validity014.checked 56 (by change 56 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt226_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt227_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt240_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds)⟩
  have hm := parent_positive_of_checks a139 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 27 (by change 27 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 26 (by change 26 < 64; omega)))
    (comparison_record_at Strict077.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict077.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 10 (by change 10 < 64; omega)),
    cellM0_positive_of_check a139 (boolean_record_at Validity014.checked 57 (by change 57 < 64; omega)), hm.1, hm.2⟩

theorem a140_certificate : ARowCertificate a140 := by
  have hf : ARowFacts a140 := ⟨(boolean_record_at Validity014.checked 59 (by change 59 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt227_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt228_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt241_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds)⟩
  have hm := parent_positive_of_checks a140 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 29 (by change 29 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 28 (by change 28 < 64; omega)))
    (comparison_record_at Strict077.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict077.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 11 (by change 11 < 64; omega)),
    cellM0_positive_of_check a140 (boolean_record_at Validity014.checked 60 (by change 60 < 64; omega)), hm.1, hm.2⟩

theorem a141_certificate : ARowCertificate a141 := by
  have hf : ARowFacts a141 := ⟨(boolean_record_at Validity014.checked 62 (by change 62 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt228_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt229_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt242_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds)⟩
  have hm := parent_positive_of_checks a141 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 31 (by change 31 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 30 (by change 30 < 64; omega)))
    (comparison_record_at Strict077.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict077.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 12 (by change 12 < 64; omega)),
    cellM0_positive_of_check a141 (boolean_record_at Validity014.checked 63 (by change 63 < 64; omega)), hm.1, hm.2⟩

theorem a142_certificate : ARowCertificate a142 := by
  have hf : ARowFacts a142 := ⟨(boolean_record_at Validity015.checked 1 (by change 1 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt229_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt230_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt243_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds)⟩
  have hm := parent_positive_of_checks a142 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 33 (by change 33 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 32 (by change 32 < 64; omega)))
    (comparison_record_at Strict077.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict077.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 13 (by change 13 < 64; omega)),
    cellM0_positive_of_check a142 (boolean_record_at Validity015.checked 2 (by change 2 < 64; omega)), hm.1, hm.2⟩

theorem a143_certificate : ARowCertificate a143 := by
  have hf : ARowFacts a143 := ⟨(boolean_record_at Validity015.checked 4 (by change 4 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt230_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt231_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt244_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds)⟩
  have hm := parent_positive_of_checks a143 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 35 (by change 35 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 34 (by change 34 < 64; omega)))
    (comparison_record_at Strict077.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict077.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 14 (by change 14 < 64; omega)),
    cellM0_positive_of_check a143 (boolean_record_at Validity015.checked 5 (by change 5 < 64; omega)), hm.1, hm.2⟩

theorem a144_certificate : ARowCertificate a144 := by
  have hf : ARowFacts a144 := ⟨(boolean_record_at Validity015.checked 7 (by change 7 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt231_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt232_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt245_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds)⟩
  have hm := parent_positive_of_checks a144 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 37 (by change 37 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 36 (by change 36 < 64; omega)))
    (comparison_record_at Strict077.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict077.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 15 (by change 15 < 64; omega)),
    cellM0_positive_of_check a144 (boolean_record_at Validity015.checked 8 (by change 8 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows018

#check Erdos993Lean.Analytic.V213.P03RowData.ARows018.a137_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows018.a137_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows018.a138_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows018.a138_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows018.a139_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows018.a139_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows018.a140_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows018.a140_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows018.a141_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows018.a141_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows018.a142_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows018.a142_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows018.a143_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows018.a143_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows018.a144_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows018.a144_certificate
