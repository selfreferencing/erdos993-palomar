module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup010
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput004
public import Erdos993Lean.ExactComparisons.F3All.Strict067
public import Erdos993Lean.ExactComparisons.F3All.Strict068
public import Erdos993Lean.ExactComparisons.F3All.Validity002
public import Erdos993Lean.ExactComparisons.F3All.Validity011

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows009

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a065_certificate : ARowCertificate a065 := by
  have hf : ARowFacts a065 := ⟨(boolean_record_at Validity011.checked 26 (by change 26 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt146_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt111_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt148_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e022_bounds)⟩
  have hm := parent_positive_of_checks a065 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 7 (by change 7 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 6 (by change 6 < 64; omega)))
    (comparison_record_at Strict067.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict067.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 0 (by change 0 < 64; omega)),
    cellM0_positive_of_check a065 (boolean_record_at Validity011.checked 27 (by change 27 < 64; omega)), hm.1, hm.2⟩

theorem a066_certificate : ARowCertificate a066 := by
  have hf : ARowFacts a066 := ⟨(boolean_record_at Validity011.checked 29 (by change 29 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt111_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt149_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt150_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e025_bounds)⟩
  have hm := parent_positive_of_checks a066 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 9 (by change 9 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 8 (by change 8 < 64; omega)))
    (comparison_record_at Strict068.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict068.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 1 (by change 1 < 64; omega)),
    cellM0_positive_of_check a066 (boolean_record_at Validity011.checked 30 (by change 30 < 64; omega)), hm.1, hm.2⟩

theorem a067_certificate : ARowCertificate a067 := by
  have hf : ARowFacts a067 := ⟨(boolean_record_at Validity011.checked 32 (by change 32 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt149_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt112_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt151_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e028_bounds)⟩
  have hm := parent_positive_of_checks a067 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 11 (by change 11 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 10 (by change 10 < 64; omega)))
    (comparison_record_at Strict068.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict068.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 2 (by change 2 < 64; omega)),
    cellM0_positive_of_check a067 (boolean_record_at Validity011.checked 33 (by change 33 < 64; omega)), hm.1, hm.2⟩

theorem a068_certificate : ARowCertificate a068 := by
  have hf : ARowFacts a068 := ⟨(boolean_record_at Validity011.checked 35 (by change 35 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt112_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt152_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt153_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e030_bounds)⟩
  have hm := parent_positive_of_checks a068 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 13 (by change 13 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 12 (by change 12 < 64; omega)))
    (comparison_record_at Strict068.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict068.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 3 (by change 3 < 64; omega)),
    cellM0_positive_of_check a068 (boolean_record_at Validity011.checked 36 (by change 36 < 64; omega)), hm.1, hm.2⟩

theorem a069_certificate : ARowCertificate a069 := by
  have hf : ARowFacts a069 := ⟨(boolean_record_at Validity011.checked 38 (by change 38 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt152_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt114_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt154_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e032_bounds)⟩
  have hm := parent_positive_of_checks a069 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 15 (by change 15 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 14 (by change 14 < 64; omega)))
    (comparison_record_at Strict068.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict068.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 4 (by change 4 < 64; omega)),
    cellM0_positive_of_check a069 (boolean_record_at Validity011.checked 39 (by change 39 < 64; omega)), hm.1, hm.2⟩

theorem a070_certificate : ARowCertificate a070 := by
  have hf : ARowFacts a070 := ⟨(boolean_record_at Validity011.checked 41 (by change 41 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt114_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt155_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt156_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e035_bounds)⟩
  have hm := parent_positive_of_checks a070 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 17 (by change 17 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 16 (by change 16 < 64; omega)))
    (comparison_record_at Strict068.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict068.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 5 (by change 5 < 64; omega)),
    cellM0_positive_of_check a070 (boolean_record_at Validity011.checked 42 (by change 42 < 64; omega)), hm.1, hm.2⟩

theorem a071_certificate : ARowCertificate a071 := by
  have hf : ARowFacts a071 := ⟨(boolean_record_at Validity011.checked 44 (by change 44 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt155_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt115_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt157_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e039_bounds)⟩
  have hm := parent_positive_of_checks a071 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 19 (by change 19 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 18 (by change 18 < 64; omega)))
    (comparison_record_at Strict068.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict068.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 6 (by change 6 < 64; omega)),
    cellM0_positive_of_check a071 (boolean_record_at Validity011.checked 45 (by change 45 < 64; omega)), hm.1, hm.2⟩

theorem a072_certificate : ARowCertificate a072 := by
  have hf : ARowFacts a072 := ⟨(boolean_record_at Validity011.checked 47 (by change 47 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt115_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt158_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt159_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e041_bounds)⟩
  have hm := parent_positive_of_checks a072 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 21 (by change 21 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 20 (by change 20 < 64; omega)))
    (comparison_record_at Strict068.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict068.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 7 (by change 7 < 64; omega)),
    cellM0_positive_of_check a072 (boolean_record_at Validity011.checked 48 (by change 48 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows009

#check Erdos993Lean.Analytic.V213.P03RowData.ARows009.a065_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows009.a065_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows009.a066_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows009.a066_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows009.a067_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows009.a067_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows009.a068_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows009.a068_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows009.a069_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows009.a069_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows009.a070_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows009.a070_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows009.a071_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows009.a071_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows009.a072_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows009.a072_certificate
