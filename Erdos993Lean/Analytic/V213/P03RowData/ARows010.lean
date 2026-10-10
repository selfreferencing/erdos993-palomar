module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup010
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup011
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput004
public import Erdos993Lean.ExactComparisons.F3All.Strict068
public import Erdos993Lean.ExactComparisons.F3All.Strict069
public import Erdos993Lean.ExactComparisons.F3All.Validity002
public import Erdos993Lean.ExactComparisons.F3All.Validity011
public import Erdos993Lean.ExactComparisons.F3All.Validity012

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows010

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a073_certificate : ARowCertificate a073 := by
  have hf : ARowFacts a073 := ⟨(boolean_record_at Validity011.checked 50 (by change 50 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt158_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt117_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt160_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e046_bounds)⟩
  have hm := parent_positive_of_checks a073 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 23 (by change 23 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 22 (by change 22 < 64; omega)))
    (comparison_record_at Strict068.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict068.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 8 (by change 8 < 64; omega)),
    cellM0_positive_of_check a073 (boolean_record_at Validity011.checked 51 (by change 51 < 64; omega)), hm.1, hm.2⟩

theorem a074_certificate : ARowCertificate a074 := by
  have hf : ARowFacts a074 := ⟨(boolean_record_at Validity011.checked 53 (by change 53 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt117_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt161_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt162_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e048_bounds)⟩
  have hm := parent_positive_of_checks a074 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 25 (by change 25 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 24 (by change 24 < 64; omega)))
    (comparison_record_at Strict069.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict069.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 9 (by change 9 < 64; omega)),
    cellM0_positive_of_check a074 (boolean_record_at Validity011.checked 54 (by change 54 < 64; omega)), hm.1, hm.2⟩

theorem a075_certificate : ARowCertificate a075 := by
  have hf : ARowFacts a075 := ⟨(boolean_record_at Validity011.checked 56 (by change 56 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt161_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt118_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt163_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e051_bounds)⟩
  have hm := parent_positive_of_checks a075 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 27 (by change 27 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 26 (by change 26 < 64; omega)))
    (comparison_record_at Strict069.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict069.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 10 (by change 10 < 64; omega)),
    cellM0_positive_of_check a075 (boolean_record_at Validity011.checked 57 (by change 57 < 64; omega)), hm.1, hm.2⟩

theorem a076_certificate : ARowCertificate a076 := by
  have hf : ARowFacts a076 := ⟨(boolean_record_at Validity011.checked 59 (by change 59 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt118_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt164_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt165_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e055_bounds)⟩
  have hm := parent_positive_of_checks a076 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 29 (by change 29 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 28 (by change 28 < 64; omega)))
    (comparison_record_at Strict069.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict069.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 11 (by change 11 < 64; omega)),
    cellM0_positive_of_check a076 (boolean_record_at Validity011.checked 60 (by change 60 < 64; omega)), hm.1, hm.2⟩

theorem a077_certificate : ARowCertificate a077 := by
  have hf : ARowFacts a077 := ⟨(boolean_record_at Validity011.checked 62 (by change 62 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt164_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt120_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt166_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e058_bounds)⟩
  have hm := parent_positive_of_checks a077 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 31 (by change 31 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 30 (by change 30 < 64; omega)))
    (comparison_record_at Strict069.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict069.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 12 (by change 12 < 64; omega)),
    cellM0_positive_of_check a077 (boolean_record_at Validity011.checked 63 (by change 63 < 64; omega)), hm.1, hm.2⟩

theorem a078_certificate : ARowCertificate a078 := by
  have hf : ARowFacts a078 := ⟨(boolean_record_at Validity012.checked 1 (by change 1 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt120_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt167_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt168_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e063_bounds)⟩
  have hm := parent_positive_of_checks a078 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 33 (by change 33 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 32 (by change 32 < 64; omega)))
    (comparison_record_at Strict069.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict069.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 13 (by change 13 < 64; omega)),
    cellM0_positive_of_check a078 (boolean_record_at Validity012.checked 2 (by change 2 < 64; omega)), hm.1, hm.2⟩

theorem a079_certificate : ARowCertificate a079 := by
  have hf : ARowFacts a079 := ⟨(boolean_record_at Validity012.checked 4 (by change 4 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt167_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt121_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt169_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e069_bounds)⟩
  have hm := parent_positive_of_checks a079 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 35 (by change 35 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 34 (by change 34 < 64; omega)))
    (comparison_record_at Strict069.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict069.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 14 (by change 14 < 64; omega)),
    cellM0_positive_of_check a079 (boolean_record_at Validity012.checked 5 (by change 5 < 64; omega)), hm.1, hm.2⟩

theorem a080_certificate : ARowCertificate a080 := by
  have hf : ARowFacts a080 := ⟨(boolean_record_at Validity012.checked 7 (by change 7 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt121_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt170_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt171_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e073_bounds)⟩
  have hm := parent_positive_of_checks a080 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 37 (by change 37 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 36 (by change 36 < 64; omega)))
    (comparison_record_at Strict069.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict069.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 15 (by change 15 < 64; omega)),
    cellM0_positive_of_check a080 (boolean_record_at Validity012.checked 8 (by change 8 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows010

#check Erdos993Lean.Analytic.V213.P03RowData.ARows010.a073_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows010.a073_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows010.a074_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows010.a074_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows010.a075_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows010.a075_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows010.a076_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows010.a076_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows010.a077_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows010.a077_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows010.a078_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows010.a078_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows010.a079_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows010.a079_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows010.a080_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows010.a080_certificate
