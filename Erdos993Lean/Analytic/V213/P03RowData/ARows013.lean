module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup013
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput005
public import Erdos993Lean.ExactComparisons.F3All.Strict071
public import Erdos993Lean.ExactComparisons.F3All.Strict072
public import Erdos993Lean.ExactComparisons.F3All.Validity002
public import Erdos993Lean.ExactComparisons.F3All.Validity012
public import Erdos993Lean.ExactComparisons.F3All.Validity013

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows013

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a097_certificate : ARowCertificate a097 := by
  have hf : ARowFacts a097 := ⟨(boolean_record_at Validity012.checked 58 (by change 58 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt133_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt134_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt196_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e125_bounds)⟩
  have hm := parent_positive_of_checks a097 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 7 (by change 7 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 6 (by change 6 < 64; omega)))
    (comparison_record_at Strict071.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict071.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 32 (by change 32 < 64; omega)),
    cellM0_positive_of_check a097 (boolean_record_at Validity012.checked 59 (by change 59 < 64; omega)), hm.1, hm.2⟩

theorem a098_certificate : ARowCertificate a098 := by
  have hf : ARowFacts a098 := ⟨(boolean_record_at Validity012.checked 61 (by change 61 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt134_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt197_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt198_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e127_bounds)⟩
  have hm := parent_positive_of_checks a098 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 9 (by change 9 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 8 (by change 8 < 64; omega)))
    (comparison_record_at Strict072.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict072.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 33 (by change 33 < 64; omega)),
    cellM0_positive_of_check a098 (boolean_record_at Validity012.checked 62 (by change 62 < 64; omega)), hm.1, hm.2⟩

theorem a099_certificate : ARowCertificate a099 := by
  have hf : ARowFacts a099 := ⟨(boolean_record_at Validity013.checked 0 (by change 0 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt197_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt135_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt199_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e129_bounds)⟩
  have hm := parent_positive_of_checks a099 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 11 (by change 11 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 10 (by change 10 < 64; omega)))
    (comparison_record_at Strict072.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict072.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 34 (by change 34 < 64; omega)),
    cellM0_positive_of_check a099 (boolean_record_at Validity013.checked 1 (by change 1 < 64; omega)), hm.1, hm.2⟩

theorem a100_certificate : ARowCertificate a100 := by
  have hf : ARowFacts a100 := ⟨(boolean_record_at Validity013.checked 3 (by change 3 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt135_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt200_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt201_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e131_bounds)⟩
  have hm := parent_positive_of_checks a100 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 13 (by change 13 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 12 (by change 12 < 64; omega)))
    (comparison_record_at Strict072.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict072.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 35 (by change 35 < 64; omega)),
    cellM0_positive_of_check a100 (boolean_record_at Validity013.checked 4 (by change 4 < 64; omega)), hm.1, hm.2⟩

theorem a101_certificate : ARowCertificate a101 := by
  have hf : ARowFacts a101 := ⟨(boolean_record_at Validity013.checked 6 (by change 6 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt200_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt137_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt202_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e133_bounds)⟩
  have hm := parent_positive_of_checks a101 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 15 (by change 15 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 14 (by change 14 < 64; omega)))
    (comparison_record_at Strict072.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict072.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 36 (by change 36 < 64; omega)),
    cellM0_positive_of_check a101 (boolean_record_at Validity013.checked 7 (by change 7 < 64; omega)), hm.1, hm.2⟩

theorem a102_certificate : ARowCertificate a102 := by
  have hf : ARowFacts a102 := ⟨(boolean_record_at Validity013.checked 9 (by change 9 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt137_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt138_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt203_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e135_bounds)⟩
  have hm := parent_positive_of_checks a102 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 17 (by change 17 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 16 (by change 16 < 64; omega)))
    (comparison_record_at Strict072.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict072.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 37 (by change 37 < 64; omega)),
    cellM0_positive_of_check a102 (boolean_record_at Validity013.checked 10 (by change 10 < 64; omega)), hm.1, hm.2⟩

theorem a103_certificate : ARowCertificate a103 := by
  have hf : ARowFacts a103 := ⟨(boolean_record_at Validity013.checked 12 (by change 12 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt138_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt140_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt204_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e137_bounds)⟩
  have hm := parent_positive_of_checks a103 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 19 (by change 19 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 18 (by change 18 < 64; omega)))
    (comparison_record_at Strict072.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict072.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 38 (by change 38 < 64; omega)),
    cellM0_positive_of_check a103 (boolean_record_at Validity013.checked 13 (by change 13 < 64; omega)), hm.1, hm.2⟩

theorem a104_certificate : ARowCertificate a104 := by
  have hf : ARowFacts a104 := ⟨(boolean_record_at Validity013.checked 15 (by change 15 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt140_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt141_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt205_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e139_bounds)⟩
  have hm := parent_positive_of_checks a104 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 21 (by change 21 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 20 (by change 20 < 64; omega)))
    (comparison_record_at Strict072.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict072.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 39 (by change 39 < 64; omega)),
    cellM0_positive_of_check a104 (boolean_record_at Validity013.checked 16 (by change 16 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows013

#check Erdos993Lean.Analytic.V213.P03RowData.ARows013.a097_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows013.a097_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows013.a098_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows013.a098_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows013.a099_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows013.a099_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows013.a100_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows013.a100_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows013.a101_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows013.a101_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows013.a102_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows013.a102_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows013.a103_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows013.a103_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows013.a104_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows013.a104_certificate
