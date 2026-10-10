module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup003
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput002
public import Erdos993Lean.ExactComparisons.F3All.Strict059
public import Erdos993Lean.ExactComparisons.F3All.Validity008

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CRows006

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem c041_certificate : CRowCertificate c041 := by
  have hf : CRowFacts c041 := ⟨(boolean_record_at Validity008.checked 23 (by change 23 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt045_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt046_facts)⟩
  have hm := face_C_positive_of_checks c041 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 0 (by change 0 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 1 (by change 1 < 64; omega)))
    (comparison_record_at Strict059.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict059.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c042_certificate : CRowCertificate c042 := by
  have hf : CRowFacts c042 := ⟨(boolean_record_at Validity008.checked 24 (by change 24 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt046_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt047_facts)⟩
  have hm := face_C_positive_of_checks c042 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 2 (by change 2 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 3 (by change 3 < 64; omega)))
    (comparison_record_at Strict059.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict059.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c043_certificate : CRowCertificate c043 := by
  have hf : CRowFacts c043 := ⟨(boolean_record_at Validity008.checked 25 (by change 25 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt047_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt048_facts)⟩
  have hm := face_C_positive_of_checks c043 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 4 (by change 4 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 5 (by change 5 < 64; omega)))
    (comparison_record_at Strict059.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict059.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, Or.inr hm⟩


end Erdos993Lean.Analytic.V213.P03RowData.CRows006

#check Erdos993Lean.Analytic.V213.P03RowData.CRows006.c041_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows006.c041_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows006.c042_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows006.c042_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows006.c043_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows006.c043_certificate
