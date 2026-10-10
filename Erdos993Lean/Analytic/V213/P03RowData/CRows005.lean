module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup003
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput001
public import Erdos993Lean.ExactComparisons.F3All.Strict058
public import Erdos993Lean.ExactComparisons.F3All.Strict059
public import Erdos993Lean.ExactComparisons.F3All.Validity008

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CRows005

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem c033_certificate : CRowCertificate c033 := by
  have hf : CRowFacts c033 := ⟨(boolean_record_at Validity008.checked 15 (by change 15 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt037_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt038_facts)⟩
  have hm := face_C_positive_of_checks c033 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 48 (by change 48 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 49 (by change 49 < 64; omega)))
    (comparison_record_at Strict058.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict058.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c034_certificate : CRowCertificate c034 := by
  have hf : CRowFacts c034 := ⟨(boolean_record_at Validity008.checked 16 (by change 16 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt038_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt039_facts)⟩
  have hm := face_C_positive_of_checks c034 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 50 (by change 50 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 51 (by change 51 < 64; omega)))
    (comparison_record_at Strict058.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict058.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c035_certificate : CRowCertificate c035 := by
  have hf : CRowFacts c035 := ⟨(boolean_record_at Validity008.checked 17 (by change 17 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt039_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt040_facts)⟩
  have hm := face_C_positive_of_checks c035 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 52 (by change 52 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 53 (by change 53 < 64; omega)))
    (comparison_record_at Strict058.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict058.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c036_certificate : CRowCertificate c036 := by
  have hf : CRowFacts c036 := ⟨(boolean_record_at Validity008.checked 18 (by change 18 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt040_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt041_facts)⟩
  have hm := face_C_positive_of_checks c036 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 54 (by change 54 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 55 (by change 55 < 64; omega)))
    (comparison_record_at Strict058.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict058.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c037_certificate : CRowCertificate c037 := by
  have hf : CRowFacts c037 := ⟨(boolean_record_at Validity008.checked 19 (by change 19 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt041_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt042_facts)⟩
  have hm := face_C_positive_of_checks c037 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 56 (by change 56 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 57 (by change 57 < 64; omega)))
    (comparison_record_at Strict059.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict059.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c038_certificate : CRowCertificate c038 := by
  have hf : CRowFacts c038 := ⟨(boolean_record_at Validity008.checked 20 (by change 20 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt042_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt043_facts)⟩
  have hm := face_C_positive_of_checks c038 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 58 (by change 58 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 59 (by change 59 < 64; omega)))
    (comparison_record_at Strict059.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict059.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c039_certificate : CRowCertificate c039 := by
  have hf : CRowFacts c039 := ⟨(boolean_record_at Validity008.checked 21 (by change 21 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt043_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt044_facts)⟩
  have hm := face_C_positive_of_checks c039 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 60 (by change 60 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 61 (by change 61 < 64; omega)))
    (comparison_record_at Strict059.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict059.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c040_certificate : CRowCertificate c040 := by
  have hf : CRowFacts c040 := ⟨(boolean_record_at Validity008.checked 22 (by change 22 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt044_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt045_facts)⟩
  have hm := face_C_positive_of_checks c040 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 62 (by change 62 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 63 (by change 63 < 64; omega)))
    (comparison_record_at Strict059.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict059.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, Or.inr hm⟩


end Erdos993Lean.Analytic.V213.P03RowData.CRows005

#check Erdos993Lean.Analytic.V213.P03RowData.CRows005.c033_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows005.c033_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows005.c034_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows005.c034_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows005.c035_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows005.c035_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows005.c036_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows005.c036_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows005.c037_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows005.c037_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows005.c038_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows005.c038_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows005.c039_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows005.c039_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows005.c040_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows005.c040_certificate
