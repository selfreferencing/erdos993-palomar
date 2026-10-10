module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup003
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput001
public import Erdos993Lean.ExactComparisons.F3All.Strict057
public import Erdos993Lean.ExactComparisons.F3All.Strict058
public import Erdos993Lean.ExactComparisons.F3All.Validity008

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CRows004

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem c025_certificate : CRowCertificate c025 := by
  have hf : CRowFacts c025 := ⟨(boolean_record_at Validity008.checked 7 (by change 7 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt028_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt029_facts)⟩
  have hm := face_C_positive_of_checks c025 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 37 (by change 37 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 38 (by change 38 < 64; omega)))
    (comparison_record_at Strict057.checked 13 (by change 13 < 16; omega)) (comparison_record_at Strict057.checked 14 (by change 14 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c026_certificate : CRowCertificate c026 := by
  have hf : CRowFacts c026 := ⟨(boolean_record_at Validity008.checked 8 (by change 8 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt030_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt031_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c026
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 39 (by change 39 < 64; omega))) (comparison_record_at Strict057.checked 15 (by change 15 < 16; omega)))⟩

theorem c027_certificate : CRowCertificate c027 := by
  have hf : CRowFacts c027 := ⟨(boolean_record_at Validity008.checked 9 (by change 9 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt031_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt032_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c027
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 40 (by change 40 < 64; omega))) (comparison_record_at Strict058.checked 0 (by change 0 < 16; omega)))⟩

theorem c028_certificate : CRowCertificate c028 := by
  have hf : CRowFacts c028 := ⟨(boolean_record_at Validity008.checked 10 (by change 10 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt032_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt033_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c028
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 41 (by change 41 < 64; omega))) (comparison_record_at Strict058.checked 1 (by change 1 < 16; omega)))⟩

theorem c029_certificate : CRowCertificate c029 := by
  have hf : CRowFacts c029 := ⟨(boolean_record_at Validity008.checked 11 (by change 11 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt033_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt034_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c029
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 42 (by change 42 < 64; omega))) (comparison_record_at Strict058.checked 2 (by change 2 < 16; omega)))⟩

theorem c030_certificate : CRowCertificate c030 := by
  have hf : CRowFacts c030 := ⟨(boolean_record_at Validity008.checked 12 (by change 12 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt034_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt035_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c030
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 43 (by change 43 < 64; omega))) (comparison_record_at Strict058.checked 3 (by change 3 < 16; omega)))⟩

theorem c031_certificate : CRowCertificate c031 := by
  have hf : CRowFacts c031 := ⟨(boolean_record_at Validity008.checked 13 (by change 13 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt035_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt036_facts)⟩
  have hm := face_C_positive_of_checks c031 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 44 (by change 44 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 45 (by change 45 < 64; omega)))
    (comparison_record_at Strict058.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict058.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c032_certificate : CRowCertificate c032 := by
  have hf : CRowFacts c032 := ⟨(boolean_record_at Validity008.checked 14 (by change 14 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt036_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup003.pt037_facts)⟩
  have hm := face_C_positive_of_checks c032 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 46 (by change 46 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 47 (by change 47 < 64; omega)))
    (comparison_record_at Strict058.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict058.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, Or.inr hm⟩


end Erdos993Lean.Analytic.V213.P03RowData.CRows004

#check Erdos993Lean.Analytic.V213.P03RowData.CRows004.c025_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows004.c025_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows004.c026_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows004.c026_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows004.c027_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows004.c027_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows004.c028_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows004.c028_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows004.c029_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows004.c029_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows004.c030_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows004.c030_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows004.c031_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows004.c031_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows004.c032_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows004.c032_certificate
