module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup001
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput001
public import Erdos993Lean.ExactComparisons.F3All.Strict055
public import Erdos993Lean.ExactComparisons.F3All.Strict056
public import Erdos993Lean.ExactComparisons.F3All.Validity007

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CRows001

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem c001_certificate : CRowCertificate c001 := by
  have hf : CRowFacts c001 := ⟨(boolean_record_at Validity007.checked 47 (by change 47 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt001_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt002_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c001
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 0 (by change 0 < 64; omega))) (comparison_record_at Strict055.checked 8 (by change 8 < 16; omega)))⟩

theorem c002_certificate : CRowCertificate c002 := by
  have hf : CRowFacts c002 := ⟨(boolean_record_at Validity007.checked 48 (by change 48 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt002_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt003_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c002
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 1 (by change 1 < 64; omega))) (comparison_record_at Strict055.checked 9 (by change 9 < 16; omega)))⟩

theorem c003_certificate : CRowCertificate c003 := by
  have hf : CRowFacts c003 := ⟨(boolean_record_at Validity007.checked 49 (by change 49 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt003_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt004_facts)⟩
  have hm := face_C_positive_of_checks c003 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 2 (by change 2 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 3 (by change 3 < 64; omega)))
    (comparison_record_at Strict055.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict055.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c004_certificate : CRowCertificate c004 := by
  have hf : CRowFacts c004 := ⟨(boolean_record_at Validity007.checked 50 (by change 50 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt004_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt005_facts)⟩
  have hm := face_C_positive_of_checks c004 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 4 (by change 4 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 5 (by change 5 < 64; omega)))
    (comparison_record_at Strict055.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict055.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c005_certificate : CRowCertificate c005 := by
  have hf : CRowFacts c005 := ⟨(boolean_record_at Validity007.checked 51 (by change 51 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt005_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt006_facts)⟩
  have hm := face_C_positive_of_checks c005 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 6 (by change 6 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 7 (by change 7 < 64; omega)))
    (comparison_record_at Strict055.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict055.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c006_certificate : CRowCertificate c006 := by
  have hf : CRowFacts c006 := ⟨(boolean_record_at Validity007.checked 52 (by change 52 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt006_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt007_facts)⟩
  have hm := face_C_positive_of_checks c006 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 8 (by change 8 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 9 (by change 9 < 64; omega)))
    (comparison_record_at Strict056.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict056.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c007_certificate : CRowCertificate c007 := by
  have hf : CRowFacts c007 := ⟨(boolean_record_at Validity007.checked 53 (by change 53 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt008_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt009_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c007
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 10 (by change 10 < 64; omega))) (comparison_record_at Strict056.checked 2 (by change 2 < 16; omega)))⟩

theorem c008_certificate : CRowCertificate c008 := by
  have hf : CRowFacts c008 := ⟨(boolean_record_at Validity007.checked 54 (by change 54 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt009_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt010_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c008
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 11 (by change 11 < 64; omega))) (comparison_record_at Strict056.checked 3 (by change 3 < 16; omega)))⟩


end Erdos993Lean.Analytic.V213.P03RowData.CRows001

#check Erdos993Lean.Analytic.V213.P03RowData.CRows001.c001_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows001.c001_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows001.c002_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows001.c002_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows001.c003_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows001.c003_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows001.c004_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows001.c004_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows001.c005_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows001.c005_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows001.c006_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows001.c006_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows001.c007_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows001.c007_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows001.c008_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows001.c008_certificate
