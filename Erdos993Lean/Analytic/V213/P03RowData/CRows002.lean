module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup002
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput001
public import Erdos993Lean.ExactComparisons.F3All.Strict056
public import Erdos993Lean.ExactComparisons.F3All.Validity007

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CRows002

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem c009_certificate : CRowCertificate c009 := by
  have hf : CRowFacts c009 := ⟨(boolean_record_at Validity007.checked 55 (by change 55 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt010_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt011_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c009
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 12 (by change 12 < 64; omega))) (comparison_record_at Strict056.checked 4 (by change 4 < 16; omega)))⟩

theorem c010_certificate : CRowCertificate c010 := by
  have hf : CRowFacts c010 := ⟨(boolean_record_at Validity007.checked 56 (by change 56 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt011_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt012_facts)⟩
  have hm := face_C_positive_of_checks c010 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 13 (by change 13 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 14 (by change 14 < 64; omega)))
    (comparison_record_at Strict056.checked 5 (by change 5 < 16; omega)) (comparison_record_at Strict056.checked 6 (by change 6 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c011_certificate : CRowCertificate c011 := by
  have hf : CRowFacts c011 := ⟨(boolean_record_at Validity007.checked 57 (by change 57 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt012_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt013_facts)⟩
  have hm := face_C_positive_of_checks c011 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 15 (by change 15 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 16 (by change 16 < 64; omega)))
    (comparison_record_at Strict056.checked 7 (by change 7 < 16; omega)) (comparison_record_at Strict056.checked 8 (by change 8 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c012_certificate : CRowCertificate c012 := by
  have hf : CRowFacts c012 := ⟨(boolean_record_at Validity007.checked 58 (by change 58 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt014_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt015_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c012
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 17 (by change 17 < 64; omega))) (comparison_record_at Strict056.checked 9 (by change 9 < 16; omega)))⟩

theorem c013_certificate : CRowCertificate c013 := by
  have hf : CRowFacts c013 := ⟨(boolean_record_at Validity007.checked 59 (by change 59 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt015_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt016_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c013
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 18 (by change 18 < 64; omega))) (comparison_record_at Strict056.checked 10 (by change 10 < 16; omega)))⟩

theorem c014_certificate : CRowCertificate c014 := by
  have hf : CRowFacts c014 := ⟨(boolean_record_at Validity007.checked 60 (by change 60 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt016_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt017_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c014
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 19 (by change 19 < 64; omega))) (comparison_record_at Strict056.checked 11 (by change 11 < 16; omega)))⟩

theorem c015_certificate : CRowCertificate c015 := by
  have hf : CRowFacts c015 := ⟨(boolean_record_at Validity007.checked 61 (by change 61 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt017_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt018_facts)⟩
  have hm := face_C_positive_of_checks c015 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 20 (by change 20 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 21 (by change 21 < 64; omega)))
    (comparison_record_at Strict056.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict056.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c016_certificate : CRowCertificate c016 := by
  have hf : CRowFacts c016 := ⟨(boolean_record_at Validity007.checked 62 (by change 62 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt018_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt019_facts)⟩
  have hm := face_C_positive_of_checks c016 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 22 (by change 22 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 23 (by change 23 < 64; omega)))
    (comparison_record_at Strict056.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict056.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, Or.inr hm⟩


end Erdos993Lean.Analytic.V213.P03RowData.CRows002

#check Erdos993Lean.Analytic.V213.P03RowData.CRows002.c009_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows002.c009_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows002.c010_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows002.c010_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows002.c011_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows002.c011_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows002.c012_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows002.c012_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows002.c013_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows002.c013_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows002.c014_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows002.c014_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows002.c015_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows002.c015_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows002.c016_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows002.c016_certificate
