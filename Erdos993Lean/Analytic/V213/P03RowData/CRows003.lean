module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup002
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput001
public import Erdos993Lean.ExactComparisons.F3All.Strict057
public import Erdos993Lean.ExactComparisons.F3All.Validity007
public import Erdos993Lean.ExactComparisons.F3All.Validity008

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CRows003

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem c017_certificate : CRowCertificate c017 := by
  have hf : CRowFacts c017 := ⟨(boolean_record_at Validity007.checked 63 (by change 63 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt019_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt020_facts)⟩
  have hm := face_C_positive_of_checks c017 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 24 (by change 24 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 25 (by change 25 < 64; omega)))
    (comparison_record_at Strict057.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict057.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c018_certificate : CRowCertificate c018 := by
  have hf : CRowFacts c018 := ⟨(boolean_record_at Validity008.checked 0 (by change 0 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt021_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt022_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c018
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 26 (by change 26 < 64; omega))) (comparison_record_at Strict057.checked 2 (by change 2 < 16; omega)))⟩

theorem c019_certificate : CRowCertificate c019 := by
  have hf : CRowFacts c019 := ⟨(boolean_record_at Validity008.checked 1 (by change 1 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt022_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt023_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c019
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 27 (by change 27 < 64; omega))) (comparison_record_at Strict057.checked 3 (by change 3 < 16; omega)))⟩

theorem c020_certificate : CRowCertificate c020 := by
  have hf : CRowFacts c020 := ⟨(boolean_record_at Validity008.checked 2 (by change 2 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt023_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt024_facts)⟩
  exact ⟨hf, Or.inl (face_L_positive_of_checks c020
    (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 28 (by change 28 < 64; omega))) (comparison_record_at Strict057.checked 4 (by change 4 < 16; omega)))⟩

theorem c021_certificate : CRowCertificate c021 := by
  have hf : CRowFacts c021 := ⟨(boolean_record_at Validity008.checked 3 (by change 3 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt024_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt025_facts)⟩
  have hm := face_C_positive_of_checks c021 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 29 (by change 29 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 30 (by change 30 < 64; omega)))
    (comparison_record_at Strict057.checked 5 (by change 5 < 16; omega)) (comparison_record_at Strict057.checked 6 (by change 6 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c022_certificate : CRowCertificate c022 := by
  have hf : CRowFacts c022 := ⟨(boolean_record_at Validity008.checked 4 (by change 4 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt025_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt026_facts)⟩
  have hm := face_C_positive_of_checks c022 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 31 (by change 31 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 32 (by change 32 < 64; omega)))
    (comparison_record_at Strict057.checked 7 (by change 7 < 16; omega)) (comparison_record_at Strict057.checked 8 (by change 8 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c023_certificate : CRowCertificate c023 := by
  have hf : CRowFacts c023 := ⟨(boolean_record_at Validity008.checked 5 (by change 5 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt026_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt027_facts)⟩
  have hm := face_C_positive_of_checks c023 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 33 (by change 33 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 34 (by change 34 < 64; omega)))
    (comparison_record_at Strict057.checked 9 (by change 9 < 16; omega)) (comparison_record_at Strict057.checked 10 (by change 10 < 16; omega))
  exact ⟨hf, Or.inr hm⟩

theorem c024_certificate : CRowCertificate c024 := by
  have hf : CRowFacts c024 := ⟨(boolean_record_at Validity008.checked 6 (by change 6 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt027_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt028_facts)⟩
  have hm := face_C_positive_of_checks c024 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 35 (by change 35 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput001.checked 36 (by change 36 < 64; omega)))
    (comparison_record_at Strict057.checked 11 (by change 11 < 16; omega)) (comparison_record_at Strict057.checked 12 (by change 12 < 16; omega))
  exact ⟨hf, Or.inr hm⟩


end Erdos993Lean.Analytic.V213.P03RowData.CRows003

#check Erdos993Lean.Analytic.V213.P03RowData.CRows003.c017_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows003.c017_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows003.c018_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows003.c018_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows003.c019_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows003.c019_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows003.c020_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows003.c020_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows003.c021_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows003.c021_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows003.c022_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows003.c022_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows003.c023_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows003.c023_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.CRows003.c024_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CRows003.c024_certificate
