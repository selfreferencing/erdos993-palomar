module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup007
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput003
public import Erdos993Lean.ExactComparisons.F3All.Strict063
public import Erdos993Lean.ExactComparisons.F3All.Strict064
public import Erdos993Lean.ExactComparisons.F3All.Validity001
public import Erdos993Lean.ExactComparisons.F3All.Validity009
public import Erdos993Lean.ExactComparisons.F3All.Validity010

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows005

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a033_certificate : ARowCertificate a033 := by
  have hf : ARowFacts a033 := ⟨(boolean_record_at Validity009.checked 58 (by change 58 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt077_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt079_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt103_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds)⟩
  have hm := parent_positive_of_checks a033 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 7 (by change 7 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 6 (by change 6 < 64; omega)))
    (comparison_record_at Strict063.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict063.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 32 (by change 32 < 64; omega)),
    cellM0_positive_of_check a033 (boolean_record_at Validity009.checked 59 (by change 59 < 64; omega)), hm.1, hm.2⟩

theorem a034_certificate : ARowCertificate a034 := by
  have hf : ARowFacts a034 := ⟨(boolean_record_at Validity009.checked 61 (by change 61 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt104_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt081_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt105_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e002_bounds)⟩
  have hm := parent_positive_of_checks a034 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 9 (by change 9 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 8 (by change 8 < 64; omega)))
    (comparison_record_at Strict064.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict064.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 33 (by change 33 < 64; omega)),
    cellM0_positive_of_check a034 (boolean_record_at Validity009.checked 62 (by change 62 < 64; omega)), hm.1, hm.2⟩

theorem a035_certificate : ARowCertificate a035 := by
  have hf : ARowFacts a035 := ⟨(boolean_record_at Validity010.checked 0 (by change 0 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt081_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt082_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt106_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e006_bounds)⟩
  have hm := parent_positive_of_checks a035 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 11 (by change 11 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 10 (by change 10 < 64; omega)))
    (comparison_record_at Strict064.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict064.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 34 (by change 34 < 64; omega)),
    cellM0_positive_of_check a035 (boolean_record_at Validity010.checked 1 (by change 1 < 64; omega)), hm.1, hm.2⟩

theorem a036_certificate : ARowCertificate a036 := by
  have hf : ARowFacts a036 := ⟨(boolean_record_at Validity010.checked 3 (by change 3 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt082_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt085_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt107_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e011_bounds)⟩
  have hm := parent_positive_of_checks a036 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 13 (by change 13 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 12 (by change 12 < 64; omega)))
    (comparison_record_at Strict064.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict064.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 35 (by change 35 < 64; omega)),
    cellM0_positive_of_check a036 (boolean_record_at Validity010.checked 4 (by change 4 < 64; omega)), hm.1, hm.2⟩

theorem a037_certificate : ARowCertificate a037 := by
  have hf : ARowFacts a037 := ⟨(boolean_record_at Validity010.checked 6 (by change 6 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt085_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt087_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt108_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e014_bounds)⟩
  have hm := parent_positive_of_checks a037 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 15 (by change 15 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 14 (by change 14 < 64; omega)))
    (comparison_record_at Strict064.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict064.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 36 (by change 36 < 64; omega)),
    cellM0_positive_of_check a037 (boolean_record_at Validity010.checked 7 (by change 7 < 64; omega)), hm.1, hm.2⟩

theorem a038_certificate : ARowCertificate a038 := by
  have hf : ARowFacts a038 := ⟨(boolean_record_at Validity010.checked 9 (by change 9 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt087_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt088_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt109_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e017_bounds)⟩
  have hm := parent_positive_of_checks a038 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 17 (by change 17 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 16 (by change 16 < 64; omega)))
    (comparison_record_at Strict064.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict064.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 37 (by change 37 < 64; omega)),
    cellM0_positive_of_check a038 (boolean_record_at Validity010.checked 10 (by change 10 < 64; omega)), hm.1, hm.2⟩

theorem a039_certificate : ARowCertificate a039 := by
  have hf : ARowFacts a039 := ⟨(boolean_record_at Validity010.checked 12 (by change 12 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt088_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt110_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt111_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e021_bounds)⟩
  have hm := parent_positive_of_checks a039 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 19 (by change 19 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 18 (by change 18 < 64; omega)))
    (comparison_record_at Strict064.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict064.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 38 (by change 38 < 64; omega)),
    cellM0_positive_of_check a039 (boolean_record_at Validity010.checked 13 (by change 13 < 64; omega)), hm.1, hm.2⟩

theorem a040_certificate : ARowCertificate a040 := by
  have hf : ARowFacts a040 := ⟨(boolean_record_at Validity010.checked 15 (by change 15 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt110_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt089_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt112_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e026_bounds)⟩
  have hm := parent_positive_of_checks a040 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 21 (by change 21 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 20 (by change 20 < 64; omega)))
    (comparison_record_at Strict064.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict064.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 39 (by change 39 < 64; omega)),
    cellM0_positive_of_check a040 (boolean_record_at Validity010.checked 16 (by change 16 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows005

#check Erdos993Lean.Analytic.V213.P03RowData.ARows005.a033_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows005.a033_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows005.a034_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows005.a034_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows005.a035_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows005.a035_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows005.a036_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows005.a036_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows005.a037_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows005.a037_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows005.a038_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows005.a038_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows005.a039_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows005.a039_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows005.a040_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows005.a040_certificate
