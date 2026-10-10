module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup010
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput003
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput004
public import Erdos993Lean.ExactComparisons.F3All.Strict066
public import Erdos993Lean.ExactComparisons.F3All.Strict067
public import Erdos993Lean.ExactComparisons.F3All.Validity001
public import Erdos993Lean.ExactComparisons.F3All.Validity011

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows008

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a057_certificate : ARowCertificate a057 := by
  have hf : ARowFacts a057 := ⟨(boolean_record_at Validity011.checked 2 (by change 2 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt101_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt136_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt137_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds)⟩
  have hm := parent_positive_of_checks a057 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 55 (by change 55 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 54 (by change 54 < 64; omega)))
    (comparison_record_at Strict066.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict066.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 56 (by change 56 < 64; omega)),
    cellM0_positive_of_check a057 (boolean_record_at Validity011.checked 3 (by change 3 < 64; omega)), hm.1, hm.2⟩

theorem a058_certificate : ARowCertificate a058 := by
  have hf : ARowFacts a058 := ⟨(boolean_record_at Validity011.checked 5 (by change 5 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt136_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt102_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt138_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e135_bounds)⟩
  have hm := parent_positive_of_checks a058 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 57 (by change 57 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 56 (by change 56 < 64; omega)))
    (comparison_record_at Strict067.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict067.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 57 (by change 57 < 64; omega)),
    cellM0_positive_of_check a058 (boolean_record_at Validity011.checked 6 (by change 6 < 64; omega)), hm.1, hm.2⟩

theorem a059_certificate : ARowCertificate a059 := by
  have hf : ARowFacts a059 := ⟨(boolean_record_at Validity011.checked 8 (by change 8 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt102_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt139_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt140_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e137_bounds)⟩
  have hm := parent_positive_of_checks a059 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 59 (by change 59 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 58 (by change 58 < 64; omega)))
    (comparison_record_at Strict067.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict067.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 58 (by change 58 < 64; omega)),
    cellM0_positive_of_check a059 (boolean_record_at Validity011.checked 9 (by change 9 < 64; omega)), hm.1, hm.2⟩

theorem a060_certificate : ARowCertificate a060 := by
  have hf : ARowFacts a060 := ⟨(boolean_record_at Validity011.checked 11 (by change 11 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt139_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt103_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt141_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e139_bounds)⟩
  have hm := parent_positive_of_checks a060 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 61 (by change 61 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 60 (by change 60 < 64; omega)))
    (comparison_record_at Strict067.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict067.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 59 (by change 59 < 64; omega)),
    cellM0_positive_of_check a060 (boolean_record_at Validity011.checked 12 (by change 12 < 64; omega)), hm.1, hm.2⟩

theorem a061_certificate : ARowCertificate a061 := by
  have hf : ARowFacts a061 := ⟨(boolean_record_at Validity011.checked 14 (by change 14 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt142_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt107_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt143_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds)⟩
  have hm := parent_positive_of_checks a061 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 63 (by change 63 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 62 (by change 62 < 64; omega)))
    (comparison_record_at Strict067.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict067.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 60 (by change 60 < 64; omega)),
    cellM0_positive_of_check a061 (boolean_record_at Validity011.checked 15 (by change 15 < 64; omega)), hm.1, hm.2⟩

theorem a062_certificate : ARowCertificate a062 := by
  have hf : ARowFacts a062 := ⟨(boolean_record_at Validity011.checked 17 (by change 17 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt107_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt108_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt144_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e014_bounds)⟩
  have hm := parent_positive_of_checks a062 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 1 (by change 1 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 0 (by change 0 < 64; omega)))
    (comparison_record_at Strict067.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict067.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 61 (by change 61 < 64; omega)),
    cellM0_positive_of_check a062 (boolean_record_at Validity011.checked 18 (by change 18 < 64; omega)), hm.1, hm.2⟩

theorem a063_certificate : ARowCertificate a063 := by
  have hf : ARowFacts a063 := ⟨(boolean_record_at Validity011.checked 20 (by change 20 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt108_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt109_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt145_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e017_bounds)⟩
  have hm := parent_positive_of_checks a063 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 3 (by change 3 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 2 (by change 2 < 64; omega)))
    (comparison_record_at Strict067.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict067.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 62 (by change 62 < 64; omega)),
    cellM0_positive_of_check a063 (boolean_record_at Validity011.checked 21 (by change 21 < 64; omega)), hm.1, hm.2⟩

theorem a064_certificate : ARowCertificate a064 := by
  have hf : ARowFacts a064 := ⟨(boolean_record_at Validity011.checked 23 (by change 23 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt109_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt146_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt147_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e020_bounds)⟩
  have hm := parent_positive_of_checks a064 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 5 (by change 5 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 4 (by change 4 < 64; omega)))
    (comparison_record_at Strict067.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict067.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 63 (by change 63 < 64; omega)),
    cellM0_positive_of_check a064 (boolean_record_at Validity011.checked 24 (by change 24 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows008

#check Erdos993Lean.Analytic.V213.P03RowData.ARows008.a057_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows008.a057_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows008.a058_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows008.a058_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows008.a059_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows008.a059_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows008.a060_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows008.a060_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows008.a061_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows008.a061_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows008.a062_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows008.a062_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows008.a063_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows008.a063_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows008.a064_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows008.a064_certificate
