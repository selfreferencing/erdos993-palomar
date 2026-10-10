module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup014
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup015
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput006
public import Erdos993Lean.ExactComparisons.F3All.Strict075
public import Erdos993Lean.ExactComparisons.F3All.Strict076
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity014

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows017

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a129_certificate : ARowCertificate a129 := by
  have hf : ARowFacts a129 := ⟨(boolean_record_at Validity014.checked 26 (by change 26 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt215_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt217_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt230_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds)⟩
  have hm := parent_positive_of_checks a129 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 7 (by change 7 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 6 (by change 6 < 64; omega)))
    (comparison_record_at Strict075.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict075.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 0 (by change 0 < 64; omega)),
    cellM0_positive_of_check a129 (boolean_record_at Validity014.checked 27 (by change 27 < 64; omega)), hm.1, hm.2⟩

theorem a130_certificate : ARowCertificate a130 := by
  have hf : ARowFacts a130 := ⟨(boolean_record_at Validity014.checked 29 (by change 29 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt217_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt218_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt231_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds)⟩
  have hm := parent_positive_of_checks a130 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 9 (by change 9 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 8 (by change 8 < 64; omega)))
    (comparison_record_at Strict076.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict076.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 1 (by change 1 < 64; omega)),
    cellM0_positive_of_check a130 (boolean_record_at Validity014.checked 30 (by change 30 < 64; omega)), hm.1, hm.2⟩

theorem a131_certificate : ARowCertificate a131 := by
  have hf : ARowFacts a131 := ⟨(boolean_record_at Validity014.checked 32 (by change 32 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt218_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt219_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt232_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds)⟩
  have hm := parent_positive_of_checks a131 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 11 (by change 11 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 10 (by change 10 < 64; omega)))
    (comparison_record_at Strict076.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict076.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 2 (by change 2 < 64; omega)),
    cellM0_positive_of_check a131 (boolean_record_at Validity014.checked 33 (by change 33 < 64; omega)), hm.1, hm.2⟩

theorem a132_certificate : ARowCertificate a132 := by
  have hf : ARowFacts a132 := ⟨(boolean_record_at Validity014.checked 35 (by change 35 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt219_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt220_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt233_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds)⟩
  have hm := parent_positive_of_checks a132 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 13 (by change 13 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 12 (by change 12 < 64; omega)))
    (comparison_record_at Strict076.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict076.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 3 (by change 3 < 64; omega)),
    cellM0_positive_of_check a132 (boolean_record_at Validity014.checked 36 (by change 36 < 64; omega)), hm.1, hm.2⟩

theorem a133_certificate : ARowCertificate a133 := by
  have hf : ARowFacts a133 := ⟨(boolean_record_at Validity014.checked 38 (by change 38 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt220_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt221_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt234_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e135_bounds)⟩
  have hm := parent_positive_of_checks a133 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 15 (by change 15 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 14 (by change 14 < 64; omega)))
    (comparison_record_at Strict076.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict076.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 4 (by change 4 < 64; omega)),
    cellM0_positive_of_check a133 (boolean_record_at Validity014.checked 39 (by change 39 < 64; omega)), hm.1, hm.2⟩

theorem a134_certificate : ARowCertificate a134 := by
  have hf : ARowFacts a134 := ⟨(boolean_record_at Validity014.checked 41 (by change 41 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt221_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt222_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt235_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e137_bounds)⟩
  have hm := parent_positive_of_checks a134 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 17 (by change 17 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 16 (by change 16 < 64; omega)))
    (comparison_record_at Strict076.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict076.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 5 (by change 5 < 64; omega)),
    cellM0_positive_of_check a134 (boolean_record_at Validity014.checked 42 (by change 42 < 64; omega)), hm.1, hm.2⟩

theorem a135_certificate : ARowCertificate a135 := by
  have hf : ARowFacts a135 := ⟨(boolean_record_at Validity014.checked 44 (by change 44 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt222_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt223_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt236_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e139_bounds)⟩
  have hm := parent_positive_of_checks a135 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 19 (by change 19 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 18 (by change 18 < 64; omega)))
    (comparison_record_at Strict076.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict076.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 6 (by change 6 < 64; omega)),
    cellM0_positive_of_check a135 (boolean_record_at Validity014.checked 45 (by change 45 < 64; omega)), hm.1, hm.2⟩

theorem a136_certificate : ARowCertificate a136 := by
  have hf : ARowFacts a136 := ⟨(boolean_record_at Validity014.checked 47 (by change 47 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt014_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt224_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt237_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds)⟩
  have hm := parent_positive_of_checks a136 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 21 (by change 21 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 20 (by change 20 < 64; omega)))
    (comparison_record_at Strict076.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict076.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 7 (by change 7 < 64; omega)),
    cellM0_positive_of_check a136 (boolean_record_at Validity014.checked 48 (by change 48 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows017

#check Erdos993Lean.Analytic.V213.P03RowData.ARows017.a129_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows017.a129_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows017.a130_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows017.a130_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows017.a131_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows017.a131_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows017.a132_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows017.a132_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows017.a133_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows017.a133_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows017.a134_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows017.a134_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows017.a135_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows017.a135_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows017.a136_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows017.a136_certificate
