module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup015
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup016
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput006
public import Erdos993Lean.ExactComparisons.F3All.Strict077
public import Erdos993Lean.ExactComparisons.F3All.Strict078
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity015

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows019

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a145_certificate : ARowCertificate a145 := by
  have hf : ARowFacts a145 := ⟨(boolean_record_at Validity015.checked 10 (by change 10 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt232_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt233_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt246_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds)⟩
  have hm := parent_positive_of_checks a145 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 39 (by change 39 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 38 (by change 38 < 64; omega)))
    (comparison_record_at Strict077.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict077.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 16 (by change 16 < 64; omega)),
    cellM0_positive_of_check a145 (boolean_record_at Validity015.checked 11 (by change 11 < 64; omega)), hm.1, hm.2⟩

theorem a146_certificate : ARowCertificate a146 := by
  have hf : ARowFacts a146 := ⟨(boolean_record_at Validity015.checked 13 (by change 13 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt233_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt234_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt247_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e135_bounds)⟩
  have hm := parent_positive_of_checks a146 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 41 (by change 41 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 40 (by change 40 < 64; omega)))
    (comparison_record_at Strict078.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict078.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 17 (by change 17 < 64; omega)),
    cellM0_positive_of_check a146 (boolean_record_at Validity015.checked 14 (by change 14 < 64; omega)), hm.1, hm.2⟩

theorem a147_certificate : ARowCertificate a147 := by
  have hf : ARowFacts a147 := ⟨(boolean_record_at Validity015.checked 16 (by change 16 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt234_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt235_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt248_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e137_bounds)⟩
  have hm := parent_positive_of_checks a147 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 43 (by change 43 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 42 (by change 42 < 64; omega)))
    (comparison_record_at Strict078.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict078.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 18 (by change 18 < 64; omega)),
    cellM0_positive_of_check a147 (boolean_record_at Validity015.checked 17 (by change 17 < 64; omega)), hm.1, hm.2⟩

theorem a148_certificate : ARowCertificate a148 := by
  have hf : ARowFacts a148 := ⟨(boolean_record_at Validity015.checked 19 (by change 19 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt235_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt236_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt249_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e139_bounds)⟩
  have hm := parent_positive_of_checks a148 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 45 (by change 45 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 44 (by change 44 < 64; omega)))
    (comparison_record_at Strict078.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict078.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 19 (by change 19 < 64; omega)),
    cellM0_positive_of_check a148 (boolean_record_at Validity015.checked 20 (by change 20 < 64; omega)), hm.1, hm.2⟩

theorem a149_certificate : ARowCertificate a149 := by
  have hf : ARowFacts a149 := ⟨(boolean_record_at Validity015.checked 22 (by change 22 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup002.pt021_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt237_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt250_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds)⟩
  have hm := parent_positive_of_checks a149 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 47 (by change 47 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 46 (by change 46 < 64; omega)))
    (comparison_record_at Strict078.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict078.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 20 (by change 20 < 64; omega)),
    cellM0_positive_of_check a149 (boolean_record_at Validity015.checked 23 (by change 23 < 64; omega)), hm.1, hm.2⟩

theorem a150_certificate : ARowCertificate a150 := by
  have hf : ARowFacts a150 := ⟨(boolean_record_at Validity015.checked 25 (by change 25 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt237_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt239_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt251_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e029_bounds)⟩
  have hm := parent_positive_of_checks a150 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 49 (by change 49 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 48 (by change 48 < 64; omega)))
    (comparison_record_at Strict078.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict078.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 21 (by change 21 < 64; omega)),
    cellM0_positive_of_check a150 (boolean_record_at Validity015.checked 26 (by change 26 < 64; omega)), hm.1, hm.2⟩

theorem a151_certificate : ARowCertificate a151 := by
  have hf : ARowFacts a151 := ⟨(boolean_record_at Validity015.checked 28 (by change 28 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt239_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt241_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt252_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e088_bounds)⟩
  have hm := parent_positive_of_checks a151 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 51 (by change 51 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 50 (by change 50 < 64; omega)))
    (comparison_record_at Strict078.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict078.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 22 (by change 22 < 64; omega)),
    cellM0_positive_of_check a151 (boolean_record_at Validity015.checked 29 (by change 29 < 64; omega)), hm.1, hm.2⟩

theorem a152_certificate : ARowCertificate a152 := by
  have hf : ARowFacts a152 := ⟨(boolean_record_at Validity015.checked 31 (by change 31 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt241_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt242_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt253_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds)⟩
  have hm := parent_positive_of_checks a152 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 53 (by change 53 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 52 (by change 52 < 64; omega)))
    (comparison_record_at Strict078.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict078.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 23 (by change 23 < 64; omega)),
    cellM0_positive_of_check a152 (boolean_record_at Validity015.checked 32 (by change 32 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows019

#check Erdos993Lean.Analytic.V213.P03RowData.ARows019.a145_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows019.a145_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows019.a146_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows019.a146_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows019.a147_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows019.a147_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows019.a148_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows019.a148_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows019.a149_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows019.a149_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows019.a150_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows019.a150_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows019.a151_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows019.a151_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows019.a152_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows019.a152_certificate
