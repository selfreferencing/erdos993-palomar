module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup008
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput003
public import Erdos993Lean.ExactComparisons.F3All.Strict064
public import Erdos993Lean.ExactComparisons.F3All.Strict065
public import Erdos993Lean.ExactComparisons.F3All.Validity001
public import Erdos993Lean.ExactComparisons.F3All.Validity010

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows006

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a041_certificate : ARowCertificate a041 := by
  have hf : ARowFacts a041 := ⟨(boolean_record_at Validity010.checked 18 (by change 18 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt089_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt113_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt114_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e031_bounds)⟩
  have hm := parent_positive_of_checks a041 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 23 (by change 23 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 22 (by change 22 < 64; omega)))
    (comparison_record_at Strict064.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict064.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 40 (by change 40 < 64; omega)),
    cellM0_positive_of_check a041 (boolean_record_at Validity010.checked 19 (by change 19 < 64; omega)), hm.1, hm.2⟩

theorem a042_certificate : ARowCertificate a042 := by
  have hf : ARowFacts a042 := ⟨(boolean_record_at Validity010.checked 21 (by change 21 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt113_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt091_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt115_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e037_bounds)⟩
  have hm := parent_positive_of_checks a042 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 25 (by change 25 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 24 (by change 24 < 64; omega)))
    (comparison_record_at Strict065.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict065.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 41 (by change 41 < 64; omega)),
    cellM0_positive_of_check a042 (boolean_record_at Validity010.checked 22 (by change 22 < 64; omega)), hm.1, hm.2⟩

theorem a043_certificate : ARowCertificate a043 := by
  have hf : ARowFacts a043 := ⟨(boolean_record_at Validity010.checked 24 (by change 24 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt091_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt116_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt117_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e042_bounds)⟩
  have hm := parent_positive_of_checks a043 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 27 (by change 27 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 26 (by change 26 < 64; omega)))
    (comparison_record_at Strict065.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict065.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 42 (by change 42 < 64; omega)),
    cellM0_positive_of_check a043 (boolean_record_at Validity010.checked 25 (by change 25 < 64; omega)), hm.1, hm.2⟩

theorem a044_certificate : ARowCertificate a044 := by
  have hf : ARowFacts a044 := ⟨(boolean_record_at Validity010.checked 27 (by change 27 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt116_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt092_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt118_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e049_bounds)⟩
  have hm := parent_positive_of_checks a044 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 29 (by change 29 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 28 (by change 28 < 64; omega)))
    (comparison_record_at Strict065.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict065.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 43 (by change 43 < 64; omega)),
    cellM0_positive_of_check a044 (boolean_record_at Validity010.checked 28 (by change 28 < 64; omega)), hm.1, hm.2⟩

theorem a045_certificate : ARowCertificate a045 := by
  have hf : ARowFacts a045 := ⟨(boolean_record_at Validity010.checked 30 (by change 30 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt092_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt119_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt120_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e057_bounds)⟩
  have hm := parent_positive_of_checks a045 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 31 (by change 31 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 30 (by change 30 < 64; omega)))
    (comparison_record_at Strict065.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict065.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 44 (by change 44 < 64; omega)),
    cellM0_positive_of_check a045 (boolean_record_at Validity010.checked 31 (by change 31 < 64; omega)), hm.1, hm.2⟩

theorem a046_certificate : ARowCertificate a046 := by
  have hf : ARowFacts a046 := ⟨(boolean_record_at Validity010.checked 33 (by change 33 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt119_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt094_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt121_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e065_bounds)⟩
  have hm := parent_positive_of_checks a046 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 33 (by change 33 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 32 (by change 32 < 64; omega)))
    (comparison_record_at Strict065.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict065.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 45 (by change 45 < 64; omega)),
    cellM0_positive_of_check a046 (boolean_record_at Validity010.checked 34 (by change 34 < 64; omega)), hm.1, hm.2⟩

theorem a047_certificate : ARowCertificate a047 := by
  have hf : ARowFacts a047 := ⟨(boolean_record_at Validity010.checked 36 (by change 36 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt094_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt095_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt122_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e081_bounds)⟩
  have hm := parent_positive_of_checks a047 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 35 (by change 35 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 34 (by change 34 < 64; omega)))
    (comparison_record_at Strict065.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict065.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 46 (by change 46 < 64; omega)),
    cellM0_positive_of_check a047 (boolean_record_at Validity010.checked 37 (by change 37 < 64; omega)), hm.1, hm.2⟩

theorem a048_certificate : ARowCertificate a048 := by
  have hf : ARowFacts a048 := ⟨(boolean_record_at Validity010.checked 39 (by change 39 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt095_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt123_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt124_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e093_bounds)⟩
  have hm := parent_positive_of_checks a048 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 37 (by change 37 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 36 (by change 36 < 64; omega)))
    (comparison_record_at Strict065.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict065.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 47 (by change 47 < 64; omega)),
    cellM0_positive_of_check a048 (boolean_record_at Validity010.checked 40 (by change 40 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows006

#check Erdos993Lean.Analytic.V213.P03RowData.ARows006.a041_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows006.a041_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows006.a042_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows006.a042_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows006.a043_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows006.a043_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows006.a044_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows006.a044_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows006.a045_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows006.a045_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows006.a046_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows006.a046_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows006.a047_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows006.a047_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows006.a048_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows006.a048_certificate
