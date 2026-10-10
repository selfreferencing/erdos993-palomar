module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup010
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup011
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup012
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup013
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup014
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput005
public import Erdos993Lean.ExactComparisons.F3All.Strict072
public import Erdos993Lean.ExactComparisons.F3All.Strict073
public import Erdos993Lean.ExactComparisons.F3All.Validity002
public import Erdos993Lean.ExactComparisons.F3All.Validity013

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows014

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a105_certificate : ARowCertificate a105 := by
  have hf : ARowFacts a105 := ⟨(boolean_record_at Validity013.checked 18 (by change 18 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt001_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt143_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt206_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds)⟩
  have hm := parent_positive_of_checks a105 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 23 (by change 23 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 22 (by change 22 < 64; omega)))
    (comparison_record_at Strict072.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict072.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 40 (by change 40 < 64; omega)),
    cellM0_positive_of_check a105 (boolean_record_at Validity013.checked 19 (by change 19 < 64; omega)), hm.1, hm.2⟩

theorem a106_certificate : ARowCertificate a106 := by
  have hf : ARowFacts a106 := ⟨(boolean_record_at Validity013.checked 21 (by change 21 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt143_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt151_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt207_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds)⟩
  have hm := parent_positive_of_checks a106 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 25 (by change 25 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 24 (by change 24 < 64; omega)))
    (comparison_record_at Strict073.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict073.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 41 (by change 41 < 64; omega)),
    cellM0_positive_of_check a106 (boolean_record_at Validity013.checked 22 (by change 22 < 64; omega)), hm.1, hm.2⟩

theorem a107_certificate : ARowCertificate a107 := by
  have hf : ARowFacts a107 := ⟨(boolean_record_at Validity013.checked 24 (by change 24 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt151_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt157_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt208_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e034_bounds)⟩
  have hm := parent_positive_of_checks a107 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 27 (by change 27 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 26 (by change 26 < 64; omega)))
    (comparison_record_at Strict073.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict073.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 42 (by change 42 < 64; omega)),
    cellM0_positive_of_check a107 (boolean_record_at Validity013.checked 25 (by change 25 < 64; omega)), hm.1, hm.2⟩

theorem a108_certificate : ARowCertificate a108 := by
  have hf : ARowFacts a108 := ⟨(boolean_record_at Validity013.checked 27 (by change 27 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup010.pt157_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt163_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt209_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e047_bounds)⟩
  have hm := parent_positive_of_checks a108 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 29 (by change 29 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 28 (by change 28 < 64; omega)))
    (comparison_record_at Strict073.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict073.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 43 (by change 43 < 64; omega)),
    cellM0_positive_of_check a108 (boolean_record_at Validity013.checked 28 (by change 28 < 64; omega)), hm.1, hm.2⟩

theorem a109_certificate : ARowCertificate a109 := by
  have hf : ARowFacts a109 := ⟨(boolean_record_at Validity013.checked 30 (by change 30 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt163_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt169_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt210_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e061_bounds)⟩
  have hm := parent_positive_of_checks a109 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 31 (by change 31 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 30 (by change 30 < 64; omega)))
    (comparison_record_at Strict073.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict073.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 44 (by change 44 < 64; omega)),
    cellM0_positive_of_check a109 (boolean_record_at Validity013.checked 31 (by change 31 < 64; omega)), hm.1, hm.2⟩

theorem a110_certificate : ARowCertificate a110 := by
  have hf : ARowFacts a110 := ⟨(boolean_record_at Validity013.checked 33 (by change 33 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt169_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt174_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt211_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e081_bounds)⟩
  have hm := parent_positive_of_checks a110 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 33 (by change 33 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 32 (by change 32 < 64; omega)))
    (comparison_record_at Strict073.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict073.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 45 (by change 45 < 64; omega)),
    cellM0_positive_of_check a110 (boolean_record_at Validity013.checked 34 (by change 34 < 64; omega)), hm.1, hm.2⟩

theorem a111_certificate : ARowCertificate a111 := by
  have hf : ARowFacts a111 := ⟨(boolean_record_at Validity013.checked 36 (by change 36 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt174_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt177_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt212_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e093_bounds)⟩
  have hm := parent_positive_of_checks a111 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 35 (by change 35 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 34 (by change 34 < 64; omega)))
    (comparison_record_at Strict073.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict073.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 46 (by change 46 < 64; omega)),
    cellM0_positive_of_check a111 (boolean_record_at Validity013.checked 37 (by change 37 < 64; omega)), hm.1, hm.2⟩

theorem a112_certificate : ARowCertificate a112 := by
  have hf : ARowFacts a112 := ⟨(boolean_record_at Validity013.checked 39 (by change 39 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt177_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt180_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt213_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e100_bounds)⟩
  have hm := parent_positive_of_checks a112 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 37 (by change 37 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 36 (by change 36 < 64; omega)))
    (comparison_record_at Strict073.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict073.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 47 (by change 47 < 64; omega)),
    cellM0_positive_of_check a112 (boolean_record_at Validity013.checked 40 (by change 40 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows014

#check Erdos993Lean.Analytic.V213.P03RowData.ARows014.a105_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows014.a105_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows014.a106_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows014.a106_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows014.a107_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows014.a107_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows014.a108_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows014.a108_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows014.a109_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows014.a109_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows014.a110_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows014.a110_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows014.a111_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows014.a111_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows014.a112_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows014.a112_certificate
