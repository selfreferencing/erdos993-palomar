module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup013
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup014
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup015
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput005
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput006
public import Erdos993Lean.ExactComparisons.F3All.Strict074
public import Erdos993Lean.ExactComparisons.F3All.Strict075
public import Erdos993Lean.ExactComparisons.F3All.Validity002
public import Erdos993Lean.ExactComparisons.F3All.Validity014

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows016

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a121_certificate : ARowCertificate a121 := by
  have hf : ARowFacts a121 := ⟨(boolean_record_at Validity014.checked 2 (by change 2 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt203_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt204_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt222_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e137_bounds)⟩
  have hm := parent_positive_of_checks a121 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 55 (by change 55 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 54 (by change 54 < 64; omega)))
    (comparison_record_at Strict074.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict074.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 56 (by change 56 < 64; omega)),
    cellM0_positive_of_check a121 (boolean_record_at Validity014.checked 3 (by change 3 < 64; omega)), hm.1, hm.2⟩

theorem a122_certificate : ARowCertificate a122 := by
  have hf : ARowFacts a122 := ⟨(boolean_record_at Validity014.checked 5 (by change 5 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt204_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt205_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt223_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e139_bounds)⟩
  have hm := parent_positive_of_checks a122 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 57 (by change 57 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 56 (by change 56 < 64; omega)))
    (comparison_record_at Strict075.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict075.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 57 (by change 57 < 64; omega)),
    cellM0_positive_of_check a122 (boolean_record_at Validity014.checked 6 (by change 6 < 64; omega)), hm.1, hm.2⟩

theorem a123_certificate : ARowCertificate a123 := by
  have hf : ARowFacts a123 := ⟨(boolean_record_at Validity014.checked 8 (by change 8 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup001.pt008_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt206_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt224_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e004_bounds)⟩
  have hm := parent_positive_of_checks a123 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 59 (by change 59 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 58 (by change 58 < 64; omega)))
    (comparison_record_at Strict075.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict075.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 58 (by change 58 < 64; omega)),
    cellM0_positive_of_check a123 (boolean_record_at Validity014.checked 9 (by change 9 < 64; omega)), hm.1, hm.2⟩

theorem a124_certificate : ARowCertificate a124 := by
  have hf : ARowFacts a124 := ⟨(boolean_record_at Validity014.checked 11 (by change 11 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt206_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt207_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt225_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e019_bounds)⟩
  have hm := parent_positive_of_checks a124 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 61 (by change 61 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 60 (by change 60 < 64; omega)))
    (comparison_record_at Strict075.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict075.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 59 (by change 59 < 64; omega)),
    cellM0_positive_of_check a124 (boolean_record_at Validity014.checked 12 (by change 12 < 64; omega)), hm.1, hm.2⟩

theorem a125_certificate : ARowCertificate a125 := by
  have hf : ARowFacts a125 := ⟨(boolean_record_at Validity014.checked 14 (by change 14 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt207_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt209_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt226_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds)⟩
  have hm := parent_positive_of_checks a125 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 63 (by change 63 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 62 (by change 62 < 64; omega)))
    (comparison_record_at Strict075.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict075.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 60 (by change 60 < 64; omega)),
    cellM0_positive_of_check a125 (boolean_record_at Validity014.checked 15 (by change 15 < 64; omega)), hm.1, hm.2⟩

theorem a126_certificate : ARowCertificate a126 := by
  have hf : ARowFacts a126 := ⟨(boolean_record_at Validity014.checked 17 (by change 17 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt209_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt211_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt227_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds)⟩
  have hm := parent_positive_of_checks a126 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 1 (by change 1 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 0 (by change 0 < 64; omega)))
    (comparison_record_at Strict075.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict075.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 61 (by change 61 < 64; omega)),
    cellM0_positive_of_check a126 (boolean_record_at Validity014.checked 18 (by change 18 < 64; omega)), hm.1, hm.2⟩

theorem a127_certificate : ARowCertificate a127 := by
  have hf : ARowFacts a127 := ⟨(boolean_record_at Validity014.checked 20 (by change 20 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt211_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt213_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt228_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds)⟩
  have hm := parent_positive_of_checks a127 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 3 (by change 3 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 2 (by change 2 < 64; omega)))
    (comparison_record_at Strict075.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict075.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 62 (by change 62 < 64; omega)),
    cellM0_positive_of_check a127 (boolean_record_at Validity014.checked 21 (by change 21 < 64; omega)), hm.1, hm.2⟩

theorem a128_certificate : ARowCertificate a128 := by
  have hf : ARowFacts a128 := ⟨(boolean_record_at Validity014.checked 23 (by change 23 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt213_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt215_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup015.pt229_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds)⟩
  have hm := parent_positive_of_checks a128 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 5 (by change 5 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 4 (by change 4 < 64; omega)))
    (comparison_record_at Strict075.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict075.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 63 (by change 63 < 64; omega)),
    cellM0_positive_of_check a128 (boolean_record_at Validity014.checked 24 (by change 24 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows016

#check Erdos993Lean.Analytic.V213.P03RowData.ARows016.a121_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows016.a121_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows016.a122_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows016.a122_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows016.a123_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows016.a123_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows016.a124_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows016.a124_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows016.a125_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows016.a125_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows016.a126_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows016.a126_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows016.a127_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows016.a127_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows016.a128_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows016.a128_certificate
