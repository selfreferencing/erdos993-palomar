module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup012
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup013
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup014
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput005
public import Erdos993Lean.ExactComparisons.F3All.Strict073
public import Erdos993Lean.ExactComparisons.F3All.Strict074
public import Erdos993Lean.ExactComparisons.F3All.Validity002
public import Erdos993Lean.ExactComparisons.F3All.Validity013
public import Erdos993Lean.ExactComparisons.F3All.Validity014

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows015

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a113_certificate : ARowCertificate a113 := by
  have hf : ARowFacts a113 := ⟨(boolean_record_at Validity013.checked 42 (by change 42 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt180_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt183_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt214_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e105_bounds)⟩
  have hm := parent_positive_of_checks a113 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 39 (by change 39 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 38 (by change 38 < 64; omega)))
    (comparison_record_at Strict073.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict073.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 48 (by change 48 < 64; omega)),
    cellM0_positive_of_check a113 (boolean_record_at Validity013.checked 43 (by change 43 < 64; omega)), hm.1, hm.2⟩

theorem a114_certificate : ARowCertificate a114 := by
  have hf : ARowFacts a114 := ⟨(boolean_record_at Validity013.checked 45 (by change 45 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt183_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt186_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt215_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e110_bounds)⟩
  have hm := parent_positive_of_checks a114 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 41 (by change 41 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 40 (by change 40 < 64; omega)))
    (comparison_record_at Strict074.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict074.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 49 (by change 49 < 64; omega)),
    cellM0_positive_of_check a114 (boolean_record_at Validity013.checked 46 (by change 46 < 64; omega)), hm.1, hm.2⟩

theorem a115_certificate : ARowCertificate a115 := by
  have hf : ARowFacts a115 := ⟨(boolean_record_at Validity013.checked 48 (by change 48 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt186_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt189_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt216_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e114_bounds)⟩
  have hm := parent_positive_of_checks a115 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 43 (by change 43 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 42 (by change 42 < 64; omega)))
    (comparison_record_at Strict074.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict074.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 50 (by change 50 < 64; omega)),
    cellM0_positive_of_check a115 (boolean_record_at Validity013.checked 49 (by change 49 < 64; omega)), hm.1, hm.2⟩

theorem a116_certificate : ARowCertificate a116 := by
  have hf : ARowFacts a116 := ⟨(boolean_record_at Validity013.checked 51 (by change 51 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt189_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt192_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt217_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e118_bounds)⟩
  have hm := parent_positive_of_checks a116 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 45 (by change 45 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 44 (by change 44 < 64; omega)))
    (comparison_record_at Strict074.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict074.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 51 (by change 51 < 64; omega)),
    cellM0_positive_of_check a116 (boolean_record_at Validity013.checked 52 (by change 52 < 64; omega)), hm.1, hm.2⟩

theorem a117_certificate : ARowCertificate a117 := by
  have hf : ARowFacts a117 := ⟨(boolean_record_at Validity013.checked 54 (by change 54 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt192_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt196_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt218_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds)⟩
  have hm := parent_positive_of_checks a117 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 47 (by change 47 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 46 (by change 46 < 64; omega)))
    (comparison_record_at Strict074.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict074.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 52 (by change 52 < 64; omega)),
    cellM0_positive_of_check a117 (boolean_record_at Validity013.checked 55 (by change 55 < 64; omega)), hm.1, hm.2⟩

theorem a118_certificate : ARowCertificate a118 := by
  have hf : ARowFacts a118 := ⟨(boolean_record_at Validity013.checked 57 (by change 57 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt196_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt199_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt219_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds)⟩
  have hm := parent_positive_of_checks a118 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 49 (by change 49 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 48 (by change 48 < 64; omega)))
    (comparison_record_at Strict074.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict074.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 53 (by change 53 < 64; omega)),
    cellM0_positive_of_check a118 (boolean_record_at Validity013.checked 58 (by change 58 < 64; omega)), hm.1, hm.2⟩

theorem a119_certificate : ARowCertificate a119 := by
  have hf : ARowFacts a119 := ⟨(boolean_record_at Validity013.checked 60 (by change 60 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt199_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt202_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt220_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds)⟩
  have hm := parent_positive_of_checks a119 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 51 (by change 51 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 50 (by change 50 < 64; omega)))
    (comparison_record_at Strict074.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict074.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 54 (by change 54 < 64; omega)),
    cellM0_positive_of_check a119 (boolean_record_at Validity013.checked 61 (by change 61 < 64; omega)), hm.1, hm.2⟩

theorem a120_certificate : ARowCertificate a120 := by
  have hf : ARowFacts a120 := ⟨(boolean_record_at Validity013.checked 63 (by change 63 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt202_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt203_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup014.pt221_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e135_bounds)⟩
  have hm := parent_positive_of_checks a120 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 53 (by change 53 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 52 (by change 52 < 64; omega)))
    (comparison_record_at Strict074.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict074.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 55 (by change 55 < 64; omega)),
    cellM0_positive_of_check a120 (boolean_record_at Validity014.checked 0 (by change 0 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows015

#check Erdos993Lean.Analytic.V213.P03RowData.ARows015.a113_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows015.a113_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows015.a114_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows015.a114_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows015.a115_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows015.a115_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows015.a116_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows015.a116_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows015.a117_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows015.a117_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows015.a118_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows015.a118_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows015.a119_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows015.a119_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows015.a120_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows015.a120_certificate
