module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup012
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup013
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput004
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput005
public import Erdos993Lean.ExactComparisons.F3All.Strict070
public import Erdos993Lean.ExactComparisons.F3All.Strict071
public import Erdos993Lean.ExactComparisons.F3All.Validity002
public import Erdos993Lean.ExactComparisons.F3All.Validity012

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows012

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a089_certificate : ARowCertificate a089 := by
  have hf : ARowFacts a089 := ⟨(boolean_record_at Validity012.checked 34 (by change 34 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt127_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt184_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt185_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e109_bounds)⟩
  have hm := parent_positive_of_checks a089 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 55 (by change 55 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 54 (by change 54 < 64; omega)))
    (comparison_record_at Strict070.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict070.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 24 (by change 24 < 64; omega)),
    cellM0_positive_of_check a089 (boolean_record_at Validity012.checked 35 (by change 35 < 64; omega)), hm.1, hm.2⟩

theorem a090_certificate : ARowCertificate a090 := by
  have hf : ARowFacts a090 := ⟨(boolean_record_at Validity012.checked 37 (by change 37 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt184_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt128_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt186_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e111_bounds)⟩
  have hm := parent_positive_of_checks a090 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 57 (by change 57 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 56 (by change 56 < 64; omega)))
    (comparison_record_at Strict071.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict071.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 25 (by change 25 < 64; omega)),
    cellM0_positive_of_check a090 (boolean_record_at Validity012.checked 38 (by change 38 < 64; omega)), hm.1, hm.2⟩

theorem a091_certificate : ARowCertificate a091 := by
  have hf : ARowFacts a091 := ⟨(boolean_record_at Validity012.checked 40 (by change 40 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt128_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt187_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt188_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e113_bounds)⟩
  have hm := parent_positive_of_checks a091 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 59 (by change 59 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 58 (by change 58 < 64; omega)))
    (comparison_record_at Strict071.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict071.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 26 (by change 26 < 64; omega)),
    cellM0_positive_of_check a091 (boolean_record_at Validity012.checked 41 (by change 41 < 64; omega)), hm.1, hm.2⟩

theorem a092_certificate : ARowCertificate a092 := by
  have hf : ARowFacts a092 := ⟨(boolean_record_at Validity012.checked 43 (by change 43 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt187_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt130_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt189_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e115_bounds)⟩
  have hm := parent_positive_of_checks a092 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 61 (by change 61 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 60 (by change 60 < 64; omega)))
    (comparison_record_at Strict071.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict071.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 27 (by change 27 < 64; omega)),
    cellM0_positive_of_check a092 (boolean_record_at Validity012.checked 44 (by change 44 < 64; omega)), hm.1, hm.2⟩

theorem a093_certificate : ARowCertificate a093 := by
  have hf : ARowFacts a093 := ⟨(boolean_record_at Validity012.checked 46 (by change 46 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt130_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt190_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt191_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e117_bounds)⟩
  have hm := parent_positive_of_checks a093 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 63 (by change 63 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 62 (by change 62 < 64; omega)))
    (comparison_record_at Strict071.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict071.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 28 (by change 28 < 64; omega)),
    cellM0_positive_of_check a093 (boolean_record_at Validity012.checked 47 (by change 47 < 64; omega)), hm.1, hm.2⟩

theorem a094_certificate : ARowCertificate a094 := by
  have hf : ARowFacts a094 := ⟨(boolean_record_at Validity012.checked 49 (by change 49 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt190_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt131_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt192_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e119_bounds)⟩
  have hm := parent_positive_of_checks a094 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 1 (by change 1 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 0 (by change 0 < 64; omega)))
    (comparison_record_at Strict071.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict071.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 29 (by change 29 < 64; omega)),
    cellM0_positive_of_check a094 (boolean_record_at Validity012.checked 50 (by change 50 < 64; omega)), hm.1, hm.2⟩

theorem a095_certificate : ARowCertificate a095 := by
  have hf : ARowFacts a095 := ⟨(boolean_record_at Validity012.checked 52 (by change 52 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt131_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt193_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt194_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e121_bounds)⟩
  have hm := parent_positive_of_checks a095 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 3 (by change 3 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 2 (by change 2 < 64; omega)))
    (comparison_record_at Strict071.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict071.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 30 (by change 30 < 64; omega)),
    cellM0_positive_of_check a095 (boolean_record_at Validity012.checked 53 (by change 53 < 64; omega)), hm.1, hm.2⟩

theorem a096_certificate : ARowCertificate a096 := by
  have hf : ARowFacts a096 := ⟨(boolean_record_at Validity012.checked 55 (by change 55 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt193_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt133_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup013.pt195_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e123_bounds)⟩
  have hm := parent_positive_of_checks a096 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 5 (by change 5 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput005.checked 4 (by change 4 < 64; omega)))
    (comparison_record_at Strict071.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict071.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 31 (by change 31 < 64; omega)),
    cellM0_positive_of_check a096 (boolean_record_at Validity012.checked 56 (by change 56 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows012

#check Erdos993Lean.Analytic.V213.P03RowData.ARows012.a089_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows012.a089_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows012.a090_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows012.a090_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows012.a091_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows012.a091_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows012.a092_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows012.a092_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows012.a093_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows012.a093_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows012.a094_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows012.a094_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows012.a095_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows012.a095_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows012.a096_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows012.a096_certificate
