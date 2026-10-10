module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup011
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup012
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput004
public import Erdos993Lean.ExactComparisons.F3All.Strict069
public import Erdos993Lean.ExactComparisons.F3All.Strict070
public import Erdos993Lean.ExactComparisons.F3All.Validity002
public import Erdos993Lean.ExactComparisons.F3All.Validity012

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows011

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a081_certificate : ARowCertificate a081 := by
  have hf : ARowFacts a081 := ⟨(boolean_record_at Validity012.checked 10 (by change 10 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt170_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt172_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt173_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e078_bounds)⟩
  have hm := parent_positive_of_checks a081 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 39 (by change 39 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 38 (by change 38 < 64; omega)))
    (comparison_record_at Strict069.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict069.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 16 (by change 16 < 64; omega)),
    cellM0_positive_of_check a081 (boolean_record_at Validity012.checked 11 (by change 11 < 64; omega)), hm.1, hm.2⟩

theorem a082_certificate : ARowCertificate a082 := by
  have hf : ARowFacts a082 := ⟨(boolean_record_at Validity012.checked 13 (by change 13 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt172_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt122_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt174_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e085_bounds)⟩
  have hm := parent_positive_of_checks a082 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 41 (by change 41 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 40 (by change 40 < 64; omega)))
    (comparison_record_at Strict070.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict070.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 17 (by change 17 < 64; omega)),
    cellM0_positive_of_check a082 (boolean_record_at Validity012.checked 14 (by change 14 < 64; omega)), hm.1, hm.2⟩

theorem a083_certificate : ARowCertificate a083 := by
  have hf : ARowFacts a083 := ⟨(boolean_record_at Validity012.checked 16 (by change 16 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt122_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt175_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt176_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e090_bounds)⟩
  have hm := parent_positive_of_checks a083 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 43 (by change 43 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 42 (by change 42 < 64; omega)))
    (comparison_record_at Strict070.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict070.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 18 (by change 18 < 64; omega)),
    cellM0_positive_of_check a083 (boolean_record_at Validity012.checked 17 (by change 17 < 64; omega)), hm.1, hm.2⟩

theorem a084_certificate : ARowCertificate a084 := by
  have hf : ARowFacts a084 := ⟨(boolean_record_at Validity012.checked 19 (by change 19 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup011.pt175_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt124_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt177_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e094_bounds)⟩
  have hm := parent_positive_of_checks a084 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 45 (by change 45 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 44 (by change 44 < 64; omega)))
    (comparison_record_at Strict070.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict070.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 19 (by change 19 < 64; omega)),
    cellM0_positive_of_check a084 (boolean_record_at Validity012.checked 20 (by change 20 < 64; omega)), hm.1, hm.2⟩

theorem a085_certificate : ARowCertificate a085 := by
  have hf : ARowFacts a085 := ⟨(boolean_record_at Validity012.checked 22 (by change 22 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt124_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt178_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt179_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e098_bounds)⟩
  have hm := parent_positive_of_checks a085 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 47 (by change 47 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 46 (by change 46 < 64; omega)))
    (comparison_record_at Strict070.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict070.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 20 (by change 20 < 64; omega)),
    cellM0_positive_of_check a085 (boolean_record_at Validity012.checked 23 (by change 23 < 64; omega)), hm.1, hm.2⟩

theorem a086_certificate : ARowCertificate a086 := by
  have hf : ARowFacts a086 := ⟨(boolean_record_at Validity012.checked 25 (by change 25 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt178_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt125_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt180_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e102_bounds)⟩
  have hm := parent_positive_of_checks a086 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 49 (by change 49 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 48 (by change 48 < 64; omega)))
    (comparison_record_at Strict070.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict070.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 21 (by change 21 < 64; omega)),
    cellM0_positive_of_check a086 (boolean_record_at Validity012.checked 26 (by change 26 < 64; omega)), hm.1, hm.2⟩

theorem a087_certificate : ARowCertificate a087 := by
  have hf : ARowFacts a087 := ⟨(boolean_record_at Validity012.checked 28 (by change 28 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt125_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt181_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt182_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e104_bounds)⟩
  have hm := parent_positive_of_checks a087 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 51 (by change 51 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 50 (by change 50 < 64; omega)))
    (comparison_record_at Strict070.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict070.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 22 (by change 22 < 64; omega)),
    cellM0_positive_of_check a087 (boolean_record_at Validity012.checked 29 (by change 29 < 64; omega)), hm.1, hm.2⟩

theorem a088_certificate : ARowCertificate a088 := by
  have hf : ARowFacts a088 := ⟨(boolean_record_at Validity012.checked 31 (by change 31 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt181_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt127_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup012.pt183_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e106_bounds)⟩
  have hm := parent_positive_of_checks a088 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 53 (by change 53 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput004.checked 52 (by change 52 < 64; omega)))
    (comparison_record_at Strict070.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict070.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity002.checked 23 (by change 23 < 64; omega)),
    cellM0_positive_of_check a088 (boolean_record_at Validity012.checked 32 (by change 32 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows011

#check Erdos993Lean.Analytic.V213.P03RowData.ARows011.a081_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows011.a081_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows011.a082_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows011.a082_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows011.a083_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows011.a083_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows011.a084_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows011.a084_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows011.a085_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows011.a085_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows011.a086_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows011.a086_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows011.a087_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows011.a087_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows011.a088_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows011.a088_certificate
