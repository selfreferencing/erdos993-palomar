module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup016
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup017
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput006
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput007
public import Erdos993Lean.ExactComparisons.F3All.Strict078
public import Erdos993Lean.ExactComparisons.F3All.Strict079
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity015

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows020

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a153_certificate : ARowCertificate a153 := by
  have hf : ARowFacts a153 := ⟨(boolean_record_at Validity015.checked 34 (by change 34 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt242_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt243_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt254_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds)⟩
  have hm := parent_positive_of_checks a153 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 55 (by change 55 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 54 (by change 54 < 64; omega)))
    (comparison_record_at Strict078.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict078.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 24 (by change 24 < 64; omega)),
    cellM0_positive_of_check a153 (boolean_record_at Validity015.checked 35 (by change 35 < 64; omega)), hm.1, hm.2⟩

theorem a154_certificate : ARowCertificate a154 := by
  have hf : ARowFacts a154 := ⟨(boolean_record_at Validity015.checked 37 (by change 37 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt243_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt244_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt255_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds)⟩
  have hm := parent_positive_of_checks a154 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 57 (by change 57 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 56 (by change 56 < 64; omega)))
    (comparison_record_at Strict079.checked 0 (by change 0 < 12; omega)) (comparison_record_at Strict079.checked 1 (by change 1 < 12; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 25 (by change 25 < 64; omega)),
    cellM0_positive_of_check a154 (boolean_record_at Validity015.checked 38 (by change 38 < 64; omega)), hm.1, hm.2⟩

theorem a155_certificate : ARowCertificate a155 := by
  have hf : ARowFacts a155 := ⟨(boolean_record_at Validity015.checked 40 (by change 40 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt244_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt245_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt256_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds)⟩
  have hm := parent_positive_of_checks a155 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 59 (by change 59 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 58 (by change 58 < 64; omega)))
    (comparison_record_at Strict079.checked 2 (by change 2 < 12; omega)) (comparison_record_at Strict079.checked 3 (by change 3 < 12; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 26 (by change 26 < 64; omega)),
    cellM0_positive_of_check a155 (boolean_record_at Validity015.checked 41 (by change 41 < 64; omega)), hm.1, hm.2⟩

theorem a156_certificate : ARowCertificate a156 := by
  have hf : ARowFacts a156 := ⟨(boolean_record_at Validity015.checked 43 (by change 43 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt245_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt246_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup017.pt257_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e132_bounds)⟩
  have hm := parent_positive_of_checks a156 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 61 (by change 61 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 60 (by change 60 < 64; omega)))
    (comparison_record_at Strict079.checked 4 (by change 4 < 12; omega)) (comparison_record_at Strict079.checked 5 (by change 5 < 12; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 27 (by change 27 < 64; omega)),
    cellM0_positive_of_check a156 (boolean_record_at Validity015.checked 44 (by change 44 < 64; omega)), hm.1, hm.2⟩

theorem a157_certificate : ARowCertificate a157 := by
  have hf : ARowFacts a157 := ⟨(boolean_record_at Validity015.checked 46 (by change 46 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt246_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt247_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup017.pt258_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e135_bounds)⟩
  have hm := parent_positive_of_checks a157 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 63 (by change 63 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput006.checked 62 (by change 62 < 64; omega)))
    (comparison_record_at Strict079.checked 6 (by change 6 < 12; omega)) (comparison_record_at Strict079.checked 7 (by change 7 < 12; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 28 (by change 28 < 64; omega)),
    cellM0_positive_of_check a157 (boolean_record_at Validity015.checked 47 (by change 47 < 64; omega)), hm.1, hm.2⟩

theorem a158_certificate : ARowCertificate a158 := by
  have hf : ARowFacts a158 := ⟨(boolean_record_at Validity015.checked 49 (by change 49 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt247_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt248_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup017.pt259_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e137_bounds)⟩
  have hm := parent_positive_of_checks a158 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput007.checked 1 (by change 1 < 4; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput007.checked 0 (by change 0 < 4; omega)))
    (comparison_record_at Strict079.checked 8 (by change 8 < 12; omega)) (comparison_record_at Strict079.checked 9 (by change 9 < 12; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 29 (by change 29 < 64; omega)),
    cellM0_positive_of_check a158 (boolean_record_at Validity015.checked 50 (by change 50 < 64; omega)), hm.1, hm.2⟩

theorem a159_certificate : ARowCertificate a159 := by
  have hf : ARowFacts a159 := ⟨(boolean_record_at Validity015.checked 52 (by change 52 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt248_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup016.pt249_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup017.pt260_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e139_bounds)⟩
  have hm := parent_positive_of_checks a159 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput007.checked 3 (by change 3 < 4; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput007.checked 2 (by change 2 < 4; omega)))
    (comparison_record_at Strict079.checked 10 (by change 10 < 12; omega)) (comparison_record_at Strict079.checked 11 (by change 11 < 12; omega))
  exact ⟨hf, (boolean_record_at Validity003.checked 30 (by change 30 < 64; omega)),
    cellM0_positive_of_check a159 (boolean_record_at Validity015.checked 53 (by change 53 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows020

#check Erdos993Lean.Analytic.V213.P03RowData.ARows020.a153_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows020.a153_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows020.a154_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows020.a154_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows020.a155_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows020.a155_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows020.a156_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows020.a156_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows020.a157_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows020.a157_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows020.a158_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows020.a158_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows020.a159_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows020.a159_certificate
