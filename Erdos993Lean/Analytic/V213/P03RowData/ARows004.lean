module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup007
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput002
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput003
public import Erdos993Lean.ExactComparisons.F3All.Strict062
public import Erdos993Lean.ExactComparisons.F3All.Strict063
public import Erdos993Lean.ExactComparisons.F3All.Validity001
public import Erdos993Lean.ExactComparisons.F3All.Validity009

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows004

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a025_certificate : ARowCertificate a025 := by
  have hf : ARowFacts a025 := ⟨(boolean_record_at Validity009.checked 34 (by change 34 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt065_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt093_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt094_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup004.e061_bounds)⟩
  have hm := parent_positive_of_checks a025 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 55 (by change 55 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 54 (by change 54 < 64; omega)))
    (comparison_record_at Strict062.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict062.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 24 (by change 24 < 64; omega)),
    cellM0_positive_of_check a025 (boolean_record_at Validity009.checked 35 (by change 35 < 64; omega)), hm.1, hm.2⟩

theorem a026_certificate : ARowCertificate a026 := by
  have hf : ARowFacts a026 := ⟨(boolean_record_at Validity009.checked 37 (by change 37 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt093_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt067_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt095_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup006.e081_bounds)⟩
  have hm := parent_positive_of_checks a026 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 57 (by change 57 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 56 (by change 56 < 64; omega)))
    (comparison_record_at Strict063.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict063.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 25 (by change 25 < 64; omega)),
    cellM0_positive_of_check a026 (boolean_record_at Validity009.checked 38 (by change 38 < 64; omega)), hm.1, hm.2⟩

theorem a027_certificate : ARowCertificate a027 := by
  have hf : ARowFacts a027 := ⟨(boolean_record_at Validity009.checked 40 (by change 40 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt067_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt069_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt096_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds)⟩
  have hm := parent_positive_of_checks a027 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 59 (by change 59 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 58 (by change 58 < 64; omega)))
    (comparison_record_at Strict063.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict063.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 26 (by change 26 < 64; omega)),
    cellM0_positive_of_check a027 (boolean_record_at Validity009.checked 41 (by change 41 < 64; omega)), hm.1, hm.2⟩

theorem a028_certificate : ARowCertificate a028 := by
  have hf : ARowFacts a028 := ⟨(boolean_record_at Validity009.checked 43 (by change 43 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt069_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt071_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt097_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds)⟩
  have hm := parent_positive_of_checks a028 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 61 (by change 61 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 60 (by change 60 < 64; omega)))
    (comparison_record_at Strict063.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict063.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 27 (by change 27 < 64; omega)),
    cellM0_positive_of_check a028 (boolean_record_at Validity009.checked 44 (by change 44 < 64; omega)), hm.1, hm.2⟩

theorem a029_certificate : ARowCertificate a029 := by
  have hf : ARowFacts a029 := ⟨(boolean_record_at Validity009.checked 46 (by change 46 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt071_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt073_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt098_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds)⟩
  have hm := parent_positive_of_checks a029 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 63 (by change 63 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 62 (by change 62 < 64; omega)))
    (comparison_record_at Strict063.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict063.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 28 (by change 28 < 64; omega)),
    cellM0_positive_of_check a029 (boolean_record_at Validity009.checked 47 (by change 47 < 64; omega)), hm.1, hm.2⟩

theorem a030_certificate : ARowCertificate a030 := by
  have hf : ARowFacts a030 := ⟨(boolean_record_at Validity009.checked 49 (by change 49 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt073_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt099_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt100_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e124_bounds)⟩
  have hm := parent_positive_of_checks a030 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 1 (by change 1 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 0 (by change 0 < 64; omega)))
    (comparison_record_at Strict063.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict063.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 29 (by change 29 < 64; omega)),
    cellM0_positive_of_check a030 (boolean_record_at Validity009.checked 50 (by change 50 < 64; omega)), hm.1, hm.2⟩

theorem a031_certificate : ARowCertificate a031 := by
  have hf : ARowFacts a031 := ⟨(boolean_record_at Validity009.checked 52 (by change 52 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt099_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt075_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt101_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds)⟩
  have hm := parent_positive_of_checks a031 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 3 (by change 3 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 2 (by change 2 < 64; omega)))
    (comparison_record_at Strict063.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict063.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 30 (by change 30 < 64; omega)),
    cellM0_positive_of_check a031 (boolean_record_at Validity009.checked 53 (by change 53 < 64; omega)), hm.1, hm.2⟩

theorem a032_certificate : ARowCertificate a032 := by
  have hf : ARowFacts a032 := ⟨(boolean_record_at Validity009.checked 55 (by change 55 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt075_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt077_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt102_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds)⟩
  have hm := parent_positive_of_checks a032 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 5 (by change 5 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 4 (by change 4 < 64; omega)))
    (comparison_record_at Strict063.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict063.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 31 (by change 31 < 64; omega)),
    cellM0_positive_of_check a032 (boolean_record_at Validity009.checked 56 (by change 56 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows004

#check Erdos993Lean.Analytic.V213.P03RowData.ARows004.a025_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows004.a025_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows004.a026_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows004.a026_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows004.a027_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows004.a027_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows004.a028_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows004.a028_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows004.a029_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows004.a029_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows004.a030_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows004.a030_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows004.a031_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows004.a031_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows004.a032_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows004.a032_certificate
