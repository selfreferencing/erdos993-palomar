module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup006
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput002
public import Erdos993Lean.ExactComparisons.F3All.Strict060
public import Erdos993Lean.ExactComparisons.F3All.Strict061
public import Erdos993Lean.ExactComparisons.F3All.Validity001
public import Erdos993Lean.ExactComparisons.F3All.Validity008
public import Erdos993Lean.ExactComparisons.F3All.Validity009

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows002

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a009_certificate : ARowCertificate a009 := by
  have hf : ARowFacts a009 := ⟨(boolean_record_at Validity008.checked 50 (by change 50 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt064_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt066_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt067_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup005.e071_bounds)⟩
  have hm := parent_positive_of_checks a009 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 23 (by change 23 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 22 (by change 22 < 64; omega)))
    (comparison_record_at Strict060.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict060.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 8 (by change 8 < 64; omega)),
    cellM0_positive_of_check a009 (boolean_record_at Validity008.checked 51 (by change 51 < 64; omega)), hm.1, hm.2⟩

theorem a010_certificate : ARowCertificate a010 := by
  have hf : ARowFacts a010 := ⟨(boolean_record_at Validity008.checked 53 (by change 53 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt066_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt068_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt069_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e097_bounds)⟩
  have hm := parent_positive_of_checks a010 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 25 (by change 25 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 24 (by change 24 < 64; omega)))
    (comparison_record_at Strict061.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict061.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 9 (by change 9 < 64; omega)),
    cellM0_positive_of_check a010 (boolean_record_at Validity008.checked 54 (by change 54 < 64; omega)), hm.1, hm.2⟩

theorem a011_certificate : ARowCertificate a011 := by
  have hf : ARowFacts a011 := ⟨(boolean_record_at Validity008.checked 56 (by change 56 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt068_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt070_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt071_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e108_bounds)⟩
  have hm := parent_positive_of_checks a011 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 27 (by change 27 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 26 (by change 26 < 64; omega)))
    (comparison_record_at Strict061.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict061.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 10 (by change 10 < 64; omega)),
    cellM0_positive_of_check a011 (boolean_record_at Validity008.checked 57 (by change 57 < 64; omega)), hm.1, hm.2⟩

theorem a012_certificate : ARowCertificate a012 := by
  have hf : ARowFacts a012 := ⟨(boolean_record_at Validity008.checked 59 (by change 59 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt070_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt072_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt073_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e116_bounds)⟩
  have hm := parent_positive_of_checks a012 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 29 (by change 29 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 28 (by change 28 < 64; omega)))
    (comparison_record_at Strict061.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict061.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 11 (by change 11 < 64; omega)),
    cellM0_positive_of_check a012 (boolean_record_at Validity008.checked 60 (by change 60 < 64; omega)), hm.1, hm.2⟩

theorem a013_certificate : ARowCertificate a013 := by
  have hf : ARowFacts a013 := ⟨(boolean_record_at Validity008.checked 62 (by change 62 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt072_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt074_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt075_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e126_bounds)⟩
  have hm := parent_positive_of_checks a013 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 31 (by change 31 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 30 (by change 30 < 64; omega)))
    (comparison_record_at Strict061.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict061.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 12 (by change 12 < 64; omega)),
    cellM0_positive_of_check a013 (boolean_record_at Validity008.checked 63 (by change 63 < 64; omega)), hm.1, hm.2⟩

theorem a014_certificate : ARowCertificate a014 := by
  have hf : ARowFacts a014 := ⟨(boolean_record_at Validity009.checked 1 (by change 1 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt074_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt076_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt077_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e134_bounds)⟩
  have hm := parent_positive_of_checks a014 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 33 (by change 33 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 32 (by change 32 < 64; omega)))
    (comparison_record_at Strict061.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict061.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 13 (by change 13 < 64; omega)),
    cellM0_positive_of_check a014 (boolean_record_at Validity009.checked 2 (by change 2 < 64; omega)), hm.1, hm.2⟩

theorem a015_certificate : ARowCertificate a015 := by
  have hf : ARowFacts a015 := ⟨(boolean_record_at Validity009.checked 4 (by change 4 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt076_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt078_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt079_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e138_bounds)⟩
  have hm := parent_positive_of_checks a015 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 35 (by change 35 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 34 (by change 34 < 64; omega)))
    (comparison_record_at Strict061.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict061.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 14 (by change 14 < 64; omega)),
    cellM0_positive_of_check a015 (boolean_record_at Validity009.checked 5 (by change 5 < 64; omega)), hm.1, hm.2⟩

theorem a016_certificate : ARowCertificate a016 := by
  have hf : ARowFacts a016 := ⟨(boolean_record_at Validity009.checked 7 (by change 7 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt080_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt053_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt081_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e002_bounds)⟩
  have hm := parent_positive_of_checks a016 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 37 (by change 37 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 36 (by change 36 < 64; omega)))
    (comparison_record_at Strict061.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict061.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 15 (by change 15 < 64; omega)),
    cellM0_positive_of_check a016 (boolean_record_at Validity009.checked 8 (by change 8 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows002

#check Erdos993Lean.Analytic.V213.P03RowData.ARows002.a009_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows002.a009_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows002.a010_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows002.a010_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows002.a011_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows002.a011_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows002.a012_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows002.a012_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows002.a013_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows002.a013_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows002.a014_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows002.a014_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows002.a015_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows002.a015_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows002.a016_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows002.a016_certificate
