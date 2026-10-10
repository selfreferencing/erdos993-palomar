module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup006
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup007
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup008
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup009
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput003
public import Erdos993Lean.ExactComparisons.F3All.Strict065
public import Erdos993Lean.ExactComparisons.F3All.Strict066
public import Erdos993Lean.ExactComparisons.F3All.Validity001
public import Erdos993Lean.ExactComparisons.F3All.Validity010
public import Erdos993Lean.ExactComparisons.F3All.Validity011

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows007

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a049_certificate : ARowCertificate a049 := by
  have hf : ARowFacts a049 := ⟨(boolean_record_at Validity010.checked 42 (by change 42 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt123_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt096_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt125_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e100_bounds)⟩
  have hm := parent_positive_of_checks a049 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 39 (by change 39 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 38 (by change 38 < 64; omega)))
    (comparison_record_at Strict065.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict065.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 48 (by change 48 < 64; omega)),
    cellM0_positive_of_check a049 (boolean_record_at Validity010.checked 43 (by change 43 < 64; omega)), hm.1, hm.2⟩

theorem a050_certificate : ARowCertificate a050 := by
  have hf : ARowFacts a050 := ⟨(boolean_record_at Validity010.checked 45 (by change 45 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt096_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt126_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt127_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e105_bounds)⟩
  have hm := parent_positive_of_checks a050 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 41 (by change 41 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 40 (by change 40 < 64; omega)))
    (comparison_record_at Strict066.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict066.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 49 (by change 49 < 64; omega)),
    cellM0_positive_of_check a050 (boolean_record_at Validity010.checked 46 (by change 46 < 64; omega)), hm.1, hm.2⟩

theorem a051_certificate : ARowCertificate a051 := by
  have hf : ARowFacts a051 := ⟨(boolean_record_at Validity010.checked 48 (by change 48 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt126_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt097_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup008.pt128_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup007.e110_bounds)⟩
  have hm := parent_positive_of_checks a051 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 43 (by change 43 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 42 (by change 42 < 64; omega)))
    (comparison_record_at Strict066.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict066.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 50 (by change 50 < 64; omega)),
    cellM0_positive_of_check a051 (boolean_record_at Validity010.checked 49 (by change 49 < 64; omega)), hm.1, hm.2⟩

theorem a052_certificate : ARowCertificate a052 := by
  have hf : ARowFacts a052 := ⟨(boolean_record_at Validity010.checked 51 (by change 51 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt097_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt129_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt130_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e114_bounds)⟩
  have hm := parent_positive_of_checks a052 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 45 (by change 45 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 44 (by change 44 < 64; omega)))
    (comparison_record_at Strict066.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict066.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 51 (by change 51 < 64; omega)),
    cellM0_positive_of_check a052 (boolean_record_at Validity010.checked 52 (by change 52 < 64; omega)), hm.1, hm.2⟩

theorem a053_certificate : ARowCertificate a053 := by
  have hf : ARowFacts a053 := ⟨(boolean_record_at Validity010.checked 54 (by change 54 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt129_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt098_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt131_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e118_bounds)⟩
  have hm := parent_positive_of_checks a053 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 47 (by change 47 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 46 (by change 46 < 64; omega)))
    (comparison_record_at Strict066.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict066.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 52 (by change 52 < 64; omega)),
    cellM0_positive_of_check a053 (boolean_record_at Validity010.checked 55 (by change 55 < 64; omega)), hm.1, hm.2⟩

theorem a054_certificate : ARowCertificate a054 := by
  have hf : ARowFacts a054 := ⟨(boolean_record_at Validity010.checked 57 (by change 57 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt098_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt132_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt133_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e122_bounds)⟩
  have hm := parent_positive_of_checks a054 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 49 (by change 49 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 48 (by change 48 < 64; omega)))
    (comparison_record_at Strict066.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict066.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 53 (by change 53 < 64; omega)),
    cellM0_positive_of_check a054 (boolean_record_at Validity010.checked 58 (by change 58 < 64; omega)), hm.1, hm.2⟩

theorem a055_certificate : ARowCertificate a055 := by
  have hf : ARowFacts a055 := ⟨(boolean_record_at Validity010.checked 60 (by change 60 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt132_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt100_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt134_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup008.e125_bounds)⟩
  have hm := parent_positive_of_checks a055 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 51 (by change 51 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 50 (by change 50 < 64; omega)))
    (comparison_record_at Strict066.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict066.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 54 (by change 54 < 64; omega)),
    cellM0_positive_of_check a055 (boolean_record_at Validity010.checked 61 (by change 61 < 64; omega)), hm.1, hm.2⟩

theorem a056_certificate : ARowCertificate a056 := by
  have hf : ARowFacts a056 := ⟨(boolean_record_at Validity010.checked 63 (by change 63 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt100_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup007.pt101_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup009.pt135_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup009.e128_bounds)⟩
  have hm := parent_positive_of_checks a056 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 53 (by change 53 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput003.checked 52 (by change 52 < 64; omega)))
    (comparison_record_at Strict066.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict066.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 55 (by change 55 < 64; omega)),
    cellM0_positive_of_check a056 (boolean_record_at Validity011.checked 0 (by change 0 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows007

#check Erdos993Lean.Analytic.V213.P03RowData.ARows007.a049_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows007.a049_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows007.a050_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows007.a050_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows007.a051_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows007.a051_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows007.a052_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows007.a052_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows007.a053_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows007.a053_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows007.a054_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows007.a054_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows007.a055_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows007.a055_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows007.a056_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows007.a056_certificate
