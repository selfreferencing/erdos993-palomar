module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup005
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput002
public import Erdos993Lean.ExactComparisons.F3All.Strict059
public import Erdos993Lean.ExactComparisons.F3All.Strict060
public import Erdos993Lean.ExactComparisons.F3All.Validity001
public import Erdos993Lean.ExactComparisons.F3All.Validity008

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows001

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a001_certificate : ARowCertificate a001 := by
  have hf : ARowFacts a001 := ⟨(boolean_record_at Validity008.checked 26 (by change 26 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt049_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt050_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt051_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e001_bounds)⟩
  have hm := parent_positive_of_checks a001 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 7 (by change 7 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 6 (by change 6 < 64; omega)))
    (comparison_record_at Strict059.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict059.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 0 (by change 0 < 64; omega)),
    cellM0_positive_of_check a001 (boolean_record_at Validity008.checked 27 (by change 27 < 64; omega)), hm.1, hm.2⟩

theorem a002_certificate : ARowCertificate a002 := by
  have hf : ARowFacts a002 := ⟨(boolean_record_at Validity008.checked 29 (by change 29 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt050_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt052_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt053_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e003_bounds)⟩
  have hm := parent_positive_of_checks a002 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 9 (by change 9 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 8 (by change 8 < 64; omega)))
    (comparison_record_at Strict060.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict060.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 1 (by change 1 < 64; omega)),
    cellM0_positive_of_check a002 (boolean_record_at Validity008.checked 30 (by change 30 < 64; omega)), hm.1, hm.2⟩

theorem a003_certificate : ARowCertificate a003 := by
  have hf : ARowFacts a003 := ⟨(boolean_record_at Validity008.checked 32 (by change 32 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt052_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt054_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt055_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e005_bounds)⟩
  have hm := parent_positive_of_checks a003 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 11 (by change 11 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 10 (by change 10 < 64; omega)))
    (comparison_record_at Strict060.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict060.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 2 (by change 2 < 64; omega)),
    cellM0_positive_of_check a003 (boolean_record_at Validity008.checked 33 (by change 33 < 64; omega)), hm.1, hm.2⟩

theorem a004_certificate : ARowCertificate a004 := by
  have hf : ARowFacts a004 := ⟨(boolean_record_at Validity008.checked 35 (by change 35 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt054_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt056_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt057_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e007_bounds)⟩
  have hm := parent_positive_of_checks a004 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 13 (by change 13 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 12 (by change 12 < 64; omega)))
    (comparison_record_at Strict060.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict060.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 3 (by change 3 < 64; omega)),
    cellM0_positive_of_check a004 (boolean_record_at Validity008.checked 36 (by change 36 < 64; omega)), hm.1, hm.2⟩

theorem a005_certificate : ARowCertificate a005 := by
  have hf : ARowFacts a005 := ⟨(boolean_record_at Validity008.checked 38 (by change 38 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt056_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt058_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt059_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e011_bounds)⟩
  have hm := parent_positive_of_checks a005 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 15 (by change 15 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 14 (by change 14 < 64; omega)))
    (comparison_record_at Strict060.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict060.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 4 (by change 4 < 64; omega)),
    cellM0_positive_of_check a005 (boolean_record_at Validity008.checked 39 (by change 39 < 64; omega)), hm.1, hm.2⟩

theorem a006_certificate : ARowCertificate a006 := by
  have hf : ARowFacts a006 := ⟨(boolean_record_at Validity008.checked 41 (by change 41 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt058_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt060_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt061_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e016_bounds)⟩
  have hm := parent_positive_of_checks a006 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 17 (by change 17 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 16 (by change 16 < 64; omega)))
    (comparison_record_at Strict060.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict060.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 5 (by change 5 < 64; omega)),
    cellM0_positive_of_check a006 (boolean_record_at Validity008.checked 42 (by change 42 < 64; omega)), hm.1, hm.2⟩

theorem a007_certificate : ARowCertificate a007 := by
  have hf : ARowFacts a007 := ⟨(boolean_record_at Validity008.checked 44 (by change 44 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt060_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt062_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt063_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e024_bounds)⟩
  have hm := parent_positive_of_checks a007 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 19 (by change 19 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 18 (by change 18 < 64; omega)))
    (comparison_record_at Strict060.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict060.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 6 (by change 6 < 64; omega)),
    cellM0_positive_of_check a007 (boolean_record_at Validity008.checked 45 (by change 45 < 64; omega)), hm.1, hm.2⟩

theorem a008_certificate : ARowCertificate a008 := by
  have hf : ARowFacts a008 := ⟨(boolean_record_at Validity008.checked 47 (by change 47 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt062_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt064_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt065_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e040_bounds)⟩
  have hm := parent_positive_of_checks a008 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 21 (by change 21 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 20 (by change 20 < 64; omega)))
    (comparison_record_at Strict060.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict060.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 7 (by change 7 < 64; omega)),
    cellM0_positive_of_check a008 (boolean_record_at Validity008.checked 48 (by change 48 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows001

#check Erdos993Lean.Analytic.V213.P03RowData.ARows001.a001_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows001.a001_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows001.a002_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows001.a002_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows001.a003_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows001.a003_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows001.a004_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows001.a004_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows001.a005_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows001.a005_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows001.a006_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows001.a006_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows001.a007_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows001.a007_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows001.a008_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows001.a008_certificate
