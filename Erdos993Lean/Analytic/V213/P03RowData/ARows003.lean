module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002
public import Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup004
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup005
public import Erdos993Lean.Analytic.V213.P03PointData.PointGroup006
public import Erdos993Lean.ExactComparisons.F3All.PositiveOutput002
public import Erdos993Lean.ExactComparisons.F3All.Strict061
public import Erdos993Lean.ExactComparisons.F3All.Strict062
public import Erdos993Lean.ExactComparisons.F3All.Validity001
public import Erdos993Lean.ExactComparisons.F3All.Validity009

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ARows003

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

theorem a017_certificate : ARowCertificate a017 := by
  have hf : ARowFacts a017 := ⟨(boolean_record_at Validity009.checked 10 (by change 10 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt053_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt057_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt082_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e006_bounds)⟩
  have hm := parent_positive_of_checks a017 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 39 (by change 39 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 38 (by change 38 < 64; omega)))
    (comparison_record_at Strict061.checked 14 (by change 14 < 16; omega)) (comparison_record_at Strict061.checked 15 (by change 15 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 16 (by change 16 < 64; omega)),
    cellM0_positive_of_check a017 (boolean_record_at Validity009.checked 11 (by change 11 < 64; omega)), hm.1, hm.2⟩

theorem a018_certificate : ARowCertificate a018 := by
  have hf : ARowFacts a018 := ⟨(boolean_record_at Validity009.checked 13 (by change 13 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt057_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt083_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt084_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e010_bounds)⟩
  have hm := parent_positive_of_checks a018 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 41 (by change 41 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 40 (by change 40 < 64; omega)))
    (comparison_record_at Strict062.checked 0 (by change 0 < 16; omega)) (comparison_record_at Strict062.checked 1 (by change 1 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 17 (by change 17 < 64; omega)),
    cellM0_positive_of_check a018 (boolean_record_at Validity009.checked 14 (by change 14 < 64; omega)), hm.1, hm.2⟩

theorem a019_certificate : ARowCertificate a019 := by
  have hf : ARowFacts a019 := ⟨(boolean_record_at Validity009.checked 16 (by change 16 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt083_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt059_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt085_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e012_bounds)⟩
  have hm := parent_positive_of_checks a019 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 43 (by change 43 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 42 (by change 42 < 64; omega)))
    (comparison_record_at Strict062.checked 2 (by change 2 < 16; omega)) (comparison_record_at Strict062.checked 3 (by change 3 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 18 (by change 18 < 64; omega)),
    cellM0_positive_of_check a019 (boolean_record_at Validity009.checked 17 (by change 17 < 64; omega)), hm.1, hm.2⟩

theorem a020_certificate : ARowCertificate a020 := by
  have hf : ARowFacts a020 := ⟨(boolean_record_at Validity009.checked 19 (by change 19 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt059_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt086_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt087_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup001.e014_bounds)⟩
  have hm := parent_positive_of_checks a020 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 45 (by change 45 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 44 (by change 44 < 64; omega)))
    (comparison_record_at Strict062.checked 4 (by change 4 < 16; omega)) (comparison_record_at Strict062.checked 5 (by change 5 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 19 (by change 19 < 64; omega)),
    cellM0_positive_of_check a020 (boolean_record_at Validity009.checked 20 (by change 20 < 64; omega)), hm.1, hm.2⟩

theorem a021_certificate : ARowCertificate a021 := by
  have hf : ARowFacts a021 := ⟨(boolean_record_at Validity009.checked 22 (by change 22 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt086_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt061_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt088_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e017_bounds)⟩
  have hm := parent_positive_of_checks a021 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 47 (by change 47 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 46 (by change 46 < 64; omega)))
    (comparison_record_at Strict062.checked 6 (by change 6 < 16; omega)) (comparison_record_at Strict062.checked 7 (by change 7 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 20 (by change 20 < 64; omega)),
    cellM0_positive_of_check a021 (boolean_record_at Validity009.checked 23 (by change 23 < 64; omega)), hm.1, hm.2⟩

theorem a022_certificate : ARowCertificate a022 := by
  have hf : ARowFacts a022 := ⟨(boolean_record_at Validity009.checked 25 (by change 25 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt061_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt063_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt089_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup002.e024_bounds)⟩
  have hm := parent_positive_of_checks a022 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 49 (by change 49 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 48 (by change 48 < 64; omega)))
    (comparison_record_at Strict062.checked 8 (by change 8 < 16; omega)) (comparison_record_at Strict062.checked 9 (by change 9 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 21 (by change 21 < 64; omega)),
    cellM0_positive_of_check a022 (boolean_record_at Validity009.checked 26 (by change 26 < 64; omega)), hm.1, hm.2⟩

theorem a023_certificate : ARowCertificate a023 := by
  have hf : ARowFacts a023 := ⟨(boolean_record_at Validity009.checked 28 (by change 28 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup004.pt063_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt090_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt091_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e034_bounds)⟩
  have hm := parent_positive_of_checks a023 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 51 (by change 51 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 50 (by change 50 < 64; omega)))
    (comparison_record_at Strict062.checked 10 (by change 10 < 16; omega)) (comparison_record_at Strict062.checked 11 (by change 11 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 22 (by change 22 < 64; omega)),
    cellM0_positive_of_check a023 (boolean_record_at Validity009.checked 29 (by change 29 < 64; omega)), hm.1, hm.2⟩

theorem a024_certificate : ARowCertificate a024 := by
  have hf : ARowFacts a024 := ⟨(boolean_record_at Validity009.checked 31 (by change 31 < 64; omega)), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt090_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup005.pt065_facts), (Erdos993Lean.Analytic.V213.P03PointData.PointGroup006.pt092_facts), (Erdos993Lean.Analytic.V213.P03PointData.ExpGroup003.e047_bounds)⟩
  have hm := parent_positive_of_checks a024 (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 53 (by change 53 < 64; omega))) (Comparison.ofRats_sound _ _ .lt (comparison_record_at PositiveOutput002.checked 52 (by change 52 < 64; omega)))
    (comparison_record_at Strict062.checked 12 (by change 12 < 16; omega)) (comparison_record_at Strict062.checked 13 (by change 13 < 16; omega))
  exact ⟨hf, (boolean_record_at Validity001.checked 23 (by change 23 < 64; omega)),
    cellM0_positive_of_check a024 (boolean_record_at Validity009.checked 32 (by change 32 < 64; omega)), hm.1, hm.2⟩


end Erdos993Lean.Analytic.V213.P03RowData.ARows003

#check Erdos993Lean.Analytic.V213.P03RowData.ARows003.a017_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows003.a017_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows003.a018_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows003.a018_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows003.a019_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows003.a019_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows003.a020_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows003.a020_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows003.a021_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows003.a021_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows003.a022_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows003.a022_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows003.a023_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows003.a023_certificate

#check Erdos993Lean.Analytic.V213.P03RowData.ARows003.a024_certificate
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ARows003.a024_certificate
