module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.ARows008
public import Erdos993Lean.Analytic.V213.P03RowData.ARows009
public import Erdos993Lean.Analytic.V213.P03RowData.ARows010
public import Erdos993Lean.Analytic.V213.P03RowData.ARows011
public import Erdos993Lean.Analytic.V213.P03RowData.ARows012
public import Erdos993Lean.Analytic.V213.P03RowData.ARows013
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity011
public import Erdos993Lean.ExactComparisons.F3All.Validity012
public import Erdos993Lean.ExactComparisons.F3All.Validity013

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ACover04

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List ARow := [a061, a062, a063, a064, a065, a066, a067, a068, a069, a070, a071, a072, a073, a074, a075, a076, a077, a078, a079, a080, a081, a082, a083, a084, a085, a086, a087, a088, a089, a090, a091, a092, a093, a094, a095, a096, a097, a098, a099, a100, a101, a102, a103, a104]

theorem all_certificates (r : ARow) (hr : r∈rows) : ARowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows008.a061_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows008.a062_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows008.a063_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows008.a064_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows009.a065_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows009.a066_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows009.a067_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows009.a068_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows009.a069_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows009.a070_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows009.a071_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows009.a072_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows010.a073_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows010.a074_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows010.a075_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows010.a076_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows010.a077_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows010.a078_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows010.a079_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows010.a080_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows011.a081_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows011.a082_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows011.a083_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows011.a084_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows011.a085_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows011.a086_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows011.a087_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows011.a088_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows012.a089_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows012.a090_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows012.a091_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows012.a092_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows012.a093_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows012.a094_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows012.a095_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows012.a096_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows013.a097_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows013.a098_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows013.a099_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows013.a100_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows013.a101_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows013.a102_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows013.a103_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows013.a104_certificate

theorem band_parameters (r : ARow) (hr : r∈rows) : r.D=(6/5 : Rat) ∧ r.ac.b.lam=(28/25 : Rat) ∧ r.bd.b.lam=(263/200 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 16 (by change 16 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 19 (by change 19 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 22 (by change 22 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 25 (by change 25 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 28 (by change 28 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 31 (by change 31 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 34 (by change 34 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 37 (by change 37 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 40 (by change 40 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 43 (by change 43 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 46 (by change 46 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 49 (by change 49 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 52 (by change 52 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 55 (by change 55 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 58 (by change 58 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 61 (by change 61 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 0 (by change 0 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 3 (by change 3 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 6 (by change 6 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 9 (by change 9 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 12 (by change 12 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 15 (by change 15 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 18 (by change 18 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 21 (by change 21 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 24 (by change 24 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 27 (by change 27 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 30 (by change 30 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 33 (by change 33 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 36 (by change 36 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 39 (by change 39 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 42 (by change 42 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 45 (by change 45 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 48 (by change 48 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 51 (by change 51 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 54 (by change 54 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 57 (by change 57 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 60 (by change 60 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity012.checked 63 (by change 63 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 2 (by change 2 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 5 (by change 5 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 8 (by change 8 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 11 (by change 11 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 14 (by change 14 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 17 (by change 17 < 64; omega))

theorem parent_cover : coverOK (0 : Rat) (3 : Rat) (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true := by
  change coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (27/64 : Rat)), ((27/64 : Rat), (15/32 : Rat)), ((15/32 : Rat), (63/128 : Rat)), ((63/128 : Rat), (33/64 : Rat)), ((33/64 : Rat), (69/128 : Rat)), ((69/128 : Rat), (9/16 : Rat)), ((9/16 : Rat), (75/128 : Rat)), ((75/128 : Rat), (39/64 : Rat)), ((39/64 : Rat), (81/128 : Rat)), ((81/128 : Rat), (21/32 : Rat)), ((21/32 : Rat), (87/128 : Rat)), ((87/128 : Rat), (45/64 : Rat)), ((45/64 : Rat), (93/128 : Rat)), ((93/128 : Rat), (3/4 : Rat)), ((3/4 : Rat), (99/128 : Rat)), ((99/128 : Rat), (51/64 : Rat)), ((51/64 : Rat), (105/128 : Rat)), ((105/128 : Rat), (27/32 : Rat)), ((27/32 : Rat), (111/128 : Rat)), ((111/128 : Rat), (57/64 : Rat)), ((57/64 : Rat), (15/16 : Rat)), ((15/16 : Rat), (63/64 : Rat)), ((63/64 : Rat), (33/32 : Rat)), ((33/32 : Rat), (69/64 : Rat)), ((69/64 : Rat), (9/8 : Rat)), ((9/8 : Rat), (75/64 : Rat)), ((75/64 : Rat), (39/32 : Rat)), ((39/32 : Rat), (81/64 : Rat)), ((81/64 : Rat), (21/16 : Rat)), ((21/16 : Rat), (87/64 : Rat)), ((87/64 : Rat), (45/32 : Rat)), ((45/32 : Rat), (93/64 : Rat)), ((93/64 : Rat), (3/2 : Rat)), ((3/2 : Rat), (99/64 : Rat)), ((99/64 : Rat), (51/32 : Rat)), ((51/32 : Rat), (27/16 : Rat)), ((27/16 : Rat), (57/32 : Rat)), ((57/32 : Rat), (15/8 : Rat)), ((15/8 : Rat), (63/32 : Rat)), ((63/32 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))]=true
  exact boolean_record_at Validity003.checked 39 (by change 39 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.ACover04

#check Erdos993Lean.Analytic.V213.P03RowData.ACover04.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover04.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.ACover04.band_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover04.band_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.ACover04.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover04.parent_cover
