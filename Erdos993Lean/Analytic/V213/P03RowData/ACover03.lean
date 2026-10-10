module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.ARows005
public import Erdos993Lean.Analytic.V213.P03RowData.ARows006
public import Erdos993Lean.Analytic.V213.P03RowData.ARows007
public import Erdos993Lean.Analytic.V213.P03RowData.ARows008
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity009
public import Erdos993Lean.ExactComparisons.F3All.Validity010
public import Erdos993Lean.ExactComparisons.F3All.Validity011

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ACover03

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List ARow := [a034, a035, a036, a037, a038, a039, a040, a041, a042, a043, a044, a045, a046, a047, a048, a049, a050, a051, a052, a053, a054, a055, a056, a057, a058, a059, a060]

theorem all_certificates (r : ARow) (hr : r∈rows) : ARowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows005.a034_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows005.a035_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows005.a036_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows005.a037_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows005.a038_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows005.a039_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows005.a040_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows006.a041_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows006.a042_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows006.a043_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows006.a044_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows006.a045_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows006.a046_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows006.a047_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows006.a048_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows007.a049_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows007.a050_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows007.a051_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows007.a052_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows007.a053_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows007.a054_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows007.a055_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows007.a056_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows008.a057_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows008.a058_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows008.a059_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows008.a060_certificate

theorem band_parameters (r : ARow) (hr : r∈rows) : r.D=(6/5 : Rat) ∧ r.ac.b.lam=(7/8 : Rat) ∧ r.bd.b.lam=(28/25 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 63 (by change 63 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 2 (by change 2 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 5 (by change 5 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 8 (by change 8 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 11 (by change 11 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 14 (by change 14 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 17 (by change 17 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 20 (by change 20 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 23 (by change 23 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 26 (by change 26 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 29 (by change 29 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 32 (by change 32 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 35 (by change 35 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 38 (by change 38 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 41 (by change 41 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 44 (by change 44 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 47 (by change 47 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 50 (by change 50 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 53 (by change 53 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 56 (by change 56 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 59 (by change 59 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity010.checked 62 (by change 62 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 1 (by change 1 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 4 (by change 4 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 7 (by change 7 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 10 (by change 10 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity011.checked 13 (by change 13 < 64; omega))

theorem parent_cover : coverOK (0 : Rat) (3 : Rat) (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true := by
  change coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/16 : Rat)), ((3/16 : Rat), (9/32 : Rat)), ((9/32 : Rat), (3/8 : Rat)), ((3/8 : Rat), (27/64 : Rat)), ((27/64 : Rat), (15/32 : Rat)), ((15/32 : Rat), (33/64 : Rat)), ((33/64 : Rat), (9/16 : Rat)), ((9/16 : Rat), (39/64 : Rat)), ((39/64 : Rat), (21/32 : Rat)), ((21/32 : Rat), (45/64 : Rat)), ((45/64 : Rat), (3/4 : Rat)), ((3/4 : Rat), (51/64 : Rat)), ((51/64 : Rat), (27/32 : Rat)), ((27/32 : Rat), (15/16 : Rat)), ((15/16 : Rat), (33/32 : Rat)), ((33/32 : Rat), (9/8 : Rat)), ((9/8 : Rat), (39/32 : Rat)), ((39/32 : Rat), (21/16 : Rat)), ((21/16 : Rat), (45/32 : Rat)), ((45/32 : Rat), (3/2 : Rat)), ((3/2 : Rat), (51/32 : Rat)), ((51/32 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))]=true
  exact boolean_record_at Validity003.checked 38 (by change 38 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.ACover03

#check Erdos993Lean.Analytic.V213.P03RowData.ACover03.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover03.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.ACover03.band_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover03.band_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.ACover03.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover03.parent_cover
