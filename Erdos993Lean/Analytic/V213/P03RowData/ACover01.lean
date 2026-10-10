module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.ARows001
public import Erdos993Lean.Analytic.V213.P03RowData.ARows002
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity008
public import Erdos993Lean.ExactComparisons.F3All.Validity009

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ACover01

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List ARow := [a001, a002, a003, a004, a005, a006, a007, a008, a009, a010, a011, a012, a013, a014, a015]

theorem all_certificates (r : ARow) (hr : r∈rows) : ARowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows001.a001_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows001.a002_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows001.a003_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows001.a004_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows001.a005_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows001.a006_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows001.a007_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows001.a008_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows002.a009_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows002.a010_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows002.a011_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows002.a012_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows002.a013_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows002.a014_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows002.a015_certificate

theorem band_parameters (r : ARow) (hr : r∈rows) : r.D=(6/5 : Rat) ∧ r.ac.b.lam=(1/3 : Rat) ∧ r.bd.b.lam=(3/5 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 28 (by change 28 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 31 (by change 31 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 34 (by change 34 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 37 (by change 37 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 40 (by change 40 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 43 (by change 43 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 46 (by change 46 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 49 (by change 49 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 52 (by change 52 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 55 (by change 55 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 58 (by change 58 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity008.checked 61 (by change 61 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 0 (by change 0 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 3 (by change 3 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 6 (by change 6 < 64; omega))

theorem parent_cover : coverOK (0 : Rat) (3 : Rat) (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true := by
  change coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/32 : Rat)), ((3/32 : Rat), (3/16 : Rat)), ((3/16 : Rat), (15/64 : Rat)), ((15/64 : Rat), (9/32 : Rat)), ((9/32 : Rat), (3/8 : Rat)), ((3/8 : Rat), (15/32 : Rat)), ((15/32 : Rat), (9/16 : Rat)), ((9/16 : Rat), (3/4 : Rat)), ((3/4 : Rat), (15/16 : Rat)), ((15/16 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (15/8 : Rat)), ((15/8 : Rat), (9/4 : Rat)), ((9/4 : Rat), (3 : Rat))]=true
  exact boolean_record_at Validity003.checked 36 (by change 36 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.ACover01

#check Erdos993Lean.Analytic.V213.P03RowData.ACover01.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover01.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.ACover01.band_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover01.band_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.ACover01.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover01.parent_cover
