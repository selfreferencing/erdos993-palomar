module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.ARows016
public import Erdos993Lean.Analytic.V213.P03RowData.ARows017
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity014

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ACover06

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List ARow := [a123, a124, a125, a126, a127, a128, a129, a130, a131, a132, a133, a134, a135]

theorem all_certificates (r : ARow) (hr : r∈rows) : ARowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows016.a123_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows016.a124_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows016.a125_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows016.a126_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows016.a127_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows016.a128_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows017.a129_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows017.a130_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows017.a131_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows017.a132_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows017.a133_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows017.a134_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows017.a135_certificate

theorem band_parameters (r : ARow) (hr : r∈rows) : r.D=(8/5 : Rat) ∧ r.ac.b.lam=(3/2 : Rat) ∧ r.bd.b.lam=(7/4 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 10 (by change 10 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 13 (by change 13 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 16 (by change 16 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 19 (by change 19 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 22 (by change 22 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 25 (by change 25 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 28 (by change 28 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 31 (by change 31 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 34 (by change 34 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 37 (by change 37 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 40 (by change 40 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 43 (by change 43 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 46 (by change 46 < 64; omega))

theorem parent_cover : coverOK (0 : Rat) (3 : Rat) (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true := by
  change coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (9/16 : Rat)), ((9/16 : Rat), (3/4 : Rat)), ((3/4 : Rat), (15/16 : Rat)), ((15/16 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))]=true
  exact boolean_record_at Validity003.checked 41 (by change 41 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.ACover06

#check Erdos993Lean.Analytic.V213.P03RowData.ACover06.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover06.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.ACover06.band_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover06.band_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.ACover06.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover06.parent_cover
