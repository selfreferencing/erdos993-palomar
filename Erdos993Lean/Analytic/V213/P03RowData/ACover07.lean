module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.ARows017
public import Erdos993Lean.Analytic.V213.P03RowData.ARows018
public import Erdos993Lean.Analytic.V213.P03RowData.ARows019
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity014
public import Erdos993Lean.ExactComparisons.F3All.Validity015

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ACover07

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List ARow := [a136, a137, a138, a139, a140, a141, a142, a143, a144, a145, a146, a147, a148]

theorem all_certificates (r : ARow) (hr : r∈rows) : ARowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows017.a136_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows018.a137_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows018.a138_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows018.a139_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows018.a140_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows018.a141_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows018.a142_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows018.a143_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows018.a144_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows019.a145_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows019.a146_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows019.a147_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows019.a148_certificate

theorem band_parameters (r : ARow) (hr : r∈rows) : r.D=(9/5 : Rat) ∧ r.ac.b.lam=(7/4 : Rat) ∧ r.bd.b.lam=(2 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 49 (by change 49 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 52 (by change 52 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 55 (by change 55 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 58 (by change 58 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 61 (by change 61 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 0 (by change 0 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 3 (by change 3 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 6 (by change 6 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 9 (by change 9 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 12 (by change 12 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 15 (by change 15 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 18 (by change 18 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 21 (by change 21 < 64; omega))

theorem parent_cover : coverOK (0 : Rat) (3 : Rat) (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true := by
  change coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (9/16 : Rat)), ((9/16 : Rat), (3/4 : Rat)), ((3/4 : Rat), (15/16 : Rat)), ((15/16 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))]=true
  exact boolean_record_at Validity003.checked 41 (by change 41 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.ACover07

#check Erdos993Lean.Analytic.V213.P03RowData.ACover07.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover07.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.ACover07.band_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover07.band_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.ACover07.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover07.parent_cover
