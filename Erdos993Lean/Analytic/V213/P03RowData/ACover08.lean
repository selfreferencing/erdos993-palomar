module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.ARows019
public import Erdos993Lean.Analytic.V213.P03RowData.ARows020
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity015

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ACover08

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List ARow := [a149, a150, a151, a152, a153, a154, a155, a156, a157, a158, a159]

theorem all_certificates (r : ARow) (hr : r∈rows) : ARowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows019.a149_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows019.a150_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows019.a151_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows019.a152_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows020.a153_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows020.a154_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows020.a155_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows020.a156_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows020.a157_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows020.a158_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows020.a159_certificate

theorem band_parameters (r : ARow) (hr : r∈rows) : r.D=(21/10 : Rat) ∧ r.ac.b.lam=(2 : Rat) ∧ r.bd.b.lam=(7/3 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 24 (by change 24 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 27 (by change 27 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 30 (by change 30 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 33 (by change 33 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 36 (by change 36 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 39 (by change 39 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 42 (by change 42 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 45 (by change 45 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 48 (by change 48 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 51 (by change 51 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity015.checked 54 (by change 54 < 64; omega))

theorem parent_cover : coverOK (0 : Rat) (3 : Rat) (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true := by
  change coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (3/4 : Rat)), ((3/4 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))]=true
  exact boolean_record_at Validity003.checked 42 (by change 42 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.ACover08

#check Erdos993Lean.Analytic.V213.P03RowData.ACover08.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover08.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.ACover08.band_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover08.band_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.ACover08.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover08.parent_cover
