module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.ARows014
public import Erdos993Lean.Analytic.V213.P03RowData.ARows015
public import Erdos993Lean.Analytic.V213.P03RowData.ARows016
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity013
public import Erdos993Lean.ExactComparisons.F3All.Validity014

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ACover05

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List ARow := [a105, a106, a107, a108, a109, a110, a111, a112, a113, a114, a115, a116, a117, a118, a119, a120, a121, a122]

theorem all_certificates (r : ARow) (hr : r∈rows) : ARowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows014.a105_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows014.a106_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows014.a107_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows014.a108_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows014.a109_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows014.a110_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows014.a111_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows014.a112_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows015.a113_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows015.a114_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows015.a115_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows015.a116_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows015.a117_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows015.a118_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows015.a119_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows015.a120_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows016.a121_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows016.a122_certificate

theorem band_parameters (r : ARow) (hr : r∈rows) : r.D=(7/5 : Rat) ∧ r.ac.b.lam=(263/200 : Rat) ∧ r.bd.b.lam=(3/2 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 20 (by change 20 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 23 (by change 23 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 26 (by change 26 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 29 (by change 29 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 32 (by change 32 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 35 (by change 35 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 38 (by change 38 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 41 (by change 41 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 44 (by change 44 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 47 (by change 47 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 50 (by change 50 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 53 (by change 53 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 56 (by change 56 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 59 (by change 59 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity013.checked 62 (by change 62 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 1 (by change 1 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 4 (by change 4 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity014.checked 7 (by change 7 < 64; omega))

theorem parent_cover : coverOK (0 : Rat) (3 : Rat) (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true := by
  change coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (9/16 : Rat)), ((9/16 : Rat), (21/32 : Rat)), ((21/32 : Rat), (3/4 : Rat)), ((3/4 : Rat), (27/32 : Rat)), ((27/32 : Rat), (15/16 : Rat)), ((15/16 : Rat), (33/32 : Rat)), ((33/32 : Rat), (9/8 : Rat)), ((9/8 : Rat), (39/32 : Rat)), ((39/32 : Rat), (21/16 : Rat)), ((21/16 : Rat), (45/32 : Rat)), ((45/32 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))]=true
  exact boolean_record_at Validity003.checked 40 (by change 40 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.ACover05

#check Erdos993Lean.Analytic.V213.P03RowData.ACover05.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover05.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.ACover05.band_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover05.band_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.ACover05.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover05.parent_cover
