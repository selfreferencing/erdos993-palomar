module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.ARows002
public import Erdos993Lean.Analytic.V213.P03RowData.ARows003
public import Erdos993Lean.Analytic.V213.P03RowData.ARows004
public import Erdos993Lean.Analytic.V213.P03RowData.ARows005
public import Erdos993Lean.ExactComparisons.F3All.Validity003
public import Erdos993Lean.ExactComparisons.F3All.Validity009

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.ACover02

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List ARow := [a016, a017, a018, a019, a020, a021, a022, a023, a024, a025, a026, a027, a028, a029, a030, a031, a032, a033]

theorem all_certificates (r : ARow) (hr : r∈rows) : ARowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows002.a016_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows003.a017_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows003.a018_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows003.a019_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows003.a020_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows003.a021_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows003.a022_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows003.a023_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows003.a024_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows004.a025_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows004.a026_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows004.a027_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows004.a028_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows004.a029_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows004.a030_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows004.a031_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows004.a032_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.ARows005.a033_certificate

theorem band_parameters (r : ARow) (hr : r∈rows) : r.D=(6/5 : Rat) ∧ r.ac.b.lam=(3/5 : Rat) ∧ r.bd.b.lam=(7/8 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 9 (by change 9 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 12 (by change 12 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 15 (by change 15 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 18 (by change 18 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 21 (by change 21 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 24 (by change 24 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 27 (by change 27 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 30 (by change 30 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 33 (by change 33 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 36 (by change 36 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 39 (by change 39 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 42 (by change 42 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 45 (by change 45 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 48 (by change 48 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 51 (by change 51 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 54 (by change 54 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 57 (by change 57 < 64; omega))
  · exact of_decide_eq_true (boolean_record_at Validity009.checked 60 (by change 60 < 64; omega))

theorem parent_cover : coverOK (0 : Rat) (3 : Rat) (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true := by
  change coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/16 : Rat)), ((3/16 : Rat), (9/32 : Rat)), ((9/32 : Rat), (21/64 : Rat)), ((21/64 : Rat), (3/8 : Rat)), ((3/8 : Rat), (27/64 : Rat)), ((27/64 : Rat), (15/32 : Rat)), ((15/32 : Rat), (9/16 : Rat)), ((9/16 : Rat), (21/32 : Rat)), ((21/32 : Rat), (3/4 : Rat)), ((3/4 : Rat), (27/32 : Rat)), ((27/32 : Rat), (15/16 : Rat)), ((15/16 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (9/4 : Rat)), ((9/4 : Rat), (3 : Rat))]=true
  exact boolean_record_at Validity003.checked 37 (by change 37 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.ACover02

#check Erdos993Lean.Analytic.V213.P03RowData.ACover02.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover02.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.ACover02.band_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover02.band_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.ACover02.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.ACover02.parent_cover
