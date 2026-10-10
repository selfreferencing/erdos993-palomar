module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.CRows003
public import Erdos993Lean.Analytic.V213.P03RowData.CRows004
public import Erdos993Lean.ExactComparisons.F3All.Validity003

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CCover04

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List CRow := [c018, c019, c020, c021, c022, c023, c024, c025]

theorem all_certificates (r : CRow) (hr : r∈rows) : CRowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows003.c018_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows003.c019_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows003.c020_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows003.c021_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows003.c022_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows003.c023_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows003.c024_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows004.c025_certificate

theorem cap_parameters (r : CRow) (hr : r∈rows) : r.D=(9/5 : Rat) ∧ r.left.b.lam=(2 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem parent_cover : coverOK (0 : Rat) (11/10 : Rat) (rows.map (fun r => (r.left.e.y,r.right.e.y)))=true := by
  change coverOK (0 : Rat) (11/10 : Rat) [((0 : Rat), (11/20 : Rat)), ((11/20 : Rat), (11/16 : Rat)), ((11/16 : Rat), (121/160 : Rat)), ((121/160 : Rat), (33/40 : Rat)), ((33/40 : Rat), (55/64 : Rat)), ((55/64 : Rat), (143/160 : Rat)), ((143/160 : Rat), (77/80 : Rat)), ((77/80 : Rat), (11/10 : Rat))]=true
  exact boolean_record_at Validity003.checked 34 (by change 34 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.CCover04

#check Erdos993Lean.Analytic.V213.P03RowData.CCover04.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover04.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.CCover04.cap_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover04.cap_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.CCover04.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover04.parent_cover
