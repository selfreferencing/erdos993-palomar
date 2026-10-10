module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.CRows001
public import Erdos993Lean.ExactComparisons.F3All.Validity003

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CCover01

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List CRow := [c001, c002, c003, c004, c005, c006]

theorem all_certificates (r : CRow) (hr : r∈rows) : CRowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows001.c001_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows001.c002_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows001.c003_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows001.c004_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows001.c005_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows001.c006_certificate

theorem cap_parameters (r : CRow) (hr : r∈rows) : r.D=(6/5 : Rat) ∧ r.left.b.lam=(263/200 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem parent_cover : coverOK (0 : Rat) (21/25 : Rat) (rows.map (fun r => (r.left.e.y,r.right.e.y)))=true := by
  change coverOK (0 : Rat) (21/25 : Rat) [((0 : Rat), (21/50 : Rat)), ((21/50 : Rat), (63/100 : Rat)), ((63/100 : Rat), (273/400 : Rat)), ((273/400 : Rat), (147/200 : Rat)), ((147/200 : Rat), (63/80 : Rat)), ((63/80 : Rat), (21/25 : Rat))]=true
  exact boolean_record_at Validity003.checked 31 (by change 31 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.CCover01

#check Erdos993Lean.Analytic.V213.P03RowData.CCover01.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover01.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.CCover01.cap_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover01.cap_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.CCover01.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover01.parent_cover
