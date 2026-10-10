module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.CRows001
public import Erdos993Lean.Analytic.V213.P03RowData.CRows002
public import Erdos993Lean.ExactComparisons.F3All.Validity003

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CCover02

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List CRow := [c007, c008, c009, c010, c011]

theorem all_certificates (r : CRow) (hr : r∈rows) : CRowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows001.c007_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows001.c008_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows002.c009_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows002.c010_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows002.c011_certificate

theorem cap_parameters (r : CRow) (hr : r∈rows) : r.D=(7/5 : Rat) ∧ r.left.b.lam=(3/2 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem parent_cover : coverOK (0 : Rat) (23/25 : Rat) (rows.map (fun r => (r.left.e.y,r.right.e.y)))=true := by
  change coverOK (0 : Rat) (23/25 : Rat) [((0 : Rat), (23/50 : Rat)), ((23/50 : Rat), (69/100 : Rat)), ((69/100 : Rat), (299/400 : Rat)), ((299/400 : Rat), (161/200 : Rat)), ((161/200 : Rat), (23/25 : Rat))]=true
  exact boolean_record_at Validity003.checked 32 (by change 32 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.CCover02

#check Erdos993Lean.Analytic.V213.P03RowData.CCover02.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover02.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.CCover02.cap_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover02.cap_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.CCover02.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover02.parent_cover
