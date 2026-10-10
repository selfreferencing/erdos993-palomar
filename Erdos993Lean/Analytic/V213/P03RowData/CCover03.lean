module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.CRows002
public import Erdos993Lean.Analytic.V213.P03RowData.CRows003
public import Erdos993Lean.ExactComparisons.F3All.Validity003

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CCover03

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List CRow := [c012, c013, c014, c015, c016, c017]

theorem all_certificates (r : CRow) (hr : r∈rows) : CRowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows002.c012_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows002.c013_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows002.c014_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows002.c015_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows002.c016_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows003.c017_certificate

theorem cap_parameters (r : CRow) (hr : r∈rows) : r.D=(8/5 : Rat) ∧ r.left.b.lam=(7/4 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem parent_cover : coverOK (0 : Rat) (51/50 : Rat) (rows.map (fun r => (r.left.e.y,r.right.e.y)))=true := by
  change coverOK (0 : Rat) (51/50 : Rat) [((0 : Rat), (51/100 : Rat)), ((51/100 : Rat), (51/80 : Rat)), ((51/80 : Rat), (153/200 : Rat)), ((153/200 : Rat), (663/800 : Rat)), ((663/800 : Rat), (357/400 : Rat)), ((357/400 : Rat), (51/50 : Rat))]=true
  exact boolean_record_at Validity003.checked 33 (by change 33 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.CCover03

#check Erdos993Lean.Analytic.V213.P03RowData.CCover03.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover03.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.CCover03.cap_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover03.cap_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.CCover03.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover03.parent_cover
