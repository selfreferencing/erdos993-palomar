module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCertificates
public import Erdos993Lean.Analytic.V213.P03RowData.CRows004
public import Erdos993Lean.Analytic.V213.P03RowData.CRows005
public import Erdos993Lean.Analytic.V213.P03RowData.CRows006
public import Erdos993Lean.ExactComparisons.F3All.Validity003

/-! Row consumers.
Existing checked records are selected structurally, not replayed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P03RowData.CCover05

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

def rows : List CRow := [c026, c027, c028, c029, c030, c031, c032, c033, c034, c035, c036, c037, c038, c039, c040, c041, c042, c043]

theorem all_certificates (r : CRow) (hr : r∈rows) : CRowCertificate r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows004.c026_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows004.c027_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows004.c028_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows004.c029_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows004.c030_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows004.c031_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows004.c032_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows005.c033_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows005.c034_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows005.c035_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows005.c036_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows005.c037_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows005.c038_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows005.c039_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows005.c040_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows006.c041_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows006.c042_certificate
  · exact Erdos993Lean.Analytic.V213.P03RowData.CRows006.c043_certificate

theorem cap_parameters (r : CRow) (hr : r∈rows) : r.D=(21/10 : Rat) ∧ r.left.b.lam=(7/3 : Rat) := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem parent_cover : coverOK (0 : Rat) (121/100 : Rat) (rows.map (fun r => (r.left.e.y,r.right.e.y)))=true := by
  change coverOK (0 : Rat) (121/100 : Rat) [((0 : Rat), (121/400 : Rat)), ((121/400 : Rat), (121/200 : Rat)), ((121/200 : Rat), (121/160 : Rat)), ((121/160 : Rat), (2541/3200 : Rat)), ((2541/3200 : Rat), (5203/6400 : Rat)), ((5203/6400 : Rat), (1331/1600 : Rat)), ((1331/1600 : Rat), (1089/1280 : Rat)), ((1089/1280 : Rat), (11011/12800 : Rat)), ((11011/12800 : Rat), (2783/3200 : Rat)), ((2783/3200 : Rat), (11253/12800 : Rat)), ((11253/12800 : Rat), (5687/6400 : Rat)), ((5687/6400 : Rat), (363/400 : Rat)), ((363/400 : Rat), (5929/6400 : Rat)), ((5929/6400 : Rat), (121/128 : Rat)), ((121/128 : Rat), (1573/1600 : Rat)), ((1573/1600 : Rat), (3267/3200 : Rat)), ((3267/3200 : Rat), (847/800 : Rat)), ((847/800 : Rat), (121/100 : Rat))]=true
  exact boolean_record_at Validity003.checked 35 (by change 35 < 64; omega)

end Erdos993Lean.Analytic.V213.P03RowData.CCover05

#check Erdos993Lean.Analytic.V213.P03RowData.CCover05.all_certificates
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover05.all_certificates

#check Erdos993Lean.Analytic.V213.P03RowData.CCover05.cap_parameters
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover05.cap_parameters

#check Erdos993Lean.Analytic.V213.P03RowData.CCover05.parent_cover
#print axioms Erdos993Lean.Analytic.V213.P03RowData.CCover05.parent_cover
