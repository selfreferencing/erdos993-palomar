module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowAC
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowCA

/-!
Finite-record interfaces and continuous cover consumers. Each
certificate retains point facts and the actual worksheet outputs separately.
The M0 sign comes from its own Validity Boolean, not the PositiveOutput
integer-margin family. Cover correctness is the actual ordered coverOK
predicate; every chosen record is recovered with its membership proof.
This file does not instantiate a concrete list or finish the global scalar
ell/denominator closure or the C-row interpolation premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Set Erdos993Lean.ExactComparisons.F3All

structure ARowCertificate (r : ARow) : Prop extends ARowFacts r where
  m_range : decide (0≤r.m ∧ r.m≤49/100)=true
  M0_positive : 0<cellM0R r
  delta_positive : 0<cellDeltaR r
  balance_positive : 0<cellBalanceR r

structure CRowCertificate (r : CRow) : Prop extends CRowFacts r where
  margin : 0<faceEllR r ∨ (0<faceDenR r ∧ 0<faceBalanceR r)

theorem cellM0_positive_of_check (r : ARow)
    (h : decide (0<cellM0 r)=true) : 0<cellM0R r := by
  have hh : 0<cellM0 r := of_decide_eq_true h
  have hR : (0:ℝ)<(cellM0 r : ℝ) := by exact_mod_cast hh
  simpa only [cellM0_cast] using hR

theorem ARowCertificate.AC_positive {r : ARow} (hr : ARowCertificate r)
    (hD : (6/5:ℝ)≤r.D) {lam t y : ℝ}
    (hlam : lam∈Icc (r.ac.b.lam : ℝ) (r.bd.b.lam : ℝ))
    (hycell : y∈Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ))
    (ht : 0≤t) (hy : 0<y) (hfeasible : logMass lam t≤y)
    (hell : -(3/4:ℝ)<ell (r.D : ℝ) lam y)
    (hden : 0<1+ell (r.D : ℝ) lam y*J lam t) :
    0<AC (r.D : ℝ) lam t y :=
  hr.toARowFacts.AC_positive hD hr.m_range hr.M0_positive hr.delta_positive
    hr.balance_positive hlam hycell ht hy hfeasible hell hden

theorem CRowCertificate.CA_face_positive {r : CRow} (hr : CRowCertificate r)
    {lam t y : ℝ} (hlam : 0<lam) (hlamu : lam≤(r.left.b.lam : ℝ))
    (ht : 0≤t) (hy : (r.left.e.y : ℝ)≤y) (hface : y=logMass lam t)
    (hEll : faceEllR r≤ell (r.D : ℝ) lam y)
    (hJ : J lam t<(jCap r.D : ℝ)) : 0<CA (r.D : ℝ) lam t y := by
  rcases hr.margin with hL | hC
  · exact hr.toCRowFacts.CA_positive_of_L hL hlam ht
      (by rw [hface]) hEll
  · exact hr.toCRowFacts.CA_face_positive hC.1 hC.2 hlam hlamu ht hy hface hEll hJ

/-- One actual parent cover at a fixed printed activity band. The row D/a/b
equalities are explicit, separate from the ordered parent cover. -/
theorem AC_positive_on_row_cover (rows : List ARow) (D a b lo hi : Rat)
    (hrows : ∀r∈rows, ARowCertificate r)
    (hband : ∀r∈rows, r.D=D ∧ r.ac.b.lam=a ∧ r.bd.b.lam=b)
    (hcover : coverOK lo hi (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true)
    (hD : (6/5:ℝ)≤D) {lam t y : ℝ}
    (hlam : lam∈Icc (a : ℝ) (b : ℝ))
    (hycell : y∈Icc (lo : ℝ) (hi : ℝ))
    (ht : 0≤t) (hy : 0<y) (hfeasible : logMass lam t≤y)
    (hell : -(3/4:ℝ)<ell (D : ℝ) lam y)
    (hden : 0<1+ell (D : ℝ) lam y*J lam t) : 0<AC (D : ℝ) lam t y := by
  obtain ⟨r, hr, hyr⟩ := coverOK_record (fun r : ARow => r.ac.e.y)
    (fun r => r.bd.e.y) rows hcover hycell.1 hycell.2
  rcases hband r hr with ⟨hRD,hra,hrb⟩
  have hh := (hrows r hr).AC_positive
    (by simpa only [hRD] using hD)
    (by simpa only [hra,hrb] using hlam) hyr ht hy hfeasible
    (by simpa only [hRD] using hell) (by simpa only [hRD] using hden)
  simpa only [hRD] using hh

/-- One actual C-row cover. The analytic interpolation consequence is kept
pointwise and local, so covering does not hide its remaining proof. -/
theorem CA_face_positive_on_row_cover (rows : List CRow) (D u lo hi : Rat)
    (hrows : ∀r∈rows, CRowCertificate r)
    (hcap : ∀r∈rows, r.D=D ∧ r.left.b.lam=u)
    (hcover : coverOK lo hi (rows.map (fun r => (r.left.e.y,r.right.e.y)))=true)
    {lam t y : ℝ} (hlam : 0<lam) (hlamu : lam≤(u : ℝ))
    (hycell : y∈Icc (lo : ℝ) (hi : ℝ)) (ht : 0≤t)
    (hface : y=logMass lam t) (hJ : J lam t<(jCap D : ℝ))
    (hEll : ∀r∈rows, (r.left.e.y : ℝ)≤y → y≤(r.right.e.y : ℝ) →
      faceEllR r≤ell (D : ℝ) lam y) : 0<CA (D : ℝ) lam t y := by
  obtain ⟨r, hr, hyr⟩ := coverOK_record (fun r : CRow => r.left.e.y)
    (fun r => r.right.e.y) rows hcover hycell.1 hycell.2
  rcases hcap r hr with ⟨hRD,hru⟩
  have hh := (hrows r hr).CA_face_positive hlam
    (by simpa only [hru] using hlamu) ht hyr.1 hface
    (by simpa only [hRD] using hEll r hr hyr.1 hyr.2)
    (by simpa only [hRD] using hJ)
  simpa only [hRD] using hh

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellM0_positive_of_check
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellM0_positive_of_check
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowCertificate.AC_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowCertificate.AC_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowCertificate.CA_face_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowCertificate.CA_face_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.AC_positive_on_row_cover
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.AC_positive_on_row_cover
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CA_face_positive_on_row_cover
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CA_face_positive_on_row_cover
