module

public import Erdos993Lean.Analytic.V213.FreeCountRationalTransfer
public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordDomains

/-!
The printed rational worksheet's Real meaning.
The suffix R denotes evaluation of the *worksheet inputs* in Real, not an
assertion that those inputs enclose log/exp or the continuous analytic curve.
Those analytic enclosure and curvature premises are separate work.  No finite
record family is evaluated or accepted by this file.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Erdos993Lean.ExactComparisons
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

theorem rmin_cast (a b : Rat) : (rmin a b : ℝ) = min (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · have hR : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only [rmin, if_pos h, min_eq_left hR]
  · have hR : (b : ℝ) ≤ a := by exact_mod_cast (le_of_lt (lt_of_not_ge h))
    simp only [rmin, if_neg h, min_eq_right hR]

theorem rmax_cast (a b : Rat) : (rmax a b : ℝ) = max (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · have hR : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only [rmax, if_pos h, max_eq_right hR]
  · have hR : (b : ℝ) ≤ a := by exact_mod_cast (le_of_lt (lt_of_not_ge h))
    simp only [rmax, if_neg h, max_eq_left hR]

theorem rabs_cast (a : Rat) : (rabs a : ℝ) = |(a : ℝ)| := by
  by_cases h : 0 ≤ a
  · have hR : (0 : ℝ) ≤ a := by exact_mod_cast h
    simp only [rabs, if_pos h, abs_of_nonneg hR]
  · have hR : (a : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h)
    simp only [rabs, if_neg h, Rat.cast_neg, abs_of_neg hR]

noncomputable def qAtR (lam : Rat) : ℝ := (lam : ℝ)/(1+(lam : ℝ))
noncomputable def pMinusR (p : Point) : ℝ := (p.b.lam : ℝ)/(p.e.hi+p.b.lam : ℝ)
noncomputable def pPlusR (p : Point) : ℝ := (p.b.lam : ℝ)/(p.e.lo+p.b.lam : ℝ)
noncomputable def ellMinusR (D : Rat) (p : Point) : ℝ :=
  (p.e.lo : ℝ)/p.b.lam - p.e.y*((1-pMinusR p)/((5*(D : ℝ)/12)*p.b.lo)+pMinusR p/p.f.lo)
noncomputable def rhoMinusR (p : Point) : ℝ :=
  qAtR p.b.lam*p.f.lo/(pMinusR p*p.b.hi)
noncomputable def rhoPlusR (p : Point) : ℝ :=
  min 1 (qAtR p.b.lam*p.f.hi/(pPlusR p*p.b.lo))
noncomputable def kPlusR (D : Rat) (p : Point) : ℝ :=
  (1-pMinusR p)/D+(5/12)*(p.b.hi : ℝ)*pMinusR p/p.f.lo
noncomputable def omegaAtR (rho : ℝ) : ℝ := 1-(7*rho+5/rho)/12

theorem qAt_cast (lam : Rat) : (qAt lam : ℝ) = qAtR lam := by simp [qAt, qAtR]
theorem pMinus_cast (p : Point) : (pMinus p : ℝ) = pMinusR p := by simp [pMinus, pMinusR]
theorem pPlus_cast (p : Point) : (pPlus p : ℝ) = pPlusR p := by simp [pPlus, pPlusR]
theorem ellMinus_cast (D : Rat) (p : Point) : (ellMinus D p : ℝ) = ellMinusR D p := by
  simp [ellMinus, ellMinusR, pMinus_cast]
theorem rhoMinus_cast (p : Point) : (rhoMinus p : ℝ) = rhoMinusR p := by
  simp [rhoMinus, rhoMinusR, qAt_cast, pMinus_cast]
theorem rhoPlus_cast (p : Point) : (rhoPlus p : ℝ) = rhoPlusR p := by
  simp [rhoPlus, rhoPlusR, rmin_cast, qAt_cast, pPlus_cast]
theorem kPlus_cast (D : Rat) (p : Point) : (kPlus D p : ℝ) = kPlusR D p := by
  simp [kPlus, kPlusR, pMinus_cast]
theorem omegaAt_cast (rho : Rat) : (omegaAt rho : ℝ) = omegaAtR (rho : ℝ) := by
  simp [omegaAt, omegaAtR]

noncomputable def faceEllR (r : CRow) : ℝ :=
  min (ellMinusR r.D r.left) (ellMinusR r.D r.right) -
    (9/16)*((r.right.e.y : ℝ)-r.left.e.y)^2
noncomputable def faceL0R (r : CRow) : ℝ := min 0 (faceEllR r)
noncomputable def faceDenR (r : CRow) : ℝ := 1+(jCap r.D : ℝ)*faceL0R r
noncomputable def faceS0R (r : CRow) : ℝ := max 0 (1-1/(r.left.e.lo : ℝ)-pPlusR r.left)
noncomputable def faceBalanceR (r : CRow) : ℝ :=
  2*(faceS0R r)^2+(5/7)*(r.left.b.hi : ℝ)*pPlusR r.left*faceL0R r/faceDenR r

theorem faceEll_cast (r : CRow) : (faceEll r : ℝ) = faceEllR r := by
  simp [faceEll, faceEllR, rmin_cast, ellMinus_cast]
theorem faceL0_cast (r : CRow) : (faceL0 r : ℝ) = faceL0R r := by
  simp [faceL0, faceL0R, rmin_cast, faceEll_cast]
theorem faceDen_cast (r : CRow) : (faceDen r : ℝ) = faceDenR r := by
  simp [faceDen, faceDenR, faceL0_cast]
theorem faceS0_cast (r : CRow) : (faceS0 r : ℝ) = faceS0R r := by
  simp [faceS0, faceS0R, rmax_cast, pPlus_cast]
theorem faceBalance_cast (r : CRow) : (faceBalance r : ℝ) = faceBalanceR r := by
  simp [faceBalance, faceBalanceR, faceS0_cast, pPlus_cast, faceL0_cast, faceDen_cast]

noncomputable def cellWidthR (r : ARow) : ℝ := ((r.bd.e.y : ℝ)-r.ac.e.y)/2
noncomputable def cellKR (r : ARow) : ℝ :=
  max (kPlusR r.D r.ad) (kPlusR r.D r.bd)+(15/256)*((r.bd.b.lam : ℝ)-r.ac.b.lam)^2
noncomputable def cellDeltaR (r : ARow) : ℝ :=
  (5/12)*((r.bd.b.lo : ℝ)*r.ac.e.lo/r.bd.b.lam+
    2*((r.bd.b.lo : ℝ)/qAtR r.bd.b.lam)^2/(1+(r.bd.b.lam : ℝ)))-r.bd.e.y*cellKR r
noncomputable def cellTR (r : ARow) : ℝ :=
  ((1+(r.bd.b.lam : ℝ))/(r.mid.hi+r.bd.b.lam : ℝ)-1)/r.D+
    (7/12)*(r.mid.y : ℝ)*r.mid.lo/((1+(r.bd.b.lam : ℝ))*r.bd.b.hi)
noncomputable def cellTMinusR (r : ARow) : ℝ :=
  -(1+(r.bd.b.lam : ℝ))*r.mid.hi/(r.D*(r.mid.lo+r.bd.b.lam : ℝ)^2)+
    (7/12)*(1+(r.mid.y : ℝ))*r.mid.lo/((1+(r.bd.b.lam : ℝ))*r.bd.b.hi)
noncomputable def cellTPlusR (r : ARow) : ℝ :=
  -(1+(r.bd.b.lam : ℝ))*r.mid.lo/(r.D*(r.mid.hi+r.bd.b.lam : ℝ)^2)+
    (7/12)*(1+(r.mid.y : ℝ))*r.mid.hi/((1+(r.bd.b.lam : ℝ))*r.bd.b.lo)
noncomputable def cellM0R (r : ARow) : ℝ :=
  (7/12)*(2+(r.ac.e.y : ℝ))*r.ac.e.lo/((1+(r.bd.b.lam : ℝ))*r.bd.b.hi)-1/10
noncomputable def cellJ0R (r : ARow) : ℝ := max |cellTMinusR r| |cellTPlusR r|
noncomputable def cellPsiR (r : ARow) : ℝ :=
  if cellJ0R r ≤ cellM0R r*cellWidthR r then (cellJ0R r)^2/(2*cellM0R r)
  else cellJ0R r*cellWidthR r-cellM0R r*(cellWidthR r)^2/2
noncomputable def cellEpsilonR (r : ARow) : ℝ := 7/12-(12/5)*(r.m : ℝ)^2
noncomputable def cellBalanceR (r : ARow) : ℝ :=
  min (omegaAtR (rhoMinusR r.bd)) (omegaAtR (rhoPlusR r.ac))+cellTR r-cellPsiR r+
  cellEpsilonR r*max 0 (1-(r.bd.e.y : ℝ)/r.ac.b.lo)-
  ((r.bd.e.y : ℝ)/qAtR r.ac.b.lam)*(max 0 (cellKR r-r.m))^2/cellDeltaR r

theorem cellWidth_cast (r : ARow) : (cellWidth r : ℝ) = cellWidthR r := by
  simp [cellWidth, cellWidthR]
theorem cellK_cast (r : ARow) : (cellK r : ℝ) = cellKR r := by
  simp [cellK, cellKR, rmax_cast, kPlus_cast]
theorem cellDelta_cast (r : ARow) : (cellDelta r : ℝ) = cellDeltaR r := by
  simp [cellDelta, cellDeltaR, qAt_cast, cellK_cast]
theorem cellT_cast (r : ARow) : (cellT r : ℝ) = cellTR r := by simp [cellT, cellTR]
theorem cellTMinus_cast (r : ARow) : (cellTMinus r : ℝ) = cellTMinusR r := by
  simp [cellTMinus, cellTMinusR]
theorem cellTPlus_cast (r : ARow) : (cellTPlus r : ℝ) = cellTPlusR r := by
  simp [cellTPlus, cellTPlusR]
theorem cellM0_cast (r : ARow) : (cellM0 r : ℝ) = cellM0R r := by simp [cellM0, cellM0R]
theorem cellJ0_cast (r : ARow) : (cellJ0 r : ℝ) = cellJ0R r := by
  simp [cellJ0, cellJ0R, rmax_cast, rabs_cast, cellTMinus_cast, cellTPlus_cast]
theorem cellPsi_cast (r : ARow) : (cellPsi r : ℝ) = cellPsiR r := by
  have hh : cellJ0 r ≤ cellM0 r*cellWidth r ↔ cellJ0R r ≤ cellM0R r*cellWidthR r := by
    rw [← cellJ0_cast, ← cellM0_cast, ← cellWidth_cast]
    norm_cast
  by_cases h : cellJ0 r ≤ cellM0 r*cellWidth r
  · simp [cellPsi, cellPsiR, h, hh.mp h, cellJ0_cast, cellM0_cast, cellWidth_cast]
  · have hR : ¬cellJ0R r ≤ cellM0R r*cellWidthR r := fun hR => h (hh.mpr hR)
    simp [cellPsi, cellPsiR, h, hR, cellJ0_cast, cellM0_cast, cellWidth_cast]
theorem cellEpsilon_cast (r : ARow) : (cellEpsilon r : ℝ) = cellEpsilonR r := by
  simp [cellEpsilon, cellEpsilonR]
theorem cellBalance_cast (r : ARow) : (cellBalance r : ℝ) = cellBalanceR r := by
  simp [cellBalance, cellBalanceR, rmin_cast, rmax_cast, omegaAt_cast,
    rhoMinus_cast, rhoPlus_cast, cellT_cast, cellPsi_cast, cellEpsilon_cast,
    qAt_cast, cellK_cast, cellDelta_cast]

/-- A printed positive integer margin and its actual strict comparison suffice. -/
theorem millionth_margin_positive {g x : Rat} (hg : 0 < g)
    (h : (Comparison.ofRats (g/1000000) x .lt).check = true) : (0 : ℝ) < x := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hm : (0 : ℝ) < (g/1000000 : Rat) := by
    exact_mod_cast (div_pos hg (show (0 : Rat) < 1000000 by norm_num))
  exact hm.trans (ofRats_lt_real h)

theorem face_L_positive_of_checks (r : CRow) {g : Rat} (hg : 0 < g)
    (h : (Comparison.ofRats (g/1000000) (faceEll r) .lt).check = true) :
    0 < faceEllR r := by
  simpa only [faceEll_cast] using millionth_margin_positive hg h

theorem face_C_positive_of_checks (r : CRow) {g gp : Rat} (hg : 0 < g) (hgp : 0 < gp)
    (hd : (Comparison.ofRats (gp/1000000) (faceDen r) .lt).check = true)
    (hb : (Comparison.ofRats (g/1000000) (faceBalance r) .lt).check = true) :
    0 < faceDenR r ∧ 0 < faceBalanceR r := by
  constructor
  · simpa only [faceDen_cast] using millionth_margin_positive hgp hd
  · simpa only [faceBalance_cast] using millionth_margin_positive hg hb

theorem parent_positive_of_checks (r : ARow) {g gp : Rat} (hg : 0 < g) (hgp : 0 < gp)
    (hd : (Comparison.ofRats (gp/1000000) (cellDelta r) .lt).check = true)
    (hb : (Comparison.ofRats (g/1000000) (cellBalance r) .lt).check = true) :
    0 < cellDeltaR r ∧ 0 < cellBalanceR r := by
  constructor
  · simpa only [cellDelta_cast] using millionth_margin_positive hgp hd
  · simpa only [cellBalance_cast] using millionth_margin_positive hg hb

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rmin_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rmin_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rmax_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rmax_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rabs_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rabs_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.qAt_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.qAt_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pMinus_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pMinus_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pPlus_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pPlus_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ellMinus_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ellMinus_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rhoMinus_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rhoMinus_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rhoPlus_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.rhoPlus_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.kPlus_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.kPlus_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.omegaAt_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.omegaAt_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceEll_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceEll_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceL0_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceL0_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceDen_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceDen_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceS0_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceS0_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceBalance_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.faceBalance_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellWidth_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellWidth_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellK_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellK_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellDelta_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellDelta_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellT_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellT_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellTMinus_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellTMinus_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellTPlus_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellTPlus_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellM0_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellM0_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellJ0_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellJ0_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellPsi_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellPsi_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellEpsilon_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellEpsilon_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellBalance_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellBalance_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.millionth_margin_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.millionth_margin_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.face_L_positive_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.face_L_positive_of_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.face_C_positive_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.face_C_positive_of_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.parent_positive_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.parent_positive_of_checks
