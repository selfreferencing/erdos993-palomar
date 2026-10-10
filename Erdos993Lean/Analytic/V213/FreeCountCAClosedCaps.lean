module

public import Erdos993Lean.Analytic.V213.FreeCountACClosedCaps
public import Erdos993Lean.Analytic.V213.FreeCountCRowInterpolation
public import Erdos993Lean.Analytic.V213.FreeCountCABoundaryLastCaps
public import Erdos993Lean.Analytic.V213.P03RowData.CCover01
public import Erdos993Lean.Analytic.V213.P03RowData.CCover02
public import Erdos993Lean.Analytic.V213.P03RowData.CCover03
public import Erdos993Lean.Analytic.V213.P03RowData.CCover04
public import Erdos993Lean.Analytic.V213.P03RowData.CCover05

/-! All 43 C rows are used
through their five actual closed covers. Actual ell interpolation is supplied
by the preceding module. The endpoint y=beta belongs to the childless branch;
the other branch uses the exact inverse log-mass and the proved least-child
reduction. No CA, AC, ell, J, or numeric-margin premise is assumed globally.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

open Real Set Certificates
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.P03RowData

/-- A single C cover, with every cap-to-row identification explicit. -/
theorem CA_from_cap_cover {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (rows : List CRow) (d u hi : Rat)
    (hd : (d : ℝ) = c.value) (hu : (u : ℝ) = c.upper)
    (hhi : (hi : ℝ) = PrintedCapData.ybar c)
    (hj : (jCap d : ℝ) = c.jBound)
    (hrows : ∀ r ∈ rows, CRowCertificate r)
    (hcap : ∀ r ∈ rows, r.D=d ∧ r.left.b.lam=u)
    (hcover : coverOK 0 hi (rows.map (fun r => (r.left.e.y,r.right.e.y)))=true)
    (ht : 0 ≤ t) (hface : y=logMass lam t) : 0 < CA c.value lam t y := by
  have hlam := Cap.activity_pos hc
  have hy : 0 < y := by rw [hface]; exact logMass_pos hlam t
  have hybeta : y ≤ logActivity lam := by
    rw [hface]
    simpa only [logMass_zero] using (logMass_strictAnti hlam).antitone ht
  have hbetau : logActivity lam ≤ logActivity c.upper := by
    unfold logActivity
    exact Real.log_le_log (by linarith) (by linarith [hc.2])
  have hyhi : y ≤ (hi : ℝ) := by
    rw [hhi]
    exact (hybeta.trans hbetau).trans (beta_upper_lt_ybar c).le
  have hJ : J lam t < (jCap d : ℝ) := by
    rw [hj]
    exact (scalarBounds hc ht hy).1
  have hEll : ∀ r ∈ rows, (r.left.e.y : ℝ) ≤ y → y ≤ (r.right.e.y : ℝ) →
      faceEllR r ≤ ell (d : ℝ) lam y := by
    intro r hr hyl hyr
    rcases hcap r hr with ⟨hrd,hru⟩
    have hh := faceEll_lower_on_cap (hrows r hr).toCRowFacts hc
      (by simpa only [hrd] using hd) (by simpa only [hru] using hu) ⟨hyl,hyr⟩
    simpa only [hd] using hh
  have hh := CA_face_positive_on_row_cover rows d u 0 hi hrows hcap hcover
    hlam (by simpa only [hu] using hc.2)
    (by simpa using (show y ∈ Icc (0 : ℝ) (hi : ℝ) from ⟨hy.le,hyhi⟩))
    ht hface hJ hEll
  simpa only [hd] using hh

theorem CA_face_positive_on_cap {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hface : y=logMass lam t) :
    0 < CA c.value lam t y := by
  cases c with
  | first =>
    exact CA_from_cap_cover hc CCover01.rows (6/5) (263/200) (21/25)
      (by norm_num [Cap.value]) (by norm_num [Cap.upper])
      (by norm_num [PrintedCapData.ybar]) (by norm_num [jCap,Cap.jBound])
      CCover01.all_certificates CCover01.cap_parameters CCover01.parent_cover ht hface
  | second =>
    exact CA_from_cap_cover hc CCover02.rows (7/5) (3/2) (23/25)
      (by norm_num [Cap.value]) (by norm_num [Cap.upper])
      (by norm_num [PrintedCapData.ybar]) (by norm_num [jCap,Cap.jBound])
      CCover02.all_certificates CCover02.cap_parameters CCover02.parent_cover ht hface
  | third =>
    exact CA_from_cap_cover hc CCover03.rows (8/5) (7/4) (51/50)
      (by norm_num [Cap.value]) (by norm_num [Cap.upper])
      (by norm_num [PrintedCapData.ybar]) (by norm_num [jCap,Cap.jBound])
      CCover03.all_certificates CCover03.cap_parameters CCover03.parent_cover ht hface
  | fourth =>
    exact CA_from_cap_cover hc CCover04.rows (9/5) 2 (11/10)
      (by norm_num [Cap.value]) (by norm_num [Cap.upper])
      (by norm_num [PrintedCapData.ybar]) (by norm_num [jCap,Cap.jBound])
      CCover04.all_certificates CCover04.cap_parameters CCover04.parent_cover ht hface
  | fifth =>
    exact CA_from_cap_cover hc CCover05.rows (21/10) (7/3) (121/100)
      (by norm_num [Cap.value]) (by norm_num [Cap.upper])
      (by norm_num [PrintedCapData.ybar]) (by norm_num [jCap,Cap.jBound])
      CCover05.all_certificates CCover05.cap_parameters CCover05.parent_cover ht hface

theorem CA_boundary_lower_on_cap {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hy : 0 < y)
    (hfeasible : logMass lam t ≤ y) (hell : ell c.value lam y ≤ 0) :
    CA c.value lam (if logActivity lam ≤ y then 0 else leastChild lam y) y ≤
      CA c.value lam t y := by
  have he := (scalarBounds hc ht hy).2.1
  have hden : ∀ s : ℝ, 0 ≤ s → 3/4 ≤ 1+ell c.value lam y*J lam s := by
    intro s hs
    exact (denominator_factor_gt hc hs hy).le
  have hD := c.value_pos
  have hlam := Cap.activity_pos hc
  cases c with
  | first =>
    apply CA_boundary_lower_first_two hD hlam (by
      have hu : lam ≤ (263/200 : ℝ) := hc.2
      linarith) ht hy hfeasible hell
      (by simpa only [Cap.eta] using he.le) hden
  | second =>
    exact CA_boundary_lower_first_two hD hlam hc.2 ht hy hfeasible hell
      (by simpa only [Cap.eta] using he.le) hden
  | third =>
    exact CA_boundary_lower_last_three hD hc.1 (by
      have hu : lam ≤ (7/4 : ℝ) := hc.2
      linarith) ht hy hfeasible hell (by simpa only [Cap.eta] using he.le) hden
  | fourth =>
    exact CA_boundary_lower_last_three hD (by
      have hl : (7/4 : ℝ) ≤ lam := hc.1
      linarith) (by
      have hu : lam ≤ (2 : ℝ) := hc.2
      linarith) ht hy hfeasible hell (by simpa only [Cap.eta] using he.le) hden
  | fifth =>
    exact CA_boundary_lower_last_three hD (by
      have hl : (2 : ℝ) ≤ lam := hc.1
      linarith) hc.2 ht hy hfeasible hell
      (by simpa only [Cap.eta] using he.le) hden

/-- Actual CA>0 on each full closed cap and every feasible child/parent pair. -/
theorem CA_positive_on_cap {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hfeasible : logMass lam t ≤ y) :
    0 < CA c.value lam t y := by
  have hlam := Cap.activity_pos hc
  have hy : 0 < y := (logMass_pos hlam t).trans_le hfeasible
  by_cases hell : 0 < ell c.value lam y
  · exact CA_pos_of_ell_pos c.value_pos hlam ht hfeasible hell
  · have hboundary := CA_boundary_lower_on_cap hc ht hy hfeasible (le_of_not_gt hell)
    by_cases hb : logActivity lam ≤ y
    · simp only [if_pos hb] at hboundary
      exact (CA_childless_positive hc hb).trans_le hboundary
    · simp only [if_neg hb] at hboundary
      have hs := leastChild_nonneg hlam hy (le_of_lt (lt_of_not_ge hb))
      have hface := (logMass_leastChild hlam hy).symm
      exact (CA_face_positive_on_cap hc hs hface).trans_le hboundary

/-- The five literal local comparisons needed by the current graph assembly.
Strict CA/AC conclusions are retained here; the assembly may weaken them. -/
theorem comparisons_on_cap {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hfeasible : logMass lam t ≤ y) :
    J lam t < c.jBound ∧ -c.eta < ell c.value lam y ∧
      0 ≤ CC c.value lam t y ∧ 0 < CA c.value lam t y ∧ 0 < AC c.value lam t y := by
  have hy := (logMass_pos (Cap.activity_pos hc) t).trans_le hfeasible
  have hs := scalarBounds hc ht hy
  exact ⟨hs.1,hs.2.1,CC_nonneg c.value_pos (Cap.activity_pos hc) ht hfeasible,
    CA_positive_on_cap hc ht hfeasible,AC_positive_on_cap hc ht hfeasible⟩

end Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_from_cap_cover
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_from_cap_cover
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_face_positive_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_face_positive_on_cap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_boundary_lower_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_boundary_lower_on_cap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_positive_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_positive_on_cap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.comparisons_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.comparisons_on_cap
