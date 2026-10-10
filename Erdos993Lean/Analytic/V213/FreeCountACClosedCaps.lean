module

public import Erdos993Lean.Analytic.V213.FreeCountChildlessFinite
public import Erdos993Lean.Analytic.V213.P03RowData.ACover01
public import Erdos993Lean.Analytic.V213.P03RowData.ACover02
public import Erdos993Lean.Analytic.V213.P03RowData.ACover03
public import Erdos993Lean.Analytic.V213.P03RowData.ACover04
public import Erdos993Lean.Analytic.V213.P03RowData.ACover05
public import Erdos993Lean.Analytic.V213.P03RowData.ACover06
public import Erdos993Lean.Analytic.V213.P03RowData.ACover07
public import Erdos993Lean.Analytic.V213.P03RowData.ACover08

/-! This consumes the actual eight reviewed A covers,
all 159 row certificates, and the analytic tail. The first four covers split
only the first cap. Every cap and every cover is closed; y=3 is included in
both arguments. Feasibility itself supplies y>0. No global AC premise occurs.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

open Real Set Certificates
open Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.P03RowData

theorem denominator_factor_gt {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hy : 0 < y) :
    (3/4 : ℝ) < 1+ell c.value lam y*J lam t := by
  have hz := (scalarBounds hc ht hy).2.2.1
  have hp := mul_pos (message_pos (Cap.activity_pos hc) y)
    (gamma_pos c.value_pos (Cap.activity_pos hc))
  rw [Z_normalized c.value_pos (Cap.activity_pos hc)] at hz
  apply (mul_lt_mul_iff_of_pos_left hp).1
  convert hz using 1 <;> ring

theorem ell_gt_neg_three_quarters {c : Cap} {lam y : ℝ}
    (hc : c.Contains lam) (hy : 0 < y) : -(3/4 : ℝ) < ell c.value lam y := by
  have he := (scalarBounds hc (t := 0) (by norm_num) hy).2.1
  have heta : c.eta ≤ (3/4 : ℝ) := by cases c <;> norm_num [Cap.eta]
  linarith

/-- One actual A cover, with the cap-to-row value identification explicit. -/
theorem AC_from_cap_cover {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (rows : List ARow) (d a b : Rat)
    (hd : (d : ℝ) = c.value)
    (hrows : ∀ r ∈ rows, ARowCertificate r)
    (hband : ∀ r ∈ rows, r.D=d ∧ r.ac.b.lam=a ∧ r.bd.b.lam=b)
    (hcover : coverOK 0 3 (rows.map (fun r => (r.ac.e.y,r.bd.e.y)))=true)
    (hlam : lam ∈ Icc (a : ℝ) (b : ℝ))
    (ht : 0 ≤ t) (hy : 0 < y) (hy3 : y ≤ 3)
    (hfeasible : logMass lam t ≤ y) : 0 < AC c.value lam t y := by
  have hD : (6/5 : ℝ) ≤ d := by
    rw [hd]
    cases c <;> norm_num [Cap.value]
  have hell := ell_gt_neg_three_quarters hc hy
  have hden : 0 < 1+ell c.value lam y*J lam t :=
    (by norm_num : (0 : ℝ) < 3/4).trans (denominator_factor_gt hc ht hy)
  have hh := AC_positive_on_row_cover rows d a b 0 3 hrows hband hcover hD
    hlam (by simpa using (show y ∈ Icc (0 : ℝ) 3 from ⟨hy.le,hy3⟩)) ht hy hfeasible
    (by simpa only [hd] using hell) (by simpa only [hd] using hden)
  simpa only [hd] using hh

theorem AC_bounded_positive {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hy : 0 < y) (hy3 : y ≤ 3)
    (hfeasible : logMass lam t ≤ y) : 0 < AC c.value lam t y := by
  cases c with
  | first =>
    have hl : (1/3 : ℝ) ≤ lam := hc.1
    have hu : lam ≤ (263/200 : ℝ) := hc.2
    by_cases h1 : lam ≤ 3/5
    · exact AC_from_cap_cover hc ACover01.rows (6/5) (1/3) (3/5)
        (by norm_num [Cap.value]) ACover01.all_certificates ACover01.band_parameters
        ACover01.parent_cover (by norm_num; exact ⟨hl,h1⟩) ht hy hy3 hfeasible
    · by_cases h2 : lam ≤ 7/8
      · exact AC_from_cap_cover hc ACover02.rows (6/5) (3/5) (7/8)
          (by norm_num [Cap.value]) ACover02.all_certificates ACover02.band_parameters
          ACover02.parent_cover (by norm_num; constructor <;> linarith)
          ht hy hy3 hfeasible
      · by_cases h3 : lam ≤ 28/25
        · exact AC_from_cap_cover hc ACover03.rows (6/5) (7/8) (28/25)
            (by norm_num [Cap.value]) ACover03.all_certificates ACover03.band_parameters
            ACover03.parent_cover (by norm_num; constructor <;> linarith)
            ht hy hy3 hfeasible
        · exact AC_from_cap_cover hc ACover04.rows (6/5) (28/25) (263/200)
            (by norm_num [Cap.value]) ACover04.all_certificates ACover04.band_parameters
            ACover04.parent_cover (by norm_num; constructor <;> linarith)
            ht hy hy3 hfeasible
  | second =>
    exact AC_from_cap_cover hc ACover05.rows (7/5) (263/200) (3/2)
      (by norm_num [Cap.value]) ACover05.all_certificates ACover05.band_parameters
      ACover05.parent_cover (by norm_num; exact hc) ht hy hy3 hfeasible
  | third =>
    exact AC_from_cap_cover hc ACover06.rows (8/5) (3/2) (7/4)
      (by norm_num [Cap.value]) ACover06.all_certificates ACover06.band_parameters
      ACover06.parent_cover (by norm_num; exact hc) ht hy hy3 hfeasible
  | fourth =>
    exact AC_from_cap_cover hc ACover07.rows (9/5) (7/4) 2
      (by norm_num [Cap.value]) ACover07.all_certificates ACover07.band_parameters
      ACover07.parent_cover (by norm_num; exact hc) ht hy hy3 hfeasible
  | fifth =>
    exact AC_from_cap_cover hc ACover08.rows (21/10) 2 (7/3)
      (by norm_num [Cap.value]) ACover08.all_certificates ACover08.band_parameters
      ACover08.parent_cover (by norm_num; exact hc) ht hy hy3 hfeasible

/-- Actual AC>0 on each full closed cap and every feasible child/parent pair. -/
theorem AC_positive_on_cap {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hfeasible : logMass lam t ≤ y) :
    0 < AC c.value lam t y := by
  have hy : 0 < y := (logMass_pos (Cap.activity_pos hc) t).trans_le hfeasible
  by_cases hy3 : y ≤ 3
  · exact AC_bounded_positive hc ht hy hy3 hfeasible
  · exact AC_tail_positive hc ht (le_of_lt (lt_of_not_ge hy3))

end Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.denominator_factor_gt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.denominator_factor_gt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_gt_neg_three_quarters
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_gt_neg_three_quarters
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.AC_from_cap_cover
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.AC_from_cap_cover
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.AC_bounded_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.AC_bounded_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.AC_positive_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.AC_positive_on_cap
