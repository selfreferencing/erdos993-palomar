module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightGeometry
public import Erdos993Lean.Analytic.V213.ResponseParentRowAffineBounds
public import Erdos993Lean.Analytic.V213.ResponseParentGuardPolynomials

/-! Parent b,c bounds from the actual four reviewed affine rows. Rational
parabola comparisons are proof terms here, not an external certificate. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem parentC_parabola {i : Fin 4} {lam H rho : ℝ}
    (hl : 0 < lam) (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rho ≤ 1) (hg : 0 ≤ gamma i lam) :
    parentC i lam H rho ≤ halfParent lam H*
      (parentE i lam-(2+gamma i lam)*halfParent lam H) := by
  have hp := halfParent_bounds hl hH hcap
  have hh := (messageRatio_weak_bounds hp.2.1.le hp.2.2.1).2
  have hr := mul_le_mul_of_nonneg_right hrho (show 0 ≤ 1-halfParent lam H by linarith [hp.2.2.1])
  have hgm := mul_le_mul_of_nonneg_left hh hg
  have hP : 2*parentP i lam H rho-alpha i lam-beta i lam ≤
      parentE i lam-(2+gamma i lam)*halfParent lam H := by
    unfold parentP parentE
    nlinarith
  exact mul_le_mul_of_nonneg_left hP hp.2.1.le

theorem parabola_decreases {p0 p A E : ℝ} (hp : p0 ≤ p) (hA : 0 ≤ A)
    (hv : E ≤ 2*A*p0) : p*(E-A*p) ≤ p0*(E-A*p0) := by
  have h1 := mul_nonneg hA (sub_nonneg.mpr hp)
  have h2 : 0 ≤ A*(p+p0)-E := by nlinarith
  have h3 := mul_nonneg (sub_nonneg.mpr hp) h2
  nlinarith

theorem parentB_pos {i : Fin 4} {lam H rho : ℝ}
    (hrow : inRow i lam) (hl : 0 < lam) (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) : 0 < parentB i lam H rho := by
  have hfields := all_rows_fields_positive hrow
  have hp := (halfParent_bounds hl hH hcap).2.1
  have hr := half_rho_pos hl hH hcap hrho
  exact mul_pos (mul_pos hfields.2.1 hr) hp

theorem D_parentB_lower {lam H rho : ℝ} (hrow : inRow 0 lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) : 364/2725 ≤ parentB 0 lam H rho := by
  have hr : 4/5 ≤ lam ∧ lam ≤ 13/10 := by simpa [inRow,rowData] using hrow
  have hl : 0 < lam := by linarith
  have hp := piStar_le_occupied hl hH hcap hrho
  have hm := piStar_monotone (by norm_num : (0:ℝ)<4/5) hr.1
  norm_num [piStar] at hm
  have hbp := mul_le_mul_of_nonneg_left (hm.trans hp) (show (0:ℝ)≤13/25 by norm_num)
  have hbet := mul_le_mul_of_nonneg_right (D_beta_lower hrow)
    (show 0 ≤ rho*halfParent lam H by linarith)
  unfold parentB
  nlinarith

theorem E1_parentB_lower {lam H rho : ℝ} (hrow : inRow 1 lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) : 1/10 ≤ parentB 1 lam H rho := by
  have hr : 13/10 ≤ lam ∧ lam ≤ 29/20 := by simpa [inRow,rowData] using hrow
  have hl : 0 < lam := by linarith
  have hp := piStar_le_occupied hl hH hcap hrho
  have hm := piStar_monotone (by norm_num : (0:ℝ)<13/10) hr.1
  norm_num [piStar] at hm
  have hbp := mul_le_mul_of_nonneg_left (hm.trans hp) (show (0:ℝ)≤11/30 by norm_num)
  have hbet := mul_le_mul_of_nonneg_right (E1_beta_lower hrow)
    (show 0 ≤ rho*halfParent lam H by linarith)
  unfold parentB
  nlinarith

theorem E2_parentB_lower {lam H rho : ℝ} (hrow : inRow 2 lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) : 1/8 ≤ parentB 2 lam H rho := by
  have hr : 29/20 ≤ lam ∧ lam ≤ 8/5 := by simpa [inRow,rowData] using hrow
  have hl : 0 < lam := by linarith
  have hp := piStar_le_occupied hl hH hcap hrho
  have hm := piStar_monotone (by norm_num : (0:ℝ)<29/20) hr.1
  norm_num [piStar] at hm
  have hbp := mul_le_mul_of_nonneg_left (hm.trans hp) (show (0:ℝ)≤9/20 by norm_num)
  have hbet := mul_le_mul_of_nonneg_right (E2_beta_lower hrow)
    (show 0 ≤ rho*halfParent lam H by linarith)
  unfold parentB
  nlinarith

theorem E1_parentC_upper {lam H rho : ℝ} (hrow : inRow 1 lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    parentC 1 lam H rho ≤ 1/5 := by
  have hr : 13/10 ≤ lam ∧ lam ≤ 29/20 := by simpa [inRow,rowData] using hrow
  have hl : 0 < lam := by linarith
  have hp := halfParent_bounds hl hH hcap
  have hg := E1_gamma_strict_lower hrow
  have he := E1_E_upper hrow
  have h0 := pStar_monotone (by norm_num : (0:ℝ)<13/10) hr.1
  norm_num [pStar] at h0
  have hmin : 429/889 ≤ halfParent lam H := h0.trans (pStar_le_halfParent hl hH hcap)
  have hc := parentC_parabola hl hH hcap hrho (by linarith)
  have hgu := mul_nonneg (show 0 ≤ gamma 1 lam-6/25 by linarith) hp.2.1.le
  have hpu := mul_le_mul_of_nonneg_left
    (show parentE 1 lam-(2+gamma 1 lam)*halfParent lam H ≤
      149/100-(2+6/25)*halfParent lam H by nlinarith) hp.2.1.le
  have hdec := parabola_decreases hmin (by norm_num : (0:ℝ)≤2+6/25)
    (by norm_num : (149/100:ℝ)≤2*(2+6/25)*(429/889))
  norm_num at hdec
  linarith

theorem E2_parentC_upper {lam H rho : ℝ} (hrow : inRow 2 lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    parentC 2 lam H rho ≤ 4/25 := by
  have hr : 29/20 ≤ lam ∧ lam ≤ 8/5 := by simpa [inRow,rowData] using hrow
  have hl : 0 < lam := by linarith
  have hp := halfParent_bounds hl hH hcap
  have hg := E2_gamma_strict_lower hrow
  have he := E2_E_upper hrow
  have h0 := pStar_monotone (by norm_num : (0:ℝ)<29/20) hr.1
  norm_num [pStar] at h0
  have hmin : 2001/3961 ≤ halfParent lam H := h0.trans (pStar_le_halfParent hl hH hcap)
  have hc := parentC_parabola hl hH hcap hrho (by linarith)
  have hgu := mul_nonneg (show 0 ≤ gamma 2 lam-7/25 by linarith) hp.2.1.le
  have hpu := mul_le_mul_of_nonneg_left
    (show parentE 2 lam-(2+gamma 2 lam)*halfParent lam H ≤
      29/20-(2+7/25)*halfParent lam H by nlinarith) hp.2.1.le
  have hdec := parabola_decreases hmin (by norm_num : (0:ℝ)≤2+7/25)
    (by norm_num : (29/20:ℝ)≤2*(2+7/25)*(2001/3961))
  norm_num at hdec
  linarith

theorem D_parentC_upper {lam H rho : ℝ} (hrow : inRow 0 lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    parentC 0 lam H rho ≤ 1/8 := by
  have hr : 4/5 ≤ lam ∧ lam ≤ 13/10 := by simpa [inRow,rowData] using hrow
  have hl : 0 < lam := by linarith
  have hp := halfParent_bounds hl hH hcap
  have hg := D_gamma_affine_lower hrow
  have hgu := D_gamma_affine_upper hrow
  have hab := D_alpha_beta_lower hrow
  have he : parentE 0 lam ≤ 108/125+8*lam/25 := by unfold parentE; linarith
  have h0 := pStar_monotone (by norm_num : (0:ℝ)<4/5) hr.1
  norm_num [pStar] at h0
  change 28/73 ≤ pStar lam at h0
  have hmin := pStar_le_halfParent hl hH hcap
  have hc := parentC_parabola hl hH hcap hrho (by linarith)
  have hgp := mul_nonneg (sub_nonneg.mpr hg) hp.2.1.le
  have hpu := mul_le_mul_of_nonneg_left
    (show parentE 0 lam-(2+gamma 0 lam)*halfParent lam H ≤
      108/125+8*lam/25-(2+lam/5)*halfParent lam H by nlinarith) hp.2.1.le
  have hv : 108/125+8*lam/25 ≤ 2*(2+lam/5)*pStar lam := by
    have hx := mul_nonneg (show 0 ≤ lam/5 by linarith) (pStar_pos hl).le
    nlinarith
  have hdec := parabola_decreases hmin (show 0 ≤ 2+lam/5 by linarith) hv
  have hend := parentDUpperC_lt_eighth hr.1 hr.2
  unfold parentDUpperC at hend
  linarith

theorem H_parentC_upper {lam H rho : ℝ} (hrow : inRow 3 lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    parentC 3 lam H rho < 4*delta 3 lam := by
  have hr : 7/4 ≤ lam ∧ lam ≤ 7/3 := by simpa [inRow,rowData] using hrow
  have hl : 0 < lam := by linarith
  have hg := H_gamma_lower hrow
  have he0 := H_E_pos hrow
  have he := H_E_upper hrow
  have hd := H_delta_affine_lower hrow
  have hdu := H_delta_floor_pos hrow
  have hc := parentC_parabola hl hH hcap hrho (by linarith)
  have hquad := sq_nonneg (2*(2+gamma 3 lam)*halfParent lam H-parentE 3 lam)
  have hclear : 4*(2+gamma 3 lam)*parentC 3 lam H rho ≤ (parentE 3 lam)^2 := by
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*(2+gamma 3 lam) by linarith)
    nlinarith
  have hE2 : (parentE 3 lam)^2 ≤ (77/25-37*lam/60)^2 := by nlinarith
  have hpoly : 0 < 16*(1/2-9*lam/50)*(12/5)-(77/25-37*lam/60)^2 := by
    have hsq : lam^2 ≤ (7/3:ℝ)^2 := by nlinarith
    nlinarith
  have hprod : 16*(1/2-9*lam/50)*(12/5) ≤ 16*delta 3 lam*(2+gamma 3 lam) := by
    have h1 := mul_le_mul_of_nonneg_right hd (by norm_num : (0:ℝ)≤16*(12/5))
    have h2 := mul_nonneg (show 0 ≤ delta 3 lam by linarith) (show 0 ≤ gamma 3 lam-2/5 by linarith)
    nlinarith
  have ht : 4*(2+gamma 3 lam)*parentC 3 lam H rho <
      4*(2+gamma 3 lam)*(4*delta 3 lam) := by nlinarith
  nlinarith [show 0 < 4*(2+gamma 3 lam) by linarith]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentC_parabola
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentC_parabola
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parabola_decreases
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parabola_decreases
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentB_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentB_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_parentB_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_parentB_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_parentB_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_parentB_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_parentB_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_parentB_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_parentC_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_parentC_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_parentC_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_parentC_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_parentC_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_parentC_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_parentC_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_parentC_upper
