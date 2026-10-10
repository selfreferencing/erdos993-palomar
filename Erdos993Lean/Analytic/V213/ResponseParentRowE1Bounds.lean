module

public import Erdos993Lean.Analytic.V213.ResponseParentRowAffineDefs

/-! All E1 affine comparisons requested in current T7 Section5.4.
No parent-message estimate is inferred solely from these field comparisons. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem E1_fields_positive {lam : ℝ} (h : inRow 1 lam) :
    0 < alpha 1 lam ∧ 0 < beta 1 lam ∧ 0 < gamma 1 lam ∧ 0 < delta 1 lam := by
  norm_num [inRow,rowData,alpha,beta,gamma,delta,affineField] at h ⊢
  exact ⟨by linarith [h.1,h.2],by linarith [h.1,h.2],
    by linarith [h.1,h.2],by linarith [h.1,h.2]⟩

theorem E1_Gamma_lower {lam : ℝ} (h : inRow 1 lam) : 19/100 ≤ capitalGamma 1 lam := by
  norm_num [inRow,rowData,capitalGamma,gamma,delta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem E1_gamma_upper {lam : ℝ} (h : inRow 1 lam) : gamma 1 lam ≤ 3/10 := by
  norm_num [inRow,rowData,gamma,affineField] at h ⊢
  linarith [h.1,h.2]

theorem E1_beta_lower {lam : ℝ} (h : inRow 1 lam) : 11/30 ≤ beta 1 lam := by
  norm_num [inRow,rowData,beta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem E1_delta_lower {lam : ℝ} (h : inRow 1 lam) : 1/25 ≤ delta 1 lam := by
  norm_num [inRow,rowData,delta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem E1_gamma_strict_lower {lam : ℝ} (h : inRow 1 lam) : 6/25 < gamma 1 lam := by
  norm_num [inRow,rowData,gamma,affineField] at h ⊢
  linarith [h.1,h.2]

theorem E1_E_upper {lam : ℝ} (h : inRow 1 lam) : parentE 1 lam < 149/100 := by
  norm_num [inRow,rowData,parentE,alpha,beta,gamma,affineField] at h ⊢
  linarith [h.1,h.2]

theorem E1_Gamma_affine_lower {lam : ℝ} (h : inRow 1 lam) :
    (19*lam-15)/50 ≤ capitalGamma 1 lam := by
  norm_num [inRow,rowData,capitalGamma,gamma,delta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem E1_gamma_affine_lower {lam : ℝ} (h : inRow 1 lam) :
    (31*lam-16)/100 ≤ gamma 1 lam := by
  norm_num [inRow,rowData,gamma,affineField] at h ⊢
  linarith [h.1,h.2]

theorem E1_alpha_beta_upper {lam : ℝ} (h : inRow 1 lam) :
    alpha 1 lam+beta 1 lam ≤ 4*lam/3-71/100 := by
  norm_num [inRow,rowData,alpha,beta,affineField] at h ⊢
  linarith [h.1,h.2]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_fields_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_fields_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_Gamma_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_Gamma_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_gamma_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_gamma_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_beta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_beta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_delta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_delta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_gamma_strict_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_gamma_strict_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_E_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_E_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_Gamma_affine_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_Gamma_affine_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_gamma_affine_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_gamma_affine_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_alpha_beta_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_alpha_beta_upper
