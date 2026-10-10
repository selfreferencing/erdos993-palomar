module

public import Erdos993Lean.Analytic.V213.ResponseParentRowAffineDefs

/-! Literal D-row affine guards, current T7 Eq11 and Section5.4.
Each proof substitutes only the reviewed Table1 integer pairs and uses the
closed row interval. These are new kernel proofs, not evaluated metadata. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem D_fields_positive {lam : ℝ} (h : inRow 0 lam) :
    0 < alpha 0 lam ∧ 0 < beta 0 lam ∧ 0 < gamma 0 lam ∧ 0 < delta 0 lam := by
  norm_num [inRow,rowData,alpha,beta,gamma,delta,affineField] at h ⊢
  exact ⟨by linarith [h.1,h.2],by linarith [h.1,h.2],
    by linarith [h.1,h.2],by linarith [h.1,h.2]⟩

theorem D_Gamma_lower {lam : ℝ} (h : inRow 0 lam) : 73/500 ≤ capitalGamma 0 lam := by
  norm_num [inRow,rowData,capitalGamma,gamma,delta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_gamma_upper {lam : ℝ} (h : inRow 0 lam) : gamma 0 lam ≤ 7/25 := by
  norm_num [inRow,rowData,gamma,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_beta_lower {lam : ℝ} (h : inRow 0 lam) : 13/25 ≤ beta 0 lam := by
  norm_num [inRow,rowData,beta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_delta_lower {lam : ℝ} (h : inRow 0 lam) : 1/50 ≤ delta 0 lam := by
  norm_num [inRow,rowData,delta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_Gamma_affine_lower {lam : ℝ} (h : inRow 0 lam) :
    19*lam/100-7/1000 ≤ capitalGamma 0 lam := by
  norm_num [inRow,rowData,capitalGamma,gamma,delta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_gamma_affine_lower {lam : ℝ} (h : inRow 0 lam) : lam/5 ≤ gamma 0 lam := by
  norm_num [inRow,rowData,gamma,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_gamma_affine_upper {lam : ℝ} (h : inRow 0 lam) :
    gamma 0 lam ≤ 21*lam/100+1/500 := by
  norm_num [inRow,rowData,gamma,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_alpha_beta_lower {lam : ℝ} (h : inRow 0 lam) :
    lam/10+57/50 ≤ alpha 0 lam+beta 0 lam := by
  norm_num [inRow,rowData,alpha,beta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_alpha_beta_upper {lam : ℝ} (h : inRow 0 lam) :
    alpha 0 lam+beta 0 lam ≤ lam/10+23/20 := by
  norm_num [inRow,rowData,alpha,beta,affineField] at h ⊢
  linarith [h.1,h.2]

theorem D_delta_adverse_upper {lam : ℝ} (h : inRow 0 lam) :
    delta 0 lam < (23+21*(lam-4/5))/1000 := by
  norm_num [inRow,rowData,delta,affineField] at h ⊢
  linarith [h.1,h.2]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_fields_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_fields_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_Gamma_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_Gamma_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_gamma_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_gamma_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_beta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_beta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_delta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_delta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_Gamma_affine_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_Gamma_affine_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_gamma_affine_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_gamma_affine_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_gamma_affine_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_gamma_affine_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_alpha_beta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_alpha_beta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_alpha_beta_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_alpha_beta_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_delta_adverse_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_delta_adverse_upper
