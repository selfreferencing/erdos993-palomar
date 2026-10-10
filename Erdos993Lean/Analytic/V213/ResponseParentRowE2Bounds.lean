module

public import Erdos993Lean.Analytic.V213.ResponseParentRowAffineDefs

/-! All E2 affine comparisons requested in current T7 Section5.4. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem E2_fields_positive {lam : ℝ} (h : inRow 2 lam) :
    0 < alpha 2 lam ∧ 0 < beta 2 lam ∧ 0 < gamma 2 lam ∧ 0 < delta 2 lam := by
  norm_num [inRow,rowData,alpha,beta,gamma,delta,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  exact ⟨by linarith [h.1,h.2],by linarith [h.1,h.2],
    by linarith [h.1,h.2],by linarith [h.1,h.2]⟩

theorem E2_Gamma_lower {lam : ℝ} (h : inRow 2 lam) : 6/25 ≤ capitalGamma 2 lam := by
  norm_num [inRow,rowData,capitalGamma,gamma,delta,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem E2_gamma_upper {lam : ℝ} (h : inRow 2 lam) : gamma 2 lam ≤ 13/40 := by
  norm_num [inRow,rowData,gamma,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem E2_beta_lower {lam : ℝ} (h : inRow 2 lam) : 9/20 ≤ beta 2 lam := by
  norm_num [inRow,rowData,beta,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem E2_delta_lower {lam : ℝ} (h : inRow 2 lam) : 1/25 ≤ delta 2 lam := by
  norm_num [inRow,rowData,delta,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem E2_gamma_strict_lower {lam : ℝ} (h : inRow 2 lam) : 7/25 < gamma 2 lam := by
  norm_num [inRow,rowData,gamma,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem E2_E_upper {lam : ℝ} (h : inRow 2 lam) : parentE 2 lam < 29/20 := by
  norm_num [inRow,rowData,parentE,alpha,beta,gamma,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem E2_Gamma_affine_lower {lam : ℝ} (h : inRow 2 lam) :
    3*lam/20+1/40 ≤ capitalGamma 2 lam := by
  norm_num [inRow,rowData,capitalGamma,gamma,delta,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem E2_gamma_affine_lower {lam : ℝ} (h : inRow 2 lam) :
    (21*lam-2)/100 ≤ gamma 2 lam := by
  norm_num [inRow,rowData,gamma,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem E2_alpha_beta_upper {lam : ℝ} (h : inRow 2 lam) :
    alpha 2 lam+beta 2 lam ≤ lam/2+41/100 := by
  norm_num [inRow,rowData,alpha,beta,affineField,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_fields_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_fields_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_Gamma_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_Gamma_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_gamma_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_gamma_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_beta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_beta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_delta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_delta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_gamma_strict_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_gamma_strict_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_E_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_E_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_Gamma_affine_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_Gamma_affine_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_gamma_affine_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_gamma_affine_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_alpha_beta_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_alpha_beta_upper
