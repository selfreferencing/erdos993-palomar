module

public import Erdos993Lean.Analytic.V213.ResponseParentRowAffineDefs

/-! The seven literal H-row PG affine comparisons, their seven PG' strict
slacks, and the field bounds used in the common parent estimates. All results
come from the original integer pairs on the closed interval [7/4,7/3]. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem H_fields_positive {lam : ℝ} (h : inRow 3 lam) :
    0 < alpha 3 lam ∧ 0 < beta 3 lam ∧ 0 < gamma 3 lam ∧ 0 < delta 3 lam := by
  norm_num [inRow,rowData,alpha,beta,gamma,delta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  exact ⟨by linarith [h.1,h.2],by linarith [h.1,h.2],
    by linarith [h.1,h.2],by linarith [h.1,h.2]⟩

theorem H_Gamma_affine_lower {lam : ℝ} (h : inRow 3 lam) :
    lam/4-1/5 ≤ capitalGamma 3 lam := by
  norm_num [inRow,rowData,capitalGamma,gamma,delta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_gamma_lower {lam : ℝ} (h : inRow 3 lam) : 2/5 ≤ gamma 3 lam := by
  norm_num [inRow,rowData,gamma,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_gamma_affine_upper {lam : ℝ} (h : inRow 3 lam) :
    gamma 3 lam ≤ lam/15+8/25 := by
  norm_num [inRow,rowData,gamma,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_delta_affine_lower {lam : ℝ} (h : inRow 3 lam) :
    1/2-9*lam/50 ≤ delta 3 lam := by
  norm_num [inRow,rowData,delta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_alpha_beta_lower {lam : ℝ} (h : inRow 3 lam) :
    3*lam/4-11/25 ≤ alpha 3 lam+beta 3 lam := by
  norm_num [inRow,rowData,alpha,beta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_alpha_beta_upper {lam : ℝ} (h : inRow 3 lam) :
    alpha 3 lam+beta 3 lam ≤ 3*lam/4-2/5 := by
  norm_num [inRow,rowData,alpha,beta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_beta_lower {lam : ℝ} (h : inRow 3 lam) : 1/8 ≤ beta 3 lam := by
  norm_num [inRow,rowData,beta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_Gamma_lower {lam : ℝ} (h : inRow 3 lam) : 19/80 ≤ capitalGamma 3 lam := by
  have ha := H_Gamma_affine_lower h
  norm_num [inRow,rowData,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h
  linarith [h.1]

theorem H_gamma_ceiling_strict {lam : ℝ} (h : inRow 3 lam) : lam/15+8/25 < 12/25 := by
  norm_num [inRow,rowData,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h
  linarith [h.2]

theorem H_gamma_upper {lam : ℝ} (h : inRow 3 lam) : gamma 3 lam ≤ 12/25 :=
  (H_gamma_affine_upper h).trans (H_gamma_ceiling_strict h).le

theorem H_delta_floor_pos {lam : ℝ} (h : inRow 3 lam) : 0 < 1/2-9*lam/50 := by
  norm_num [inRow,rowData,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h
  linarith [h.2]

theorem H_delta_pos {lam : ℝ} (h : inRow 3 lam) : 0 < delta 3 lam :=
  (H_delta_floor_pos h).trans_le (H_delta_affine_lower h)

theorem H_E_pos {lam : ℝ} (h : inRow 3 lam) : 0 < parentE 3 lam := by
  norm_num [inRow,rowData,parentE,alpha,beta,gamma,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_E_upper {lam : ℝ} (h : inRow 3 lam) : parentE 3 lam ≤ 77/25-37*lam/60 := by
  have hg := H_gamma_affine_upper h
  have ha := H_alpha_beta_lower h
  unfold parentE
  linarith

theorem H_Gamma_slack {lam : ℝ} (h : inRow 3 lam) :
    1/4000 < capitalGamma 3 lam-(lam/4-1/5) := by
  norm_num [inRow,rowData,capitalGamma,gamma,delta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_gamma_lower_slack {lam : ℝ} (h : inRow 3 lam) :
    1/50 < gamma 3 lam-2/5 := by
  norm_num [inRow,rowData,gamma,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_gamma_upper_slack {lam : ℝ} (h : inRow 3 lam) :
    1/2000 < (lam/15+8/25)-gamma 3 lam := by
  norm_num [inRow,rowData,gamma,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_delta_slack {lam : ℝ} (h : inRow 3 lam) :
    1/300 < delta 3 lam-(1/2-9*lam/50) := by
  norm_num [inRow,rowData,delta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_alpha_beta_lower_slack {lam : ℝ} (h : inRow 3 lam) :
    1/1000 < (alpha 3 lam+beta 3 lam)-(3*lam/4-11/25) := by
  norm_num [inRow,rowData,alpha,beta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_alpha_beta_upper_slack {lam : ℝ} (h : inRow 3 lam) :
    1/1000 < (3*lam/4-2/5)-(alpha 3 lam+beta 3 lam) := by
  norm_num [inRow,rowData,alpha,beta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

theorem H_beta_slack {lam : ℝ} (h : inRow 3 lam) : 1/400 < beta 3 lam-1/8 := by
  norm_num [inRow,rowData,beta,affineField,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h ⊢
  linarith [h.1,h.2]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_fields_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_fields_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_Gamma_affine_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_Gamma_affine_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_affine_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_affine_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_delta_affine_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_delta_affine_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_alpha_beta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_alpha_beta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_alpha_beta_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_alpha_beta_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_beta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_beta_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_Gamma_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_Gamma_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_ceiling_strict
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_ceiling_strict
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_delta_floor_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_delta_floor_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_delta_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_delta_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_E_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_E_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_E_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_E_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_Gamma_slack
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_Gamma_slack
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_lower_slack
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_lower_slack
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_upper_slack
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_gamma_upper_slack
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_delta_slack
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_delta_slack
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_alpha_beta_lower_slack
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_alpha_beta_lower_slack
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_alpha_beta_upper_slack
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_alpha_beta_upper_slack
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_beta_slack
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_beta_slack
