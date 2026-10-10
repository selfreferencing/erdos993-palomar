module

public import Erdos993Lean.Analytic.V213.ResponseParentYBounds
public import Erdos993Lean.Analytic.V213.ResponseParentQuadraticCap
public import Erdos993Lean.Analytic.V213.ResponseParentRowAffineBounds

/-! Current T7 positive response curvature on every original closed parent row.
The actual pP cap, actual Y bounds and proved affine fields are assembled here;
none survives as an additional premise in the final row theorem. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows
open FreeCountVariance.Envelopes

theorem parent_product_ceiling {i : Fin 4} {lam H rho M : ℝ}
    (hl : 0 < lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rho ≤ 1) (hg0 : 0 ≤ gamma i lam) (hgM : gamma i lam ≤ M) :
    halfParent lam H*parentP i lam H rho ≤ (1+M)^2/(2*(2+M)) := by
  have hp := parent_pP_upper (i := i) hl hH hcap hrho hg0
  have hM0 : 0 ≤ M := hg0.trans hgM
  have hd1 : 2+gamma i lam ≠ 0 := by positivity
  have hd2 : 2+M ≠ 0 := by positivity
  have he :
      (1+M)^2/(2*(2+M))-(1+gamma i lam)^2/(2*(2+gamma i lam)) =
        (M-gamma i lam)*(3+2*M+2*gamma i lam+M*gamma i lam)/
          (2*(2+M)*(2+gamma i lam)) := by
    field_simp [hd1,hd2]
    ring
  have hn : 0 ≤
      (1+M)^2/(2*(2+M))-(1+gamma i lam)^2/(2*(2+gamma i lam)) := by
    rw [he]
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hgM) (by positivity)) (by positivity)
  linarith

theorem parent_curvature_of_bounds {i : Fin 4} {lam H rho M L U : ℝ}
    (hl : 0 < lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rho ≤ 1) (hg0 : 0 ≤ gamma i lam) (hgM : gamma i lam ≤ M)
    (hGamma : L ≤ capitalGamma i lam) (hy : parentY H < U)
    (hcert : 1/40 < L-((1+M)^2/(2*(2+M)))*U) :
    1/40 < parentD i lam H rho := by
  have hM0 : 0 ≤ M := hg0.trans hgM
  have hq1 : childQ lam < 1 := by
    unfold childQ
    exact (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hH1 : H < 1 := by linarith
  have hy0 : 0 ≤ parentY H := (scalarLog_pos hH hH1).le
  have hp := parent_product_ceiling hl hH hcap hrho hg0 hgM
  have hB : 0 < (1+M)^2/(2*(2+M)) := by positivity
  have hm := mul_le_mul_of_nonneg_right hp hy0
  have hu := mul_lt_mul_of_pos_left hy hB
  have ht : halfParent lam H*parentP i lam H rho*parentY H <
      ((1+M)^2/(2*(2+M)))*U := hm.trans_lt hu
  unfold capitalGamma at hGamma
  unfold parentD
  linarith

theorem parentD_D_gt_fortieth {lam H rho : ℝ} (hrow : inRow 0 lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    1/40 < parentD 0 lam H rho := by
  have hb : 4/5 ≤ lam ∧ lam ≤ 13/10 := by simpa [inRow,rowData] using hrow
  exact parent_curvature_of_bounds (M := 7/25) (L := 73/500) (U := 1/3)
    (by linarith) hH hcap hrho (D_fields_positive hrow).2.2.1.le
    (D_gamma_upper hrow) (D_Gamma_lower hrow) (parentY_D_upper hrow hH hcap)
    (by norm_num)

theorem parentD_E1_gt_fortieth {lam H rho : ℝ} (hrow : inRow 1 lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    1/40 < parentD 1 lam H rho := by
  have hb : 13/10 ≤ lam ∧ lam ≤ 29/20 := by simpa [inRow,rowData] using hrow
  exact parent_curvature_of_bounds (M := 3/10) (L := 19/100) (U := 9/25)
    (by linarith) hH hcap hrho (E1_fields_positive hrow).2.2.1.le
    (E1_gamma_upper hrow) (E1_Gamma_lower hrow) (parentY_E1_upper hrow hH hcap)
    (by norm_num)

theorem parentD_E2_gt_fortieth {lam H rho : ℝ} (hrow : inRow 2 lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    1/40 < parentD 2 lam H rho := by
  have hb : 29/20 ≤ lam ∧ lam ≤ 8/5 := by simpa [inRow,rowData] using hrow
  exact parent_curvature_of_bounds (M := 13/40) (L := 6/25) (U := 3/8)
    (by linarith) hH hcap hrho (E2_fields_positive hrow).2.2.1.le
    (E2_gamma_upper hrow) (E2_Gamma_lower hrow) (parentY_E2_upper hrow hH hcap)
    (by norm_num)

theorem parentD_H_gt_fortieth {lam H rho : ℝ} (hrow : inRow 3 lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    1/40 < parentD 3 lam H rho := by
  have hb : 7/4 ≤ lam ∧ lam ≤ 7/3 := by simpa [inRow,rowData] using hrow
  exact parent_curvature_of_bounds (M := 12/25) (L := 19/80) (U := 7/16)
    (by linarith) hH hcap hrho (H_fields_positive hrow).2.2.1.le
    (H_gamma_upper hrow) (H_Gamma_lower hrow) (parentY_H_upper hrow hH hcap)
    (by norm_num)

theorem parentD_gt_fortieth {i : Fin 4} {lam H rho : ℝ} (hrow : inRow i lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) (hrho : rho ≤ 1) :
    1/40 < parentD i lam H rho := by
  fin_cases i
  · exact parentD_D_gt_fortieth hrow hH hcap hrho
  · exact parentD_E1_gt_fortieth hrow hH hcap hrho
  · exact parentD_E2_gt_fortieth hrow hH hcap hrho
  · exact parentD_H_gt_fortieth hrow hH hcap hrho

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_product_ceiling
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_product_ceiling
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_curvature_of_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_curvature_of_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_D_gt_fortieth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_D_gt_fortieth
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_E1_gt_fortieth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_E1_gt_fortieth
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_E2_gt_fortieth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_E2_gt_fortieth
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_H_gt_fortieth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_H_gt_fortieth
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_gt_fortieth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD_gt_fortieth
