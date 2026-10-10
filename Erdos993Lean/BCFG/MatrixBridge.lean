module

public import Erdos993Lean.BCFG.DeterminantAlgebra

/-! Scalar matrix and continuity steps from T6b Eq.(3) and Section 9.
Every determinant, diagonal, envelope and reduction premise remains explicit
in these intermediate lemmas. No concrete transfer theorem is asserted. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Set

theorem continuous_positive_of_nonzero {a b : ℝ} {C : ℝ → ℝ}
    (hcont : ContinuousOn C (Icc a b)) (hbase : 0 < C a)
    (hnonzero : ∀ x ∈ Icc a b, C x ≠ 0) :
    ∀ x ∈ Icc a b, 0 < C x := by
  intro x hx
  by_contra hn
  have hCx : C x ≤ 0 := le_of_not_gt hn
  have hc : ContinuousOn C (Icc a x) := hcont.mono (by
    intro y hy
    exact ⟨hy.1, hy.2.trans hx.2⟩)
  obtain ⟨y,hy,hzero⟩ := intermediate_value_Icc' hx.1 hc
    (show (0 : ℝ) ∈ Icc (C x) (C a) from ⟨hCx,hbase.le⟩)
  exact hnonzero y ⟨hy.1,hy.2.trans hx.2⟩ hzero

theorem diagonal_ne_zero_of_scaled_det {A B C U : ℝ}
    (hU : 0 ≤ U) (hD : 0 < A*C-U*B^2) : C ≠ 0 := by
  intro hC
  rw [hC, mul_zero, zero_sub] at hD
  have hs : 0 ≤ U*B^2 := mul_nonneg hU (sq_nonneg B)
  linarith

/-- Eq.(3) prevents a continuous diagonal from crossing zero. -/
theorem continuous_diagonal_positive {a b : ℝ} {A B C U : ℝ → ℝ}
    (hcont : ContinuousOn C (Icc a b)) (hbase : 0 < C a)
    (hU : ∀ x ∈ Icc a b, 0 ≤ U x)
    (hD : ∀ x ∈ Icc a b, 0 < A x*C x-U x*(B x)^2) :
    ∀ x ∈ Icc a b, 0 < C x := by
  apply continuous_positive_of_nonzero hcont hbase
  intro x hx
  exact diagonal_ne_zero_of_scaled_det (hU x hx) (hD x hx)

theorem scaled_quadratic_identity (A B C U y : ℝ) (hC : C ≠ 0) (hU : U ≠ 0) :
    A+2*B*y+C/U*y^2 = (A*C-U*B^2)/C+C/U*(y+U*B/C)^2 := by
  field_simp [hC,hU]
  ring

theorem scaled_quadratic_pos {A B C U : ℝ} (hC : 0 < C) (hU : 0 < U)
    (hD : 0 < A*C-U*B^2) (y : ℝ) : 0 < A+2*B*y+C/U*y^2 := by
  rw [scaled_quadratic_identity A B C U y hC.ne' hU.ne']
  exact add_pos_of_pos_of_nonneg (div_pos hD hC)
    (mul_nonneg (div_pos hC hU).le (sq_nonneg _))

/-- The exact matrix implication is valid for every real response z. -/
theorem all_response_minorant {Kminus K P R Y U t0 eps : ℝ}
    (hK : Kminus ≤ K) (hY : 0 < Y) (hYU : Y ≤ U) (hR : 0 ≤ R)
    (hC : 0 < R-P*U)
    (hD : 0 < (Kminus-P-eps)*(R-P*U)-U*(P-t0)^2) (z : ℝ) :
    eps < K-P+2*(P-t0)*(1-z)+(R/Y-P)*(1-z)^2 := by
  have hU : 0 < U := hY.trans_le hYU
  have hq := scaled_quadratic_pos hC hU hD (1-z)
  have hCU : (R-P*U)/U = R/U-P := by
    field_simp [hU.ne']
  rw [hCU] at hq
  have hratio : R/U ≤ R/Y := (div_le_div_iff₀ hU hY).2
    (mul_le_mul_of_nonneg_left hYU hR)
  have hs := mul_le_mul_of_nonneg_right hratio (sq_nonneg (1-z))
  nlinarith

/-- The regular U=0 determinant supplies the leaf margin without division. -/
theorem leaf_margin_of_scaled_det {Kminus K P R eps : ℝ}
    (hK : Kminus ≤ K) (hR : 0 < R)
    (hD : 0 < (Kminus-P-eps)*R) : eps < K-P := by
  have hA : 0 < Kminus-P-eps := (mul_pos_iff_of_pos_right hR).mp hD
  linarith

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.continuous_positive_of_nonzero
#print axioms Erdos993Lean.BCFG.Analytic.continuous_positive_of_nonzero
#check Erdos993Lean.BCFG.Analytic.diagonal_ne_zero_of_scaled_det
#print axioms Erdos993Lean.BCFG.Analytic.diagonal_ne_zero_of_scaled_det
#check Erdos993Lean.BCFG.Analytic.continuous_diagonal_positive
#print axioms Erdos993Lean.BCFG.Analytic.continuous_diagonal_positive
#check Erdos993Lean.BCFG.Analytic.scaled_quadratic_identity
#print axioms Erdos993Lean.BCFG.Analytic.scaled_quadratic_identity
#check Erdos993Lean.BCFG.Analytic.scaled_quadratic_pos
#print axioms Erdos993Lean.BCFG.Analytic.scaled_quadratic_pos
#check Erdos993Lean.BCFG.Analytic.all_response_minorant
#print axioms Erdos993Lean.BCFG.Analytic.all_response_minorant
#check Erdos993Lean.BCFG.Analytic.leaf_margin_of_scaled_det
#print axioms Erdos993Lean.BCFG.Analytic.leaf_margin_of_scaled_det
