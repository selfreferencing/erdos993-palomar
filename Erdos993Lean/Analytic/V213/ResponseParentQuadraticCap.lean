module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightDefs

/-! The literal pP quadratic cap in current T7's positive-response-curvature
paragraph. The row-field sign is explicit; no parent d sign is assumed. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem parent_quadratic_square (p g : ℝ) (hg : 0 ≤ g) :
    (1+g)^2/(2*(2+g))-p*(1-p+g*(1-p/2)) =
      ((2+g)*p-(1+g))^2/(2*(2+g)) := by
  have hd : 2+g ≠ 0 := by positivity
  field_simp [hd] <;> ring

theorem parent_pP_upper {i : Fin 4} {lam H rho : ℝ}
    (hl : 0 < lam) (hH : 0 < H) (hHq : H ≤ childQ lam/2)
    (hrho : rho ≤ 1) (hgamma : 0 ≤ gamma i lam) :
    halfParent lam H*parentP i lam H rho ≤
      (1+gamma i lam)^2/(2*(2+gamma i lam)) := by
  have hq1 : childQ lam < 1 := by
    unfold childQ
    exact (div_lt_one (show 0 < 1+lam by linarith)).2 (by linarith)
  have hH1 : H < 1 := by linarith
  have hp := chartParent_bounds hl
    (show 0 < 1-H by linarith) (show 1-H ≤ 1 by linarith)
  change 0 < halfParent lam H ∧ halfParent lam H ≤ actQ lam ∧
    halfParent lam H < 1 at hp
  have hh := (messageRatio_weak_bounds hp.1.le hp.2.2).2
  have h1 := mul_le_mul_of_nonneg_right hrho (show 0 ≤ 1-halfParent lam H by linarith)
  have h2 := mul_le_mul_of_nonneg_left hh hgamma
  have hP : parentP i lam H rho ≤
      1-halfParent lam H+gamma i lam*(1-halfParent lam H/2) := by
    unfold parentP
    linarith
  have hprod := mul_le_mul_of_nonneg_left hP hp.1.le
  have hs := parent_quadratic_square (halfParent lam H) (gamma i lam) hgamma
  have hnonneg : 0 ≤ ((2+gamma i lam)*halfParent lam H-(1+gamma i lam))^2/
      (2*(2+gamma i lam)) := by positivity
  linarith

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_quadratic_square
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_quadratic_square
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_pP_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_pP_upper
