module

public import Erdos993Lean.BCFG.TailRationalGates

/-! Generic all-real-response square minimum and the two printed tail margins. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem tail_quadratic_gt {A B C a b c margin : ℝ}
    (hA : a ≤ A) (hB : |B| ≤ b) (hb : 0 ≤ b) (hc : 0 < c) (hC : c ≤ C)
    (hmargin : margin+b^2/c < a) (y : ℝ) :
    margin < A+2*B*y+C*y^2 := by
  have hpm := abs_le.mp hB
  have hprod := mul_nonneg (show 0 ≤ b-B by linarith only [hpm.2])
    (show 0 ≤ b+B by linarith only [hpm.1])
  have hsq : B^2 ≤ b^2 := by nlinarith only [hprod]
  have hdiv := div_le_div_of_nonneg_right hsq hc.le
  have hcomplete : (c*y+B)^2/c = c*y^2+2*B*y+B^2/c := by
    field_simp [hc.ne'] <;> ring
  have hnonneg : 0 ≤ c*y^2+2*B*y+B^2/c := by
    rw [← hcomplete]
    exact div_nonneg (sq_nonneg _) hc.le
  have hextra := mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg y)
  nlinarith only [hA,hmargin,hdiv,hnonneg,hextra]

theorem tail_BC_square_minimum {K P eta t0 : ℝ}
    (hK : 397/500 ≤ K-P) (hC : 169/375 ≤ eta-P)
    (hB : |P-t0| ≤ 89/189) (z : ℝ) :
    (1 : ℝ)/4 < K-P+2*(P-t0)*(1-z)+(eta-P)*(1-z)^2 := by
  exact tail_quadratic_gt hK hB
    (by positivity) (by positivity)
    hC tail_BC_square_gate (1-z)

theorem tail_FG_square_minimum {K P eta t0 : ℝ}
    (hK : 4/5 ≤ K-P) (hC : 329/120 ≤ eta-P)
    (hB : |P-t0| ≤ tailFGResponse) (z : ℝ) :
    (1 : ℝ)/2 < K-P+2*(P-t0)*(1-z)+(eta-P)*(1-z)^2 := by
  exact tail_quadratic_gt hK hB tail_FG_response_positive_gate.le
    (div_pos (by exact_mod_cast (by decide +kernel : 0 < (329 : ℕ)))
      (by exact_mod_cast (by decide +kernel : 0 < (120 : ℕ))))
    hC tail_FG_square_gate (1-z)

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.tail_quadratic_gt
#print axioms Erdos993Lean.BCFG.Analytic.tail_quadratic_gt
#check Erdos993Lean.BCFG.Analytic.tail_BC_square_minimum
#print axioms Erdos993Lean.BCFG.Analytic.tail_BC_square_minimum
#check Erdos993Lean.BCFG.Analytic.tail_FG_square_minimum
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_square_minimum
