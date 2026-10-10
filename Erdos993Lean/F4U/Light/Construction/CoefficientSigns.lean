module

public import Erdos993Lean.F4U.Light.Construction.Domain

/-! Positivity of the retained row coefficients and parent P-plus field.
Every coefficient is the literal affine function from the frozen contract. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem inRow_coefficient_positive {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    0 < alpha r lam ∧ 0 < beta r lam ∧ 0 < gamma r lam ∧ 0 < delta r lam := by
  cases r <;> simp only [InRow, rowData] at hlam
  all_goals
    simp only [alpha, beta, gamma, delta, field, rowData]
    norm_num
    refine ⟨?_,?_,?_,?_⟩ <;> linarith [hlam.1,hlam.2]

 theorem parentHBound_positive {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < parentHBound x := by
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (show 0 ≤ 1+x by linarith)]
  unfold parentHBound
  nlinarith

 theorem parentPPlus_positive {r : Row} {lam H rho : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam) (hrho : 0 ≤ rho) :
    0 < parentPPlus r lam H rho := by
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,_,_,_,_,_,_,_,_,_,_,hp,hp1,_⟩
  have hc := inRow_coefficient_positive hlam
  have hV := parentHBound_positive hp.le (by linarith : pH lam H ≤ 1)
  unfold parentPPlus
  exact add_pos_of_nonneg_of_pos (mul_nonneg hrho hp1.le) (mul_pos hc.2.2.1 hV)

#print axioms inRow_coefficient_positive
#print axioms parentHBound_positive
#print axioms parentPPlus_positive

end
end F4Unified.LightConstruction
