module

public import Erdos993Lean.F4U.Light.Construction.CoefficientSigns
public import Erdos993Lean.F4U.Light.Construction.ChildBounds
public import Erdos993Lean.F4U.Light.Construction.PaymentAlgebra

/-! The proved upper h bound and the exact correlated identity apply to the
original parent P and payment, with every source/response field fixed. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem p_original_bounds {lam Y : ℝ} (hlam : 0 < lam) : 0 < p lam Y ∧ p lam Y < 1 := by
  have he := Real.exp_pos (-Y)
  have hden : 0 < 1+lam*Real.exp (-Y) := by positivity
  constructor
  · unfold p
    positivity
  · unfold p
    rw [div_lt_one hden]
    linarith

 theorem parentP_le_parentPPlus {r : Row} {lam Y rho : ℝ}
    (hlam : InRow r lam) (hY : 0 < Y) (hcap : parentH Y ≤ q lam) :
    parentP r lam Y rho ≤ parentPPlus r lam (parentH Y) rho := by
  have hp := p_original_bounds (inRow_lambda_bounds hlam).1 (Y := Y)
  have hh := childH_le_parentHBound hp.1.le hp.2
  simp only [F4Unified.childH, F4Unified.phi, if_neg hp.1.ne'] at hh
  have hg := (inRow_coefficient_positive hlam).2.2.1
  have hscaled := add_le_add_left (mul_le_mul_of_nonneg_left hh hg.le) (rho*(1-p lam Y))
  simpa only [parentP, parentPPlus, pH_original, mul_div_assoc, add_comm] using hscaled

 theorem payment_parentPPlus_le {r : Row} {lam Y rho u y : ℝ}
    (hlam : InRow r lam) (hY : 0 < Y) (hcap : parentH Y ≤ q lam) :
    paymentWithParentP r lam Y rho u y (parentPPlus r lam (parentH Y) rho) ≤
      payment r lam Y rho u y := by
  rw [← paymentWithParentP_original]
  exact correlated_parent_replacement_le r lam Y rho u y
    (parentP r lam Y rho) (parentPPlus r lam (parentH Y) rho) hY
    (p_original_bounds (inRow_lambda_bounds hlam).1).1.le
    (parentP_le_parentPPlus hlam hY hcap)

#print axioms p_original_bounds
#print axioms parentP_le_parentPPlus
#print axioms payment_parentPPlus_le

end
end F4Unified.LightConstruction
