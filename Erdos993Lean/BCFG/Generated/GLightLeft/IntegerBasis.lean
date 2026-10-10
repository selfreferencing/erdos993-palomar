module

public import Erdos993Lean.BCFG.Generated.GLightLeft.IntegerTables
public import Erdos993Lean.F4Fast.IntegerPolynomial
public import Erdos993Lean.F4Fast.RangeAll

/-! Integer Bernstein basis checks and exact cast recovery of every original basis list. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.GLightLeft

theorem integer_basis_checks :
    (List.range (M+1)).all (fun j => decide
      (IUni.bernBasis M j = basisInt.getD j [])) = true := by
  decide +kernel

theorem integer_basis_checked : ∀ j < M+1,
    Uni.bernBasis M j = IUni.castRat (basisInt.getD j []) := by
  intro j hj
  have hc := of_decide_eq_true
    (Erdos993Lean.F4Fast.forall_lt_of_range_all integer_basis_checks j hj)
  rw [← IUni.castRat_bernBasis, hc]

end Erdos993Lean.BCFG.CertData.GLightLeft
