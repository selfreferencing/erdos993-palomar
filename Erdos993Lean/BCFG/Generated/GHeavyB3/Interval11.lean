module

public import Erdos993Lean.BCFG.Generated.GHeavyB3.Data
public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerInterval11Checks

/-! Generated transcription of G.heavy.b3
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.GHeavyB3

theorem interval11_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [interval11.lo, interval11.hi-interval11.lo])
      (Uni.bernVector M interval11.coeffs) = true := by
  exact integer_interval11_identity
theorem interval11_positive :
    positiveCoefficients M (fun j => interval11.coeffs.getD j 0) = true := by decide +kernel
theorem interval11_nondegenerate : interval11.lo < interval11.hi := by decide +kernel
theorem interval11_checked : intervalCheck M lower interval11 = true := by
  have hlt : decide (interval11.lo < interval11.hi) = true := by decide +kernel
  simp only [intervalCheck, interval11_identity, interval11_positive,
    hlt, Bool.and_self]

end Erdos993Lean.BCFG.CertData.GHeavyB3
