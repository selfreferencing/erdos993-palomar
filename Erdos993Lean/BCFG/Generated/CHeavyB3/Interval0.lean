module

public import Erdos993Lean.BCFG.Generated.CHeavyB3.Data
public import Erdos993Lean.BCFG.Generated.CHeavyB3.IntegerInterval0Checks

/-! Generated transcription of C.heavy.b3
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.CHeavyB3

theorem interval0_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [interval0.lo, interval0.hi-interval0.lo])
      (Uni.bernVector M interval0.coeffs) = true := by
  exact integer_interval0_identity
theorem interval0_positive :
    positiveCoefficients M (fun j => interval0.coeffs.getD j 0) = true := by decide +kernel
theorem interval0_nondegenerate : interval0.lo < interval0.hi := by decide +kernel
theorem interval0_checked : intervalCheck M lower interval0 = true := by
  have hlt : decide (interval0.lo < interval0.hi) = true := by decide +kernel
  simp only [intervalCheck, interval0_identity, interval0_positive,
    hlt, Bool.and_self]

end Erdos993Lean.BCFG.CertData.CHeavyB3
