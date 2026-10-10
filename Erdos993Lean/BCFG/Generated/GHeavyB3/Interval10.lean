module

public import Erdos993Lean.BCFG.Generated.GHeavyB3.Data
public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerInterval10Checks

/-! Generated transcription of G.heavy.b3
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.GHeavyB3

theorem interval10_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [interval10.lo, interval10.hi-interval10.lo])
      (Uni.bernVector M interval10.coeffs) = true := by
  exact integer_interval10_identity
theorem interval10_positive :
    positiveCoefficients M (fun j => interval10.coeffs.getD j 0) = true := by decide +kernel
theorem interval10_nondegenerate : interval10.lo < interval10.hi := by decide +kernel
theorem interval10_checked : intervalCheck M lower interval10 = true := by
  have hlt : decide (interval10.lo < interval10.hi) = true := by decide +kernel
  simp only [intervalCheck, interval10_identity, interval10_positive,
    hlt, Bool.and_self]

end Erdos993Lean.BCFG.CertData.GHeavyB3
