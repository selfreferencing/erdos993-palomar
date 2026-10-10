module

public import Erdos993Lean.BCFG.Generated.CHeavyB3.Data
public import Erdos993Lean.BCFG.Generated.CHeavyB3.IntegerInterval1Checks

/-! Generated transcription of C.heavy.b3
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.CHeavyB3

theorem interval1_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [interval1.lo, interval1.hi-interval1.lo])
      (Uni.bernVector M interval1.coeffs) = true := by
  exact integer_interval1_identity
theorem interval1_positive :
    positiveCoefficients M (fun j => interval1.coeffs.getD j 0) = true := by decide +kernel
theorem interval1_nondegenerate : interval1.lo < interval1.hi := by decide +kernel
theorem interval1_checked : intervalCheck M lower interval1 = true := by
  have hlt : decide (interval1.lo < interval1.hi) = true := by decide +kernel
  simp only [intervalCheck, interval1_identity, interval1_positive,
    hlt, Bool.and_self]

end Erdos993Lean.BCFG.CertData.CHeavyB3
