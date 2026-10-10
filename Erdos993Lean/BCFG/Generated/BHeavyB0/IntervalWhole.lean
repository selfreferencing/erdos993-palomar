module

public import Erdos993Lean.BCFG.Generated.BHeavyB0.Data
public import Erdos993Lean.F4Fast.WholeIdentity

/-! Generated transcription of B.heavy.b0
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.BHeavyB0

theorem intervalWhole_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [intervalWhole.lo, intervalWhole.hi-intervalWhole.lo])
      (Uni.bernVector M intervalWhole.coeffs) = true := by
  have hlo : intervalWhole.lo = 0 := by rfl
  have hhi : intervalWhole.hi = 1 := by rfl
  have hcoeff : intervalWhole.coeffs = lower := by rfl
  rw [hlo, hhi, sub_zero, hcoeff]
  exact Uni.checkEq_comp_zero_one (Uni.bernVector M lower)
theorem intervalWhole_positive :
    positiveCoefficients M (fun j => intervalWhole.coeffs.getD j 0) = true := by decide +kernel
theorem intervalWhole_nondegenerate : intervalWhole.lo < intervalWhole.hi := by decide +kernel
theorem intervalWhole_checked : intervalCheck M lower intervalWhole = true := by
  have hlt : decide (intervalWhole.lo < intervalWhole.hi) = true := by decide +kernel
  simp only [intervalCheck, intervalWhole_identity, intervalWhole_positive,
    hlt, Bool.and_self]

end Erdos993Lean.BCFG.CertData.BHeavyB0
