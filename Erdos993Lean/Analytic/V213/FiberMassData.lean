module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerArithmetic

/-!
Reviewed F01 leaves for exact Eq74. Every row is bound
to its printed window and minimum width identity. Checking is
explicit signed-integer cross multiplication with positive natural denominators.
This module contains data and definitions; the analytic all-width bound is separate.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

structure FiberMassBoundRow where
  minimumN : ℕ
  window : lowMeanFraction
  reciprocalN : Bool
  left : lowMeanFraction
  right : lowMeanFraction
  bound : lowMeanFraction

inductive FiberMassIdentity where
  | w1_n14
  | w15_n22
  | w15_n32

def fiberMassIdentityPrinted : FiberMassIdentity → String
  | .w1_n14 => "F01:W=1:N>=14"
  | .w15_n22 => "F01:W=3/2:N>=22"
  | .w15_n32 => "F01:W=3/2:N>=32"

def fiberMassBoundById : FiberMassIdentity → FiberMassBoundRow
  -- F01:W=1:N>=14
  | .w1_n14 => ⟨14, (1, 1), true, (4802, 14641), (25, 81), (1, 3)⟩
  -- F01:W=3/2:N>=22
  | .w15_n22 => ⟨22, (3, 2), false, (1476225, 70860608), (23, 1008), (1, 40)⟩
  -- F01:W=3/2:N>=32
  | .w15_n32 => ⟨32, (3, 2), false, (4096, 304425), (9604, 637659), (1, 60)⟩


def fiberMassIdentityAt : ℕ → FiberMassIdentity
  | 0 => .w1_n14
  | 1 => .w15_n22
  | _ => .w15_n32

def fiberMassBoundCheck (x : FiberMassBoundRow) : Bool :=
  decide (0 < x.left.2 ∧ 0 < x.right.2 ∧ 0 < x.bound.2 ∧
    x.left.1 * (x.bound.2 : ℤ) < x.bound.1 * (x.left.2 : ℤ) ∧
    x.right.1 * (x.bound.2 : ℤ) < x.bound.1 * (x.right.2 : ℤ))

end Erdos993Lean.Analytic.V213
