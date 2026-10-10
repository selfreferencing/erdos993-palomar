module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerArithmetic

/-!
Accepted F02 leaves for exact T3 Eq83 at t0=(11/10)^2,z=1/19.
The typed lookup uses printed identities. All source fractions retain explicit
Int numerators/Nat denominators; canonical formula binding is checked separately.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

inductive FiberLowerCoefficientIdentity where
  | a0 | a1 | a2 | v0 | v1 | v2

structure FiberLowerCoefficientRow where
  actual : lowMeanFraction
  bound : lowMeanFraction
  difference : lowMeanFraction
  power : ℕ
  sqrtPoint : lowMeanFraction
  reciprocalMean : lowMeanFraction

def fiberLowerCoefficientPrinted : FiberLowerCoefficientIdentity → String
  | .a0 => "F02:A-A_b:a^0"
  | .a1 => "F02:A-A_b:a^1"
  | .a2 => "F02:A-A_b:a^2"
  | .v0 => "F02:V-V_b:a^0"
  | .v1 => "F02:V-V_b:a^1"
  | .v2 => "F02:V-V_b:a^2"

def fiberLowerCoefficientById : FiberLowerCoefficientIdentity → FiberLowerCoefficientRow
  -- F02:A-A_b:a^0
  | .a0 => ⟨(115411, 380000), (303, 1000), (271, 380000), 0, (11, 10), (1, 19)⟩
  -- F02:A-A_b:a^1
  | .a1 => ⟨(-475700266251, 703486873100), (-1353, 2000), (4172068023, 14069737462000), 1, (11, 10), (1, 19)⟩
  -- F02:A-A_b:a^2
  | .a2 => ⟨(1249500, 3059969), (51, 125), (129081, 382496125), 2, (11, 10), (1, 19)⟩
  -- F02:V-V_b:a^0
  | .v0 => ⟨(189, 100), (189, 100), (0, 1), 0, (11, 10), (1, 19)⟩
  -- F02:V-V_b:a^1
  | .v1 => ⟨(-1436604266451, 851219116451), (-211, 125), (31700264786, 106402389556375), 1, (11, 10), (1, 19)⟩
  -- F02:V-V_b:a^2
  | .v2 => ⟨(-197425000, 370256249), (-533, 1000), (-78419283, 370256249000), 2, (11, 10), (1, 19)⟩

def fiberLowerCoefficientIdentityAt : ℕ → FiberLowerCoefficientIdentity
  | 0 => .a0
  | 1 => .a1
  | 2 => .a2
  | 3 => .v0
  | 4 => .v1
  | _ => .v2

end Erdos993Lean.Analytic.V213
