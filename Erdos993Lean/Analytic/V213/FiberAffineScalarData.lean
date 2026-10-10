module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerArithmetic

/-!
Accepted F03 exponent sums/slopes and supporting squared root bounds,
in exact form. The typed printed identity controls lookup; numeric
positions only enumerate the grouped kernel checks. Canonical formula
binding and Int/Nat semantic soundness are proved in the checker.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

inductive FiberAffineScalarIdentity where
  | constant22 | slope22 | constant32 | slope32 | root22 | root32 | inverseRootW

structure FiberAffineScalarRow where
  printed : String
  left : lowMeanFraction
  right : lowMeanFraction
  terms : List (String × lowMeanFraction)
  minimumN : Option ℕ
  argument : Option lowMeanFraction
  rootBound : Option lowMeanFraction

def fiberAffineScalarPrinted : FiberAffineScalarIdentity → String
  | .constant22 => "F03:N>=22:constant"
  | .slope22 => "F03:N>=22:slope"
  | .constant32 => "F03:N>=32:constant"
  | .slope32 => "F03:N>=32:slope"
  | .root22 => "F03:root:sqrt(N)/(N+1):N=22"
  | .root32 => "F03:root:sqrt(N)/(N+1):N=32"
  | .inverseRootW => "F03:root:inverse_sqrt(W):W=3/2"

def fiberAffineScalarById : FiberAffineScalarIdentity → FiberAffineScalarRow
  | .constant22 => ⟨"F03:N>=22:constant", (32081, 115000), (3, 10), [("F03:N>=22:constant:mean_correction", (1, 46)), ("F03:N>=22:constant:amplitude_h", (87, 460)), ("F03:N>=22:constant:xi_correction", (32, 14375)), ("F03:N>=22:constant:mass_error", (1, 40)), ("F03:N>=22:constant:root_correction", (47, 1150))], some 22, none, none⟩
  | .slope22 => ⟨"F03:N>=22:slope", (1819, 3450), (8, 15), [("F03:N>=22:slope:base_slope", (1, 2)), ("F03:N>=22:slope:root_correction", (47, 1725))], some 22, none, none⟩
  | .constant32 => ⟨"F03:N>=32:constant", (24317, 123750), (1, 5), [("F03:N>=32:constant:mean_correction", (1, 66)), ("F03:N>=32:constant:amplitude_h", (251, 1980)), ("F03:N>=32:constant:xi_correction", (32, 20625)), ("F03:N>=32:constant:mass_error", (1, 60)), ("F03:N>=32:constant:root_correction", (2, 55))], some 32, none, none⟩
  | .slope32 => ⟨"F03:N>=32:slope", (173, 330), (21, 40), [("F03:N>=32:slope:base_slope", (1, 2)), ("F03:N>=32:slope:root_correction", (4, 165))], some 32, none, none⟩
  | .root22 => ⟨"F03:root:sqrt(N)/(N+1):N=22", (22, 529), (2209, 52900), [], some 22, some (22, 1), some (47, 230)⟩
  | .root32 => ⟨"F03:root:sqrt(N)/(N+1):N=32", (32, 1089), (4, 121), [], some 32, some (32, 1), some (2, 11)⟩
  | .inverseRootW => ⟨"F03:root:inverse_sqrt(W):W=3/2", (2, 3), (25, 36), [], none, some (3, 2), some (5, 6)⟩

def fiberAffineScalarIdentityAt : ℕ → FiberAffineScalarIdentity
  | 0 => .constant22
  | 1 => .slope22
  | 2 => .constant32
  | 3 => .slope32
  | 4 => .root22
  | 5 => .root32
  | _ => .inverseRootW

end Erdos993Lean.Analytic.V213
