module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerArithmetic

/-!
Remaining accepted F03 polynomial/discriminant controls, in exact form.
Each typed identity denotes its printed formula/role. Coefficients retain the
source's ascending-power order; auxiliary leaves retain their exact fractions.
This export alone is not a kernel or analytic correctness claim.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

inductive FiberAffinePolynomialIdentity where
  | a | v | c | p | q | quarticLeft | quarticRight | errorA | errorQ | positiveQuadratic | discriminant

structure FiberAffinePolynomialRow where
  printed : String
  coefficients : List lowMeanFraction

def fiberAffinePolynomialPrinted : FiberAffinePolynomialIdentity → String
  | .a => "F03:quartic_positive_decomposition:A"
  | .v => "F03:quartic_positive_decomposition:V0"
  | .c => "F03:quartic_positive_decomposition:c"
  | .p => "F03:quartic_positive_decomposition:p"
  | .q => "F03:quartic_positive_decomposition:qstar"
  | .quarticLeft => "F03:quartic_positive_decomposition:lhs"
  | .quarticRight => "F03:quartic_positive_decomposition:rhs"
  | .errorA => "F03:A-p"
  | .errorQ => "F03:qstar-(1-V0)"
  | .positiveQuadratic => "F03:positive_quadratic_square"
  | .discriminant => "F03:discriminant_polynomial"

def fiberAffinePolynomialById : FiberAffinePolynomialIdentity → FiberAffinePolynomialRow
  | .a => ⟨"F03:quartic_positive_decomposition:A", [(7903, 6250), (-34401, 25000), (21, 40)]⟩
  | .v => ⟨"F03:quartic_positive_decomposition:V0", [(-45819, 12500), (201323, 50000), (-63, 80)]⟩
  | .c => ⟨"F03:quartic_positive_decomposition:c", [(9, 1), (0, 1), (-9, 8)]⟩
  | .p => ⟨"F03:quartic_positive_decomposition:p", [(63, 50), (-69, 50), (21, 40)]⟩
  | .q => ⟨"F03:quartic_positive_decomposition:qstar", [(14, 3), (-4, 1), (4, 5)]⟩
  | .quarticLeft => ⟨"F03:quartic_positive_decomposition:lhs", [(203, 225), (937, 75), (-10111, 600), (1901, 200), (-1457, 800)]⟩
  | .quarticRight => ⟨"F03:quartic_positive_decomposition:rhs", [(203, 225), (937, 75), (-10111, 600), (1901, 200), (-1457, 800)]⟩
  | .errorA => ⟨"F03:A-p", [(14, 3125), (99, 25000), (0, 1)]⟩
  | .errorQ => ⟨"F03:qstar-(1-V0)", [(43, 37500), (1323, 50000), (1, 80)]⟩
  | .positiveQuadratic => ⟨"F03:positive_quadratic_square", [(12, 1), (-17, 1), (27, 4)]⟩
  | .discriminant => ⟨"F03:discriminant_polynomial", [(2132, 1), (-2941, 1), (1015, 1)]⟩

def fiberAffinePolynomialIdentityAt : ℕ → FiberAffinePolynomialIdentity
  | 0 => .a
  | 1 => .v
  | 2 => .c
  | 3 => .p
  | 4 => .q
  | 5 => .quarticLeft
  | 6 => .quarticRight
  | 7 => .errorA
  | 8 => .errorQ
  | 9 => .positiveQuadratic
  | _ => .discriminant

inductive FiberAffineAuxiliaryIdentity where
  | deficit | sqrt3 | ratio | ratioUpper | vAt | vUpper | margin | required | squareCoefficient | squareShift | squareConstant

def fiberAffineAuxiliaryPrinted : FiberAffineAuxiliaryIdentity → String
  | .deficit => "F03:discriminant_deficit"
  | .sqrt3 => "F03:sqrt3_lower"
  | .ratio => "F03:rational_comparison"
  | .ratioUpper => "F03:rational_comparison:upper"
  | .vAt => "F03:V0_at_three_halves"
  | .vUpper => "F03:V0_upper"
  | .margin => "F03:final_margin"
  | .required => "F03:required_margin"
  | .squareCoefficient => "F03:positive_quadratic_square:square_coefficient"
  | .squareShift => "F03:positive_quadratic_square:square_shift"
  | .squareConstant => "F03:positive_quadratic_square:constant"

def fiberAffineAuxiliaryById : FiberAffineAuxiliaryIdentity → String × lowMeanFraction
  | .deficit => ("F03:discriminant_deficit", (6439, 1))
  | .sqrt3 => ("F03:sqrt3_lower", (45, 26))
  | .ratio => ("F03:rational_comparison", (91, 81))
  | .ratioUpper => ("F03:rational_comparison:upper", (9, 8))
  | .vAt => ("F03:V0_at_three_halves", (120459, 200000))
  | .vUpper => ("F03:V0_upper", (5, 8))
  | .margin => ("F03:final_margin", (587, 16200))
  | .required => ("F03:required_margin", (1, 28))
  | .squareCoefficient => ("F03:positive_quadratic_square:square_coefficient", (27, 4))
  | .squareShift => ("F03:positive_quadratic_square:square_shift", (-34, 27))
  | .squareConstant => ("F03:positive_quadratic_square:constant", (35, 27))

def fiberAffineAuxiliaryIdentityAt : ℕ → FiberAffineAuxiliaryIdentity
  | 0 => .deficit
  | 1 => .sqrt3
  | 2 => .ratio
  | 3 => .ratioUpper
  | 4 => .vAt
  | 5 => .vUpper
  | 6 => .margin
  | 7 => .required
  | 8 => .squareCoefficient
  | 9 => .squareShift
  | _ => .squareConstant

end Erdos993Lean.Analytic.V213
