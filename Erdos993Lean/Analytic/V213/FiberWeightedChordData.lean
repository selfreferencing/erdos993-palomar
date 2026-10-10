module

public import Erdos993Lean.Analytic.V213.FiberWeightedChordDataH

/-!
All eighteen accepted F12 weighted-chord identities. Canonical trees
retain actual F10 chord/F11 weight leaves; reduced Int/Nat nodes are
untrusted data until the separate shape/checker consumes them.
Source: Eq89.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWeightedChordExpr : FiberWeightedChordIdentity → FiberWeightedChordRole → LowMeanIntegerExpr
  | .a_third_p042, .logarithm => fiberWeightedChordExpr_a_third_p042_logarithm
  | .a_third_p042, .gap => fiberWeightedChordExpr_a_third_p042_gap
  | .a_p042_half, .logarithm => fiberWeightedChordExpr_a_p042_half_logarithm
  | .a_p042_half, .gap => fiberWeightedChordExpr_a_p042_half_gap
  | .a_half_p06, .logarithm => fiberWeightedChordExpr_a_half_p06_logarithm
  | .a_half_p06, .gap => fiberWeightedChordExpr_a_half_p06_gap
  | .b_third_p042, .logarithm => fiberWeightedChordExpr_b_third_p042_logarithm
  | .b_third_p042, .gap => fiberWeightedChordExpr_b_third_p042_gap
  | .b_p042_half, .logarithm => fiberWeightedChordExpr_b_p042_half_logarithm
  | .b_p042_half, .gap => fiberWeightedChordExpr_b_p042_half_gap
  | .b_half_p06, .logarithm => fiberWeightedChordExpr_b_half_p06_logarithm
  | .b_half_p06, .gap => fiberWeightedChordExpr_b_half_p06_gap
  | .c_third_p042, .logarithm => fiberWeightedChordExpr_c_third_p042_logarithm
  | .c_third_p042, .gap => fiberWeightedChordExpr_c_third_p042_gap
  | .c_p042_half, .logarithm => fiberWeightedChordExpr_c_p042_half_logarithm
  | .c_p042_half, .gap => fiberWeightedChordExpr_c_p042_half_gap
  | .c_half_p06, .logarithm => fiberWeightedChordExpr_c_half_p06_logarithm
  | .c_half_p06, .gap => fiberWeightedChordExpr_c_half_p06_gap
  | .d_third_p042, .logarithm => fiberWeightedChordExpr_d_third_p042_logarithm
  | .d_third_p042, .gap => fiberWeightedChordExpr_d_third_p042_gap
  | .d_p042_half, .logarithm => fiberWeightedChordExpr_d_p042_half_logarithm
  | .d_p042_half, .gap => fiberWeightedChordExpr_d_p042_half_gap
  | .d_half_p052, .logarithm => fiberWeightedChordExpr_d_half_p052_logarithm
  | .d_half_p052, .gap => fiberWeightedChordExpr_d_half_p052_gap
  | .f_third_p042, .logarithm => fiberWeightedChordExpr_f_third_p042_logarithm
  | .f_third_p042, .gap => fiberWeightedChordExpr_f_third_p042_gap
  | .f_p042_half, .logarithm => fiberWeightedChordExpr_f_p042_half_logarithm
  | .f_p042_half, .gap => fiberWeightedChordExpr_f_p042_half_gap
  | .f_half_p052, .logarithm => fiberWeightedChordExpr_f_half_p052_logarithm
  | .f_half_p052, .gap => fiberWeightedChordExpr_f_half_p052_gap
  | .g_third_p042, .logarithm => fiberWeightedChordExpr_g_third_p042_logarithm
  | .g_third_p042, .gap => fiberWeightedChordExpr_g_third_p042_gap
  | .g_p042_p044, .logarithm => fiberWeightedChordExpr_g_p042_p044_logarithm
  | .g_p042_p044, .gap => fiberWeightedChordExpr_g_p042_p044_gap
  | .h_third_p038, .logarithm => fiberWeightedChordExpr_h_third_p038_logarithm
  | .h_third_p038, .gap => fiberWeightedChordExpr_h_third_p038_gap

end Erdos993Lean.Analytic.V213
