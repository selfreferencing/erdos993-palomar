module

public import Erdos993Lean.Analytic.V213.FiberTailData00

/-!
Accepted F15 literal thirteen tail rows and complete Eq104 witnesses.
The ordinary maximum branch is explicit, and group x_a uses the table's
least mu, independently of the shifted large-tail mean m.
Eq89 and Eq91/92 are retained in F15.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberTailExpr : FiberTailIdentity → FiberTailRole → LowMeanIntegerExpr
  | .c1, .smallLog => fiberTailExpr_c1_smallLog
  | .c1, .smallGap => fiberTailExpr_c1_smallGap
  | .c1, .largeLog => fiberTailExpr_c1_largeLog
  | .c1, .largeGap => fiberTailExpr_c1_largeGap
  | .c2, .smallLog => fiberTailExpr_c2_smallLog
  | .c2, .smallGap => fiberTailExpr_c2_smallGap
  | .c2, .largeLog => fiberTailExpr_c2_largeLog
  | .c2, .largeGap => fiberTailExpr_c2_largeGap
  | .a, .smallLog => fiberTailExpr_a_smallLog
  | .a, .smallGap => fiberTailExpr_a_smallGap
  | .a, .largeLog => fiberTailExpr_a_largeLog
  | .a, .largeGap => fiberTailExpr_a_largeGap
  | .b10, .smallLog => fiberTailExpr_b10_smallLog
  | .b10, .smallGap => fiberTailExpr_b10_smallGap
  | .b10, .largeLog => fiberTailExpr_b10_largeLog
  | .b10, .largeGap => fiberTailExpr_b10_largeGap
  | .b19, .smallLog => fiberTailExpr_b19_smallLog
  | .b19, .smallGap => fiberTailExpr_b19_smallGap
  | .b19, .largeLog => fiberTailExpr_b19_largeLog
  | .b19, .largeGap => fiberTailExpr_b19_largeGap
  | .c, .smallLog => fiberTailExpr_c_smallLog
  | .c, .smallGap => fiberTailExpr_c_smallGap
  | .c, .largeLog => fiberTailExpr_c_largeLog
  | .c, .largeGap => fiberTailExpr_c_largeGap
  | .defGroup, .smallLog => fiberTailExpr_defGroup_smallLog
  | .defGroup, .smallGap => fiberTailExpr_defGroup_smallGap
  | .defGroup, .largeLog => fiberTailExpr_defGroup_largeLog
  | .defGroup, .largeGap => fiberTailExpr_defGroup_largeGap
  | .g, .smallLog => fiberTailExpr_g_smallLog
  | .g, .smallGap => fiberTailExpr_g_smallGap
  | .g, .largeLog => fiberTailExpr_g_largeLog
  | .g, .largeGap => fiberTailExpr_g_largeGap
  | .h40, .smallLog => fiberTailExpr_h40_smallLog
  | .h40, .smallGap => fiberTailExpr_h40_smallGap
  | .h40, .largeLog => fiberTailExpr_h40_largeLog
  | .h40, .largeGap => fiberTailExpr_h40_largeGap
  | .h45, .smallLog => fiberTailExpr_h45_smallLog
  | .h45, .smallGap => fiberTailExpr_h45_smallGap
  | .h45, .largeLog => fiberTailExpr_h45_largeLog
  | .h45, .largeGap => fiberTailExpr_h45_largeGap
  | .c5, .smallLog => fiberTailExpr_c5_smallLog
  | .c5, .smallGap => fiberTailExpr_c5_smallGap
  | .c5, .largeLog => fiberTailExpr_c5_largeLog
  | .c5, .largeGap => fiberTailExpr_c5_largeGap
  | .c6, .smallLog => fiberTailExpr_c6_smallLog
  | .c6, .smallGap => fiberTailExpr_c6_smallGap
  | .c6, .largeLog => fiberTailExpr_c6_largeLog
  | .c6, .largeGap => fiberTailExpr_c6_largeGap
  | .c78, .smallLog => fiberTailExpr_c78_smallLog
  | .c78, .smallGap => fiberTailExpr_c78_smallGap
  | .c78, .largeLog => fiberTailExpr_c78_largeLog
  | .c78, .largeGap => fiberTailExpr_c78_largeGap

end Erdos993Lean.Analytic.V213
