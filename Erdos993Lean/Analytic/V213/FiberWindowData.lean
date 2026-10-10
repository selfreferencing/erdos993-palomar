module

public import Erdos993Lean.Analytic.V213.FiberWindowData10

/-!
All ten accepted F13 Eq102/103 windows, keyed by printed window identity.
Full rational trees retain the actual accepted F05 class parameters,
N0=mu_D*l+2, the degree-five exponential sum, capped inverse, X test and
both signs of the unweighted price. Data only until shape/kernel checks.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWindowExpr : FiberWindowIdentity → FiberWindowRole → LowMeanIntegerExpr
  | .window1, .gain => fiberWindowExpr_window1_gain
  | .window1, .rate => fiberWindowExpr_window1_rate
  | .window1, .bonus => fiberWindowExpr_window1_bonus
  | .window1, .anchor => fiberWindowExpr_window1_anchor
  | .window1, .inverse => fiberWindowExpr_window1_inverse
  | .window1, .minorant => fiberWindowExpr_window1_minorant
  | .window1, .gap => fiberWindowExpr_window1_gap
  | .window1, .price => fiberWindowExpr_window1_price
  | .window2, .gain => fiberWindowExpr_window2_gain
  | .window2, .rate => fiberWindowExpr_window2_rate
  | .window2, .bonus => fiberWindowExpr_window2_bonus
  | .window2, .anchor => fiberWindowExpr_window2_anchor
  | .window2, .inverse => fiberWindowExpr_window2_inverse
  | .window2, .minorant => fiberWindowExpr_window2_minorant
  | .window2, .gap => fiberWindowExpr_window2_gap
  | .window2, .price => fiberWindowExpr_window2_price
  | .window3, .gain => fiberWindowExpr_window3_gain
  | .window3, .rate => fiberWindowExpr_window3_rate
  | .window3, .bonus => fiberWindowExpr_window3_bonus
  | .window3, .anchor => fiberWindowExpr_window3_anchor
  | .window3, .inverse => fiberWindowExpr_window3_inverse
  | .window3, .minorant => fiberWindowExpr_window3_minorant
  | .window3, .gap => fiberWindowExpr_window3_gap
  | .window3, .price => fiberWindowExpr_window3_price
  | .window4, .gain => fiberWindowExpr_window4_gain
  | .window4, .rate => fiberWindowExpr_window4_rate
  | .window4, .bonus => fiberWindowExpr_window4_bonus
  | .window4, .anchor => fiberWindowExpr_window4_anchor
  | .window4, .inverse => fiberWindowExpr_window4_inverse
  | .window4, .minorant => fiberWindowExpr_window4_minorant
  | .window4, .gap => fiberWindowExpr_window4_gap
  | .window4, .price => fiberWindowExpr_window4_price
  | .window5, .gain => fiberWindowExpr_window5_gain
  | .window5, .rate => fiberWindowExpr_window5_rate
  | .window5, .bonus => fiberWindowExpr_window5_bonus
  | .window5, .anchor => fiberWindowExpr_window5_anchor
  | .window5, .inverse => fiberWindowExpr_window5_inverse
  | .window5, .minorant => fiberWindowExpr_window5_minorant
  | .window5, .gap => fiberWindowExpr_window5_gap
  | .window5, .price => fiberWindowExpr_window5_price
  | .window6, .gain => fiberWindowExpr_window6_gain
  | .window6, .rate => fiberWindowExpr_window6_rate
  | .window6, .bonus => fiberWindowExpr_window6_bonus
  | .window6, .anchor => fiberWindowExpr_window6_anchor
  | .window6, .inverse => fiberWindowExpr_window6_inverse
  | .window6, .minorant => fiberWindowExpr_window6_minorant
  | .window6, .gap => fiberWindowExpr_window6_gap
  | .window6, .price => fiberWindowExpr_window6_price
  | .window7, .gain => fiberWindowExpr_window7_gain
  | .window7, .rate => fiberWindowExpr_window7_rate
  | .window7, .bonus => fiberWindowExpr_window7_bonus
  | .window7, .anchor => fiberWindowExpr_window7_anchor
  | .window7, .inverse => fiberWindowExpr_window7_inverse
  | .window7, .minorant => fiberWindowExpr_window7_minorant
  | .window7, .gap => fiberWindowExpr_window7_gap
  | .window7, .price => fiberWindowExpr_window7_price
  | .window8, .gain => fiberWindowExpr_window8_gain
  | .window8, .rate => fiberWindowExpr_window8_rate
  | .window8, .bonus => fiberWindowExpr_window8_bonus
  | .window8, .anchor => fiberWindowExpr_window8_anchor
  | .window8, .inverse => fiberWindowExpr_window8_inverse
  | .window8, .minorant => fiberWindowExpr_window8_minorant
  | .window8, .gap => fiberWindowExpr_window8_gap
  | .window8, .price => fiberWindowExpr_window8_price
  | .window9, .gain => fiberWindowExpr_window9_gain
  | .window9, .rate => fiberWindowExpr_window9_rate
  | .window9, .bonus => fiberWindowExpr_window9_bonus
  | .window9, .anchor => fiberWindowExpr_window9_anchor
  | .window9, .inverse => fiberWindowExpr_window9_inverse
  | .window9, .minorant => fiberWindowExpr_window9_minorant
  | .window9, .gap => fiberWindowExpr_window9_gap
  | .window9, .price => fiberWindowExpr_window9_price
  | .window10, .gain => fiberWindowExpr_window10_gain
  | .window10, .rate => fiberWindowExpr_window10_rate
  | .window10, .bonus => fiberWindowExpr_window10_bonus
  | .window10, .anchor => fiberWindowExpr_window10_anchor
  | .window10, .inverse => fiberWindowExpr_window10_inverse
  | .window10, .minorant => fiberWindowExpr_window10_minorant
  | .window10, .gap => fiberWindowExpr_window10_gap
  | .window10, .price => fiberWindowExpr_window10_price

end Erdos993Lean.Analytic.V213
