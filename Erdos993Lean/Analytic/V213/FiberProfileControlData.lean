module

public import Erdos993Lean.Analytic.V213.FiberProfileControlDataE

/-!
Accepted F10 complete canonical expression dispatcher; all 24 named controls.
Data only: canonical erased trees and Int/Nat nodes must be separately
checked before semantic use.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberProfileControlExpr : FiberProfileControlIdentity → FiberProfileControlRole → LowMeanIntegerExpr
  | .a_third, .c0 => fiberProfileControlExpr_a_third_c0
  | .a_third, .c1 => fiberProfileControlExpr_a_third_c1
  | .a_third, .c2 => fiberProfileControlExpr_a_third_c2
  | .a_third, .firstTest => fiberProfileControlExpr_a_third_firstTest
  | .a_third, .secondTest => fiberProfileControlExpr_a_third_secondTest
  | .a_p042, .c0 => fiberProfileControlExpr_a_p042_c0
  | .a_p042, .c1 => fiberProfileControlExpr_a_p042_c1
  | .a_p042, .c2 => fiberProfileControlExpr_a_p042_c2
  | .a_p042, .firstTest => fiberProfileControlExpr_a_p042_firstTest
  | .a_p042, .secondTest => fiberProfileControlExpr_a_p042_secondTest
  | .a_half, .c0 => fiberProfileControlExpr_a_half_c0
  | .a_half, .c1 => fiberProfileControlExpr_a_half_c1
  | .a_half, .c2 => fiberProfileControlExpr_a_half_c2
  | .a_half, .firstTest => fiberProfileControlExpr_a_half_firstTest
  | .a_half, .secondTest => fiberProfileControlExpr_a_half_secondTest
  | .a_p06, .c0 => fiberProfileControlExpr_a_p06_c0
  | .a_p06, .c1 => fiberProfileControlExpr_a_p06_c1
  | .a_p06, .c2 => fiberProfileControlExpr_a_p06_c2
  | .a_p06, .firstTest => fiberProfileControlExpr_a_p06_firstTest
  | .a_p06, .secondTest => fiberProfileControlExpr_a_p06_secondTest
  | .b_third, .c0 => fiberProfileControlExpr_b_third_c0
  | .b_third, .c1 => fiberProfileControlExpr_b_third_c1
  | .b_third, .c2 => fiberProfileControlExpr_b_third_c2
  | .b_third, .firstTest => fiberProfileControlExpr_b_third_firstTest
  | .b_third, .secondTest => fiberProfileControlExpr_b_third_secondTest
  | .b_p042, .c0 => fiberProfileControlExpr_b_p042_c0
  | .b_p042, .c1 => fiberProfileControlExpr_b_p042_c1
  | .b_p042, .c2 => fiberProfileControlExpr_b_p042_c2
  | .b_p042, .firstTest => fiberProfileControlExpr_b_p042_firstTest
  | .b_p042, .secondTest => fiberProfileControlExpr_b_p042_secondTest
  | .b_half, .c0 => fiberProfileControlExpr_b_half_c0
  | .b_half, .c1 => fiberProfileControlExpr_b_half_c1
  | .b_half, .c2 => fiberProfileControlExpr_b_half_c2
  | .b_half, .firstTest => fiberProfileControlExpr_b_half_firstTest
  | .b_half, .secondTest => fiberProfileControlExpr_b_half_secondTest
  | .b_p06, .c0 => fiberProfileControlExpr_b_p06_c0
  | .b_p06, .c1 => fiberProfileControlExpr_b_p06_c1
  | .b_p06, .c2 => fiberProfileControlExpr_b_p06_c2
  | .b_p06, .firstTest => fiberProfileControlExpr_b_p06_firstTest
  | .b_p06, .secondTest => fiberProfileControlExpr_b_p06_secondTest
  | .d_third, .c0 => fiberProfileControlExpr_d_third_c0
  | .d_third, .c1 => fiberProfileControlExpr_d_third_c1
  | .d_third, .c2 => fiberProfileControlExpr_d_third_c2
  | .d_third, .firstTest => fiberProfileControlExpr_d_third_firstTest
  | .d_third, .secondTest => fiberProfileControlExpr_d_third_secondTest
  | .d_p042, .c0 => fiberProfileControlExpr_d_p042_c0
  | .d_p042, .c1 => fiberProfileControlExpr_d_p042_c1
  | .d_p042, .c2 => fiberProfileControlExpr_d_p042_c2
  | .d_p042, .firstTest => fiberProfileControlExpr_d_p042_firstTest
  | .d_p042, .secondTest => fiberProfileControlExpr_d_p042_secondTest
  | .d_half, .c0 => fiberProfileControlExpr_d_half_c0
  | .d_half, .c1 => fiberProfileControlExpr_d_half_c1
  | .d_half, .c2 => fiberProfileControlExpr_d_half_c2
  | .d_half, .firstTest => fiberProfileControlExpr_d_half_firstTest
  | .d_half, .secondTest => fiberProfileControlExpr_d_half_secondTest
  | .d_p052, .c0 => fiberProfileControlExpr_d_p052_c0
  | .d_p052, .c1 => fiberProfileControlExpr_d_p052_c1
  | .d_p052, .c2 => fiberProfileControlExpr_d_p052_c2
  | .d_p052, .firstTest => fiberProfileControlExpr_d_p052_firstTest
  | .d_p052, .secondTest => fiberProfileControlExpr_d_p052_secondTest
  | .g_third, .c0 => fiberProfileControlExpr_g_third_c0
  | .g_third, .c1 => fiberProfileControlExpr_g_third_c1
  | .g_third, .c2 => fiberProfileControlExpr_g_third_c2
  | .g_third, .firstTest => fiberProfileControlExpr_g_third_firstTest
  | .g_third, .secondTest => fiberProfileControlExpr_g_third_secondTest
  | .g_p042, .c0 => fiberProfileControlExpr_g_p042_c0
  | .g_p042, .c1 => fiberProfileControlExpr_g_p042_c1
  | .g_p042, .c2 => fiberProfileControlExpr_g_p042_c2
  | .g_p042, .firstTest => fiberProfileControlExpr_g_p042_firstTest
  | .g_p042, .secondTest => fiberProfileControlExpr_g_p042_secondTest
  | .g_p044, .c0 => fiberProfileControlExpr_g_p044_c0
  | .g_p044, .c1 => fiberProfileControlExpr_g_p044_c1
  | .g_p044, .c2 => fiberProfileControlExpr_g_p044_c2
  | .g_p044, .firstTest => fiberProfileControlExpr_g_p044_firstTest
  | .g_p044, .secondTest => fiberProfileControlExpr_g_p044_secondTest
  | .h_third, .c0 => fiberProfileControlExpr_h_third_c0
  | .h_third, .c1 => fiberProfileControlExpr_h_third_c1
  | .h_third, .c2 => fiberProfileControlExpr_h_third_c2
  | .h_third, .firstTest => fiberProfileControlExpr_h_third_firstTest
  | .h_third, .secondTest => fiberProfileControlExpr_h_third_secondTest
  | .h_p038, .c0 => fiberProfileControlExpr_h_p038_c0
  | .h_p038, .c1 => fiberProfileControlExpr_h_p038_c1
  | .h_p038, .c2 => fiberProfileControlExpr_h_p038_c2
  | .h_p038, .firstTest => fiberProfileControlExpr_h_p038_firstTest
  | .h_p038, .secondTest => fiberProfileControlExpr_h_p038_secondTest
  | .e_third, .c0 => fiberProfileControlExpr_e_third_c0
  | .e_third, .c1 => fiberProfileControlExpr_e_third_c1
  | .e_third, .c2 => fiberProfileControlExpr_e_third_c2
  | .e_third, .firstTest => fiberProfileControlExpr_e_third_firstTest
  | .e_third, .secondTest => fiberProfileControlExpr_e_third_secondTest
  | .e_p038, .c0 => fiberProfileControlExpr_e_p038_c0
  | .e_p038, .c1 => fiberProfileControlExpr_e_p038_c1
  | .e_p038, .c2 => fiberProfileControlExpr_e_p038_c2
  | .e_p038, .firstTest => fiberProfileControlExpr_e_p038_firstTest
  | .e_p038, .secondTest => fiberProfileControlExpr_e_p038_secondTest
  | .e_p042, .c0 => fiberProfileControlExpr_e_p042_c0
  | .e_p042, .c1 => fiberProfileControlExpr_e_p042_c1
  | .e_p042, .c2 => fiberProfileControlExpr_e_p042_c2
  | .e_p042, .firstTest => fiberProfileControlExpr_e_p042_firstTest
  | .e_p042, .secondTest => fiberProfileControlExpr_e_p042_secondTest
  | .e_p044, .c0 => fiberProfileControlExpr_e_p044_c0
  | .e_p044, .c1 => fiberProfileControlExpr_e_p044_c1
  | .e_p044, .c2 => fiberProfileControlExpr_e_p044_c2
  | .e_p044, .firstTest => fiberProfileControlExpr_e_p044_firstTest
  | .e_p044, .secondTest => fiberProfileControlExpr_e_p044_secondTest
  | .e_half, .c0 => fiberProfileControlExpr_e_half_c0
  | .e_half, .c1 => fiberProfileControlExpr_e_half_c1
  | .e_half, .c2 => fiberProfileControlExpr_e_half_c2
  | .e_half, .firstTest => fiberProfileControlExpr_e_half_firstTest
  | .e_half, .secondTest => fiberProfileControlExpr_e_half_secondTest
  | .e_p052, .c0 => fiberProfileControlExpr_e_p052_c0
  | .e_p052, .c1 => fiberProfileControlExpr_e_p052_c1
  | .e_p052, .c2 => fiberProfileControlExpr_e_p052_c2
  | .e_p052, .firstTest => fiberProfileControlExpr_e_p052_firstTest
  | .e_p052, .secondTest => fiberProfileControlExpr_e_p052_secondTest
  | .e_p06, .c0 => fiberProfileControlExpr_e_p06_c0
  | .e_p06, .c1 => fiberProfileControlExpr_e_p06_c1
  | .e_p06, .c2 => fiberProfileControlExpr_e_p06_c2
  | .e_p06, .firstTest => fiberProfileControlExpr_e_p06_firstTest
  | .e_p06, .secondTest => fiberProfileControlExpr_e_p06_secondTest

end Erdos993Lean.Analytic.V213
