module

public import Erdos993Lean.Analytic.V213.FiberProfileLineBounds

/-!
All twelve consecutive printed F10 profile-control pairs, with their
actual accepted F09 closed root-line piece. Data only; separate Int/Nat
checks and real consumers establish all geometry and chord conclusions.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberProfileChordIdentity where
  | a_third_p042 | a_p042_half | a_half_p06 | b_third_p042 | b_p042_half | b_half_p06 | d_third_p042 | d_p042_half | d_half_p052 | g_third_p042 | g_p042_p044 | h_third_p038

structure FiberProfileChordRow where
  profile : FiberRationalProfileIdentity
  left : FiberProfileControlIdentity
  right : FiberProfileControlIdentity
  piece : FiberRootLineIdentity

def fiberProfileChordById : FiberProfileChordIdentity → FiberProfileChordRow
  | .a_third_p042 => ⟨.a, .a_third, .a_p042, .third_042⟩
  | .a_p042_half => ⟨.a, .a_p042, .a_half, .p042_half⟩
  | .a_half_p06 => ⟨.a, .a_half, .a_p06, .half_p06⟩
  | .b_third_p042 => ⟨.b, .b_third, .b_p042, .third_042⟩
  | .b_p042_half => ⟨.b, .b_p042, .b_half, .p042_half⟩
  | .b_half_p06 => ⟨.b, .b_half, .b_p06, .half_p06⟩
  | .d_third_p042 => ⟨.d, .d_third, .d_p042, .third_042⟩
  | .d_p042_half => ⟨.d, .d_p042, .d_half, .p042_half⟩
  | .d_half_p052 => ⟨.d, .d_half, .d_p052, .half_p06⟩
  | .g_third_p042 => ⟨.g, .g_third, .g_p042, .third_042⟩
  | .g_p042_p044 => ⟨.g, .g_p042, .g_p044, .p042_half⟩
  | .h_third_p038 => ⟨.h, .h_third, .h_p038, .third_042⟩

def fiberProfileChordPrinted : FiberProfileChordIdentity → String
  | .a_third_p042 => "F10:A:consecutive=[1/3,21/50]"
  | .a_p042_half => "F10:A:consecutive=[21/50,1/2]"
  | .a_half_p06 => "F10:A:consecutive=[1/2,3/5]"
  | .b_third_p042 => "F10:B:consecutive=[1/3,21/50]"
  | .b_p042_half => "F10:B:consecutive=[21/50,1/2]"
  | .b_half_p06 => "F10:B:consecutive=[1/2,3/5]"
  | .d_third_p042 => "F10:D:consecutive=[1/3,21/50]"
  | .d_p042_half => "F10:D:consecutive=[21/50,1/2]"
  | .d_half_p052 => "F10:D:consecutive=[1/2,13/25]"
  | .g_third_p042 => "F10:G:consecutive=[1/3,21/50]"
  | .g_p042_p044 => "F10:G:consecutive=[21/50,11/25]"
  | .h_third_p038 => "F10:H:consecutive=[1/3,19/50]"

def fiberProfileChordIdentityAt : ℕ → FiberProfileChordIdentity
  | 0 => .a_third_p042
  | 1 => .a_p042_half
  | 2 => .a_half_p06
  | 3 => .b_third_p042
  | 4 => .b_p042_half
  | 5 => .b_half_p06
  | 6 => .d_third_p042
  | 7 => .d_p042_half
  | 8 => .d_half_p052
  | 9 => .g_third_p042
  | 10 => .g_p042_p044
  | _ => .h_third_p038

def fiberProfileChordIndex : FiberProfileChordIdentity → ℕ
  | .a_third_p042 => 0
  | .a_p042_half => 1
  | .a_half_p06 => 2
  | .b_third_p042 => 3
  | .b_p042_half => 4
  | .b_half_p06 => 5
  | .d_third_p042 => 6
  | .d_p042_half => 7
  | .d_half_p052 => 8
  | .g_third_p042 => 9
  | .g_p042_p044 => 10
  | .h_third_p038 => 11

end Erdos993Lean.Analytic.V213
