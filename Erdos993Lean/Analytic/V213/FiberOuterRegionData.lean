module

public import Erdos993Lean.Analytic.V213.FiberOuterStartData

/-!
Accepted F05 universal outer-region constants and all eight class rows.
Exact printed identity is authoritative. Reduced rational data is not
certification; grouped Int/Nat checking and real soundness are separate.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

structure FiberOuterUniversalRow where
  printed : String
  minimum_N : lowMeanFraction
  minimum_t : lowMeanFraction
  skew_lower : lowMeanFraction
  skew_upper : lowMeanFraction
  b_lower : lowMeanFraction
  b_upper : lowMeanFraction
  beta_lower : lowMeanFraction
  beta_upper : lowMeanFraction
  delta_lower : lowMeanFraction
  phi_lower : lowMeanFraction
  rho_lower : lowMeanFraction
  eta : lowMeanFraction
  negative_omega_upper : lowMeanFraction
  v : lowMeanFraction
  f_at_start_upper : lowMeanFraction
  D_star : lowMeanFraction
  C_half : lowMeanFraction
  phi_at_start : lowMeanFraction
  endpoint_gap : lowMeanFraction
  exp_negative_argument : lowMeanFraction
  exp_upper : lowMeanFraction
  exp_upper_next : lowMeanFraction

def fiberOuterUniversal : FiberOuterUniversalRow :=
  ⟨"F05:universal_outer_region:r12:lem20(i)", (26, 1), (3, 5), (1, 4), (1, 2), (0, 1), (2, 5), (0, 1), (1, 1), (5, 3), (2, 5), (1, 3), (12, 13), (23, 18), (79, 90), (7, 15), (251, 2700), (4169, 675), (5173, 10800), (3032, 4215), (8, 25), (25, 33), (41, 45)⟩

inductive FiberOuterClassIdentity where
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8

structure FiberOuterClassRow where
  printed : String
  input_lo : ℕ
  input_hi : ℕ
  skew_lower : lowMeanFraction
  skew_upper : lowMeanFraction
  b : lowMeanFraction
  beta_prime : lowMeanFraction
  tau : lowMeanFraction
  mu_D : lowMeanFraction
  minimum_N : lowMeanFraction
  required_N : lowMeanFraction
  required_skew_lower : lowMeanFraction
  required_skew_upper : lowMeanFraction
  required_tau : lowMeanFraction
  start : Option FiberOuterStartIdentity
  regionPrinted : String

def fiberOuterClassById : FiberOuterClassIdentity → FiberOuterClassRow
  | .c1 => ⟨"F05:class:C1", 0, 2, (3793, 10000), (1, 2), (2, 5), (0, 1), (3, 5), (45, 1), (29, 1), (26, 1), (1, 4), (1, 2), (3, 5), none, "F05:universal_outer_region:r12:lem20(i)"⟩
  | .c2 => ⟨"F05:class:C2", 3, 5, (1, 4), (1897, 5000), (2, 5), (0, 1), (69, 100), (50, 1), (73, 2), (26, 1), (1, 4), (1, 2), (3, 5), none, "F05:universal_outer_region:r12:lem20(i)"⟩
  | .c3 => ⟨"F05:class:C3", 40, 43, (833, 5000), (2309, 10000), (0, 1), (1, 2), (11, 25), (50, 1), (24, 1), (24, 1), (4, 25), (2, 5), (11, 25), some .c3, "F05:start:C3"⟩
  | .c4 => ⟨"F05:class:C4", 44, 46, (2307, 10000), (341, 1250), (3, 20), (3, 10), (21, 50), (40, 1), (94, 5), (18, 1), (9, 40), (2, 5), (21, 50), some .c4, "F05:start:C4"⟩
  | .c5 => ⟨"F05:class:C5", 47, 49, (2727, 10000), (194, 625), (3, 10), (0, 1), (2, 5), (50, 1), (22, 1), (20, 1), (4, 15), (2, 5), (9, 25), some .c5c6, "F05:start:C5,C6"⟩
  | .c6 => ⟨"F05:class:C6", 50, 52, (3103, 10000), (861, 2500), (3, 10), (0, 1), (9, 25), (50, 1), (20, 1), (20, 1), (4, 15), (2, 5), (9, 25), some .c5c6, "F05:start:C5,C6"⟩
  | .c7 => ⟨"F05:class:C7", 53, 53, (1721, 5000), (3847, 10000), (3, 10), (1, 1), (33, 100), (50, 1), (37, 2), (17, 1), (17, 50), (2, 5), (3, 10), some .c7c8, "F05:start:C7,C8"⟩
  | .c8 => ⟨"F05:class:C8", 54, 54, (1923, 5000), (2, 5), (3, 10), (1, 1), (3, 10), (50, 1), (17, 1), (17, 1), (17, 50), (2, 5), (3, 10), some .c7c8, "F05:start:C7,C8"⟩

def fiberOuterClassIdentityAt : ℕ → FiberOuterClassIdentity
  | 0 => .c1
  | 1 => .c2
  | 2 => .c3
  | 3 => .c4
  | 4 => .c5
  | 5 => .c6
  | 6 => .c7
  | _ => .c8

end Erdos993Lean.Analytic.V213
