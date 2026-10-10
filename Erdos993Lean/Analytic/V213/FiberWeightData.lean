module

public import Erdos993Lean.Analytic.V213.FiberProfileChordData

/-!
All eight accepted F11 printed weights with exact class spans, profile
association, dyadic exponent lists and both closed guard endpoints.
Data only; actual rate, original-input and price consumers are separate.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberWeightIdentity where
  | a | b | c | d | e | f | g | h

structure FiberWeightRow where
  printed : String
  profile : FiberRationalProfileIdentity
  inputLo : ℕ
  inputHi : ℕ
  mu_w : lowMeanFraction
  ell_w : lowMeanFraction
  L_w : lowMeanFraction
  eta_w : lowMeanFraction
  guard_lo : lowMeanFraction
  guard_hi : lowMeanFraction
  chord_epsilon : Option lowMeanFraction
  guard_gap : lowMeanFraction
  chordNs : List ℕ

def fiberWeightById : FiberWeightIdentity → FiberWeightRow
  | .a => ⟨"F11:A", .a, 6, 9, (23, 1), (1801, 5000), (328, 625), (3, 50), (7, 23), (3, 5), some (1, 100), (1, 100000), [5, 4, 2]⟩
  | .b => ⟨"F11:B", .b, 10, 29, (19, 1), (439, 1000), (14409, 20000), (3, 40), (1, 3), (3, 5), some (1, 1000), (1, 100000), [4, 2, 1]⟩
  | .c => ⟨"F11:C", .b, 30, 36, (20, 1), (903, 2000), (40547, 50000), (1, 8), (1, 3), (3, 5), some (1, 100), (1, 100000), [3, 1, 0]⟩
  | .d => ⟨"F11:D", .d, 37, 37, (26, 1), (91, 200), (83291, 100000), (1, 10), (1, 3), (13, 25), some (1, 100), (1, 100000), [2, 1, 1]⟩
  | .e => ⟨"F11:E", .d, 38, 38, (32, 1), (4599, 10000), (42721, 50000), (1, 10), (1, 3), (13, 25), none, (1, 100000), []⟩
  | .f => ⟨"F11:F", .d, 39, 39, (36, 1), (289, 625), (87547, 100000), (1, 10), (1, 3), (13, 25), some (1, 1000), (1, 100000), [2, 1, 0]⟩
  | .g => ⟨"F11:G", .g, 40, 43, (50, 1), (903, 2000), (2986, 3125), (3, 25), (1, 3), (11, 25), some (1, 100), (1, 100000), [1, 2]⟩
  | .h => ⟨"F11:H", .h, 44, 46, (40, 1), (294, 625), (101161, 100000), (17, 500), (1, 3), (19, 50), some (1, 1000), (1, 100000), [4]⟩

def fiberWeightPrinted : FiberWeightIdentity → String
  | .a => "F11:A"
  | .b => "F11:B"
  | .c => "F11:C"
  | .d => "F11:D"
  | .e => "F11:E"
  | .f => "F11:F"
  | .g => "F11:G"
  | .h => "F11:H"

def fiberWeightIdentityAt : ℕ → FiberWeightIdentity
  | 0 => .a
  | 1 => .b
  | 2 => .c
  | 3 => .d
  | 4 => .e
  | 5 => .f
  | 6 => .g
  | _ => .h

def fiberWeightIndex : FiberWeightIdentity → ℕ
  | .a => 0
  | .b => 1
  | .c => 2
  | .d => 3
  | .e => 4
  | .f => 5
  | .g => 6
  | .h => 7

end Erdos993Lean.Analytic.V213
