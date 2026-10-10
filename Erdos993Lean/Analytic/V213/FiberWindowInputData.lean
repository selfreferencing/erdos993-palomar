module

public import Erdos993Lean.Analytic.V213.FiberCornerRows

/-!
Actual F06 window associations. Printed iota identities govern
lookups. Endpoints, rates and means are read through the actual accepted
input interface. C1/C2 have coupled-rate consumers, separately from the
five ordinary class corners.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberWindowInputIdentity where
  | iota0 | iota1 | iota2 | iota3 | iota4 | iota5 | iota44 | iota45 | iota46 | iota47 | iota48 | iota49 | iota50 | iota51 | iota52 | iota53 | iota54

def fiberWindowInput : FiberWindowInputIdentity → FiberInputIdentity
  | .iota0 => .iota_0
  | .iota1 => .iota_1
  | .iota2 => .iota_2
  | .iota3 => .iota_3
  | .iota4 => .iota_4
  | .iota5 => .iota_5
  | .iota44 => .iota_44
  | .iota45 => .iota_45
  | .iota46 => .iota_46
  | .iota47 => .iota_47
  | .iota48 => .iota_48
  | .iota49 => .iota_49
  | .iota50 => .iota_50
  | .iota51 => .iota_51
  | .iota52 => .iota_52
  | .iota53 => .iota_53
  | .iota54 => .iota_54

def fiberWindowInputWindows : FiberWindowInputIdentity → List FiberWindowIdentity
  | .iota0 => [.window1]
  | .iota1 => [.window1]
  | .iota2 => [.window1]
  | .iota3 => [.window2]
  | .iota4 => [.window2]
  | .iota5 => [.window2]
  | .iota44 => [.window3, .window4]
  | .iota45 => [.window3, .window4]
  | .iota46 => [.window3, .window4]
  | .iota47 => [.window5]
  | .iota48 => [.window5]
  | .iota49 => [.window5]
  | .iota50 => [.window6, .window7]
  | .iota51 => [.window6, .window7]
  | .iota52 => [.window6, .window7]
  | .iota53 => [.window8, .window9]
  | .iota54 => [.window10]

def fiberWindowInputCorner : FiberWindowInputIdentity → Option FiberWindowCornerIdentity
  | .iota0 => none
  | .iota1 => none
  | .iota2 => none
  | .iota3 => none
  | .iota4 => none
  | .iota5 => none
  | .iota44 => some .c4
  | .iota45 => some .c4
  | .iota46 => some .c4
  | .iota47 => some .c5
  | .iota48 => some .c5
  | .iota49 => some .c5
  | .iota50 => some .c6
  | .iota51 => some .c6
  | .iota52 => some .c6
  | .iota53 => some .c7
  | .iota54 => some .c8

def fiberWindowInputLog : FiberWindowInputIdentity → FiberCornerLogIdentity
  | .iota0 => .y29_20
  | .iota1 => .y29_20
  | .iota2 => .y29_20
  | .iota3 => .y8_5
  | .iota4 => .y8_5
  | .iota5 => .y8_5
  | .iota44 => .y11_4
  | .iota45 => .y11_4
  | .iota46 => .y11_4
  | .iota47 => .y29_10
  | .iota48 => .y29_10
  | .iota49 => .y29_10
  | .iota50 => .y61_20
  | .iota51 => .y61_20
  | .iota52 => .y61_20
  | .iota53 => .y13_4
  | .iota54 => .y10_3

def fiberWindowInputIdentityAt : ℕ → FiberWindowInputIdentity
  | 0 => .iota0
  | 1 => .iota1
  | 2 => .iota2
  | 3 => .iota3
  | 4 => .iota4
  | 5 => .iota5
  | 6 => .iota44
  | 7 => .iota45
  | 8 => .iota46
  | 9 => .iota47
  | 10 => .iota48
  | 11 => .iota49
  | 12 => .iota50
  | 13 => .iota51
  | 14 => .iota52
  | 15 => .iota53
  | _ => .iota54

def fiberWindowInputIndex : FiberWindowInputIdentity → ℕ
  | .iota0 => 0
  | .iota1 => 1
  | .iota2 => 2
  | .iota3 => 3
  | .iota4 => 4
  | .iota5 => 5
  | .iota44 => 6
  | .iota45 => 7
  | .iota46 => 8
  | .iota47 => 9
  | .iota48 => 10
  | .iota49 => 11
  | .iota50 => 12
  | .iota51 => 13
  | .iota52 => 14
  | .iota53 => 15
  | .iota54 => 16

end Erdos993Lean.Analytic.V213
