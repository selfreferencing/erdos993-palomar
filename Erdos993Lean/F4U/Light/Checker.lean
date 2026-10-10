module

@[expose] public section


/-!
# F4 unified light core: integer-arithmetic kernel checker (TIMING PROTOTYPE)

The soundness proofs are separate modules. This file keeps executable checks in core integer arithmetic.
Every function is structurally recursive (no well-founded recursion) and uses only `Int`/`Nat`/`List`/`Bool`
from core Lean, so the kernel evaluates it with GMP-backed `Nat` literals.

Rules implemented (the F4 note, "Exact finite specification for the light region"; the light source note, Sec. 7-8):
* parent Bernstein control, scaled by the positive integer `C(m,s)`:
    `P_s(x) = sum_{j<=s} C(m-j, s-j) N_j(x) = C(m,s) * C_s(x)`, where `N(x,t) = sum_j N_j(x) t^j`;
* E1/E2 controls in the coordinate `q` (base variable `x = lambda`): `B(q) = (1-q)^n P_s(q/(1-q))`, `n = deg P_s`;
  all other controls: `B = P_s`;
* centred, scaled expansion with `v_c = c/D`, `r = rad/D` (interval midpoint and half-width):
    `G(u) = D^n B((c + rad*u)/D) = sum_k G_k u^k`, so `G_k = D^n e_k r^k > 0`-multiples of the paper's `e_k r^k`;
* norm rule (E1/E2): `199 G_0 - 200 sum_{k>=1} |G_k| > 0`;
* quadratic rule (D/H): with `T = sum_{k>=3} |G_k|`, `a = 200 (G_2 - T)`, `b = 200 G_1`, `c = 199 G_0`:
    `G_0 > 0`, `a - b + c > 0`, `a + b + c > 0`, and if `a > 0 and |b| < 2a` then `b^2 < 4ac`
  (these are `D^n`, `r`-rescalings of `e_0 > 0`, `A* r^2 -+ B* r + C* > 0`, `4 A* C* - B*^2 > 0`);
* the single exception (H, s = 12): Bernstein coefficients of degree `n = deg B` on the whole interval
  `[a, b]`, scaled by `C(n,j)`: `sum_{k<=j} C(n-k, j-k) g_k > 0` for all `j`, where
  `g(v) = D^n B(a + (b-a) v)` with `a = (c-rad)/D`, `b - a = 2 rad/D`.
-/

namespace F4U.Light

/-! ## Dense integer polynomials (ascending coefficient lists) -/

def padd : List Int → List Int → List Int
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

def pneg : List Int → List Int
  | [] => []
  | a :: p => (-a) :: pneg p

def psub : List Int → List Int → List Int
  | [], q => pneg q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a - b) :: psub p q

def pscale (a : Int) : List Int → List Int
  | [] => []
  | b :: p => (a * b) :: pscale a p

/-- remove trailing zero coefficients -/
def dropZ : List Int → List Int
  | [] => []
  | a :: p => if a = 0 then dropZ p else a :: p

def trimZ : List Int → List Int
  | [] => []
  | a :: p =>
    let t := trimZ p
    if a = 0 ∧ t = [] then [] else a :: t

/-! ## Small binomials -/

def descFact (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n - k) * descFact n k

def fact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * fact k

def binom (n k : Nat) : Nat := descFact n k / fact k

/-! ## Step 1: parent Bernstein control (scaled by `C(m,s)`) -/

def parentGo (m s : Nat) : Nat → List (List Int) → List Int → List Int
  | _, [], acc => acc
  | j, r :: rs, acc =>
      if j ≤ s then parentGo m s (j + 1) rs (padd acc (pscale (Int.ofNat (binom (m - j) (s - j))) r))
      else acc

def parent (m s : Nat) (rows : List (List Int)) : List Int := parentGo m s 0 rows []

/-! ## Step 2: `(1-q)^n C(q/(1-q))`, `n = deg C`, by the recursion `H_k = (1-q) H_{k-1} + b_k q^k` -/

def toQGo : List Int → List Int → List Int
  | [], H => H
  | b :: bs, H => toQGo bs (psub (H ++ [b]) (0 :: H))

def toQ (p : List Int) : List Int := toQGo (trimZ p) []

/-! ## Step 3: `D^n B((c + r u)/D)` by homogeneous Horner, `n = length B - 1` -/

/-- `(c + r u) * G + b`, second half -/
def mlGo (c r : Int) : Int → List Int → List Int
  | prev, [] => [r * prev]
  | prev, g :: gs => (c * g + r * prev) :: mlGo c r g gs

/-- `(c + r u) * G + b` -/
def mulLinAdd (c r b : Int) : List Int → List Int
  | [] => [b]
  | g :: gs => (c * g + b) :: mlGo c r g gs

/-- input: `B` reversed (top coefficient first), running power `P = D^(n-k)` -/
def hornerGo (c r D : Int) : List Int → Int → List Int → List Int
  | [], _, G => G
  | b :: bs, P, G => hornerGo c r D bs (P * D) (mulLinAdd c r (b * P) G)

def shiftScale (c r D : Int) (B : List Int) : List Int := hornerGo c r D B.reverse 1 []

/-! ## Step 4: the sign rules -/

def absI (a : Int) : Int := if a < 0 then -a else a

def sumAbs : List Int → Int
  | [] => 0
  | a :: p => absI a + sumAbs p

/-- norm rule `199 G_0 > 200 sum_{k>=1} |G_k|` -/
def normOK : List Int → Bool
  | [] => false
  | g0 :: rest => decide (200 * sumAbs rest < 199 * g0)

/-- quadratic lower-bound rule -/
def quadOK (G : List Int) : Bool :=
  let g0 := G.getD 0 0
  let g1 := G.getD 1 0
  let g2 := G.getD 2 0
  let T := sumAbs (G.drop 3)
  let a := 200 * (g2 - T)
  let b := 200 * g1
  let c := 199 * g0
  decide (0 < g0) && decide (0 < a - b + c) && decide (0 < a + b + c) &&
    (!(decide (0 < a) && decide (absI b < 2 * a)) || decide (b * b < 4 * a * c))

/-- `C(n,j) d_j = sum_{k<=j} C(n-k, j-k) g_k` -/
def bernGo (n j : Nat) : Nat → List Int → Int
  | _, [] => 0
  | k, g :: gs => if k ≤ j then Int.ofNat (binom (n - k) (j - k)) * g + bernGo n j (k + 1) gs else 0

def bernAll (n : Nat) (G : List Int) : Nat → Bool
  | 0 => decide (0 < bernGo n 0 0 G)
  | j + 1 => decide (0 < bernGo n (j + 1) 0 G) && bernAll n G j

def bernOK (G : List Int) : Bool := bernAll (G.length - 1) G (G.length - 1)

/-! ## Records -/

inductive Rule where
  | norm
  | quad
  | bern

structure Ctl where
  s : Nat
  rule : Rule

/-- one rational function record -/
structure Fn where
  /-- parent (t-) degree -/
  m : Nat
  /-- E1/E2 control in the coordinate q: apply `(1-q)^n C(q/(1-q))` -/
  toQ : Bool
  /-- interval `[a1/a2, b1/b2]` in the activity coordinate -/
  a1 : Nat
  a2 : Nat
  b1 : Nat
  b2 : Nat
  /-- midpoint `c/D`, half-width `rad/D` -/
  c : Nat
  rad : Nat
  D : Nat
  /-- `rows[j]` = coefficients (ascending powers of x) of the `t^j` part of the primitive numerator -/
  rows : List (List Int)
  ctls : List Ctl

/-- the centre/radius data really are the midpoint and half-width of the interval -/
def geomOK (F : Fn) : Bool :=
  decide (0 < F.a2) && decide (0 < F.b2) &&
  (!F.toQ || decide (F.b1 < F.b2)) &&
  decide (0 < F.D) && decide (0 < F.rad) && decide (F.a1 * F.b2 < F.b1 * F.a2) &&
  decide (2 * F.c * F.a2 * F.b2 = F.D * (F.a1 * F.b2 + F.b1 * F.a2)) &&
  decide (2 * F.rad * F.a2 * F.b2 = F.D * (F.b1 * F.a2 - F.a1 * F.b2))

def control (F : Fn) (s : Nat) : List Int :=
  let P := parent F.m s F.rows
  if F.toQ then toQ P else P

def checkCtl (F : Fn) (C : Ctl) : Bool :=
  match C.rule with
  | .norm => normOK (shiftScale (Int.ofNat F.c) (Int.ofNat F.rad) (Int.ofNat F.D) (control F C.s))
  | .quad => quadOK (shiftScale (Int.ofNat F.c) (Int.ofNat F.rad) (Int.ofNat F.D) (control F C.s))
  | .bern => bernOK (shiftScale (Int.ofNat F.c - Int.ofNat F.rad) (2 * Int.ofNat F.rad) (Int.ofNat F.D)
                        (trimZ (control F C.s)))

def shapeOK (F : Fn) : Bool :=
  decide (F.rows.length ≤ F.m + 1) && decide (F.ctls.map Ctl.s = List.range (F.m + 1))

def checkFn (F : Fn) : Bool := geomOK F && shapeOK F && F.ctls.all (checkCtl F)

end F4U.Light
