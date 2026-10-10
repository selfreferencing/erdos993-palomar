module

public import Init

/-!
Integer arithmetic for the finite certificates. A fraction is an explicit integer
numerator and natural denominator; no `Rat`, floating point or native decision
procedure is used. All comparisons reject zero denominators. The generated
theorems check the Boolean predicates separately with `decide +kernel`.

This module is a computation layer. Connecting its predicates to real-valued
analytic statements is a subsequent proof obligation, not asserted here.
-/

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

structure Fraction where
  num : Int
  den : Nat
  deriving Repr, DecidableEq

namespace Fraction

def ofInt (n : Int) : Fraction := ⟨n, 1⟩
def zero : Fraction := ofInt 0
def one : Fraction := ofInt 1

def normalize (n : Int) (d : Nat) : Fraction :=
  let g := n.natAbs.gcd d
  ⟨n / (g : Int), d / g⟩

def add (a b : Fraction) : Fraction :=
  let g := a.den.gcd b.den
  let ad := a.den / g
  let bd := b.den / g
  normalize (a.num * (bd : Int) + b.num * (ad : Int)) (ad * b.den)

def neg (a : Fraction) : Fraction := ⟨-a.num, a.den⟩
def sub (a b : Fraction) : Fraction := add a (neg b)
def mul (a b : Fraction) : Fraction :=
  normalize (a.num * b.num) (a.den * b.den)
def inv (a : Fraction) : Fraction :=
  ⟨(if a.num < 0 then -(a.den : Int) else (a.den : Int)), a.num.natAbs⟩
def div (a b : Fraction) : Fraction := mul a (inv b)
def abs (a : Fraction) : Fraction := ⟨a.num.natAbs, a.den⟩
def pow (a : Fraction) (n : Nat) : Fraction := ⟨a.num ^ n, a.den ^ n⟩

def eq (a b : Fraction) : Bool :=
  a.den > 0 && b.den > 0 && a.num * (b.den : Int) == b.num * (a.den : Int)
def lt (a b : Fraction) : Bool :=
  a.den > 0 && b.den > 0 && a.num * (b.den : Int) < b.num * (a.den : Int)
def le (a b : Fraction) : Bool :=
  a.den > 0 && b.den > 0 && a.num * (b.den : Int) ≤ b.num * (a.den : Int)
def positive (a : Fraction) : Bool := a.den > 0 && a.num > 0
def sum (xs : List Fraction) : Fraction := xs.foldl add zero
def allEq (xs ys : List Fraction) : Bool :=
  xs.length == ys.length && (xs.zip ys).all (fun (a,b) => eq a b)

def minimum (xs : List Fraction) : Fraction :=
  match xs with
  | [] => zero
  | a :: rest => rest.foldl (fun b c => if lt c b then c else b) a
def maximum (xs : List Fraction) : Fraction :=
  match xs with
  | [] => zero
  | a :: rest => rest.foldl (fun b c => if lt b c then c else b) a

end Fraction

open Fraction

def tailNorm (e : List Fraction) (r : Fraction) (start : Nat) : Fraction :=
  sum ((e.drop start).zipIdx start |>.map fun (a,k) => mul (abs a) (pow r (k-start)))

def normMargin (e : List Fraction) (r : Fraction) : Fraction :=
  sub (mul ⟨199,200⟩ (e[0]?.getD zero)) (mul r (tailNorm e r 1))

def quadraticOperands (e : List Fraction) (r : Fraction) : Fraction × Fraction × Fraction :=
  (sub (e[2]?.getD zero) (mul r (tailNorm e r 3)),
   e[1]?.getD zero, mul ⟨199,200⟩ (e[0]?.getD zero))

def quadraticCheck (e : List Fraction) (r : Fraction) : Bool :=
  let (a,b,c) := quadraticOperands e r
  let ar := mul a (pow r 2)
  let br := mul b r
  let interior := positive a && lt (abs b) (mul (ofInt 2) (mul a r))
  positive (e[0]?.getD zero) && positive (add (sub ar br) c) &&
    positive (add (add ar br) c) &&
    (!interior || positive (sub (mul (ofInt 4) (mul a c)) (pow b 2)))

def evalPoly (p : List Fraction) (x : Fraction) : Fraction :=
  p.foldr (fun a z => add a (mul x z)) zero

def derivative (p : List Fraction) : List Fraction :=
  (p.drop 1).zipIdx 1 |>.map fun (a,k) => mul (ofInt k) a

def squareDiscriminant (quot : List Fraction) (a0 a1 : Fraction) : Fraction :=
  sub (mul (ofInt 4) (mul (quot[0]?.getD zero) a0)) (pow a1 2)

def squareExists (p quot : List Fraction) (center : Fraction) : Bool :=
  quot.all positive && positive (squareDiscriminant quot
    (evalPoly p center) (evalPoly (derivative p) center))

def lowerColumn (col : List Fraction) (r : Fraction) : Fraction :=
  sub (col[0]?.getD zero) (mul r (tailNorm col r 1))

def primitiveLowerCheck (cols : List (List Fraction)) (r scale : Fraction)
    (p : List Fraction) : Bool :=
  positive scale && allEq (p.map (mul scale)) (cols.map (fun c => lowerColumn c r))

structure Term where
  v : Nat
  x : Nat
  c : Fraction
  deriving Repr, DecidableEq

abbrev Polynomial := List Term

def termBefore (a b : Term) : Bool := a.v < b.v || (a.v == b.v && a.x < b.x)

def insertTerm (t : Term) : Polynomial → Polynomial
  | [] => if t.c.num == 0 then [] else [t]
  | a :: rest =>
    if t.c.num == 0 then a :: rest
    else if t.v == a.v && t.x == a.x then
      let s := add t.c a.c
      if s.num == 0 then rest else { a with c := s } :: rest
    else if termBefore t a then t :: a :: rest
    else a :: insertTerm t rest

def mergeTerms : Nat → Polynomial → Polynomial → Polynomial
  | _, [], b => b
  | _, a, [] => a
  | 0, _, _ => []
  | fuel+1, a :: aa, b :: bb =>
    if a.v == b.v && a.x == b.x then
      let c := add a.c b.c
      if c.num == 0 then mergeTerms fuel aa bb
      else { a with c := c } :: mergeTerms fuel aa bb
    else if termBefore a b then a :: mergeTerms fuel aa (b :: bb)
    else b :: mergeTerms fuel (a :: aa) bb

def polyAdd (a b : Polynomial) : Polynomial := mergeTerms (a.length+b.length) a b
def polyMul (a b : Polynomial) : Polynomial :=
  -- Put the shorter factor outside: each term causes one linear merge.
  let (small, large) := if a.length ≤ b.length then (a,b) else (b,a)
  small.foldl (fun z s => polyAdd z (large.filterMap fun t =>
    let c := mul s.c t.c
    if c.num == 0 then none else some ⟨s.v+t.v, s.x+t.x, c⟩)) []
def polyPow (p : Polynomial) : Nat → Polynomial
  | 0 => [⟨0,0,one⟩]
  | n+1 => polyMul p (polyPow p n)
def polyEq (a b : Polynomial) : Bool :=
  a.length == b.length && (a.zip b).all (fun (s,t) =>
    s.v == t.v && s.x == t.x && eq s.c t.c)
def polyEval (p : Polynomial) (v x : Fraction) : Fraction :=
  -- Evaluate over one explicit common denominator. Repeated Fraction.add on
  -- these large integer polynomials retains excessive kernel reduction data.
  let dv := p.foldl (fun z t => max z t.v) 0
  let dx := p.foldl (fun z t => max z t.x) 0
  let dc := p.foldl (fun z t => z.lcm t.c.den) 1
  let num := p.foldl (fun z t => z + t.c.num * (dc / t.c.den : Nat) *
    v.num ^ t.v * (v.den : Int) ^ (dv-t.v) *
    x.num ^ t.x * (x.den : Int) ^ (dx-t.x)) 0
  ⟨num, dc * v.den ^ dv * x.den ^ dx⟩
def polyTimes (p f : Polynomial) : Nat → Polynomial
  | 0 => p
  | n+1 => polyTimes (polyMul p f) f n

def factorCheck (p : Polynomial) (c : Fraction) (fs : List (Polynomial × Nat)) : Bool :=
  let product := fs.foldl (fun z (f,n) => polyTimes z f n) [⟨0,0,one⟩]
  polyEq p (product.map fun t => { t with c := mul c t.c })

-- Small multiplication proofs can be composed without asking one kernel
-- reduction to retain the entire expanded product at once.
inductive MultiplySteps (f : Polynomial) : Nat → Polynomial → Polynomial → Prop where
  | zero (p : Polynomial) : MultiplySteps f 0 p p
  | succ {n : Nat} {p q r : Polynomial} :
      polyMul p f = q → MultiplySteps f n q r → MultiplySteps f (n+1) p r

theorem MultiplySteps.sound {f p r : Polynomial} {n : Nat}
    (h : MultiplySteps f n p r) : polyTimes p f n = r := by
  induction h with
  | zero => rfl
  | succ step rest ih => simp only [polyTimes, step, ih]

inductive FactorSteps : List (Polynomial × Nat) → Polynomial → Polynomial → Prop where
  | nil (p : Polynomial) : FactorSteps [] p p
  | cons {f p q r : Polynomial} {n : Nat} {fs : List (Polynomial × Nat)} :
      MultiplySteps f n p q → FactorSteps fs q r → FactorSteps ((f,n)::fs) p r

theorem FactorSteps.sound {fs : List (Polynomial × Nat)} {p r : Polynomial}
    (h : FactorSteps fs p r) : fs.foldl (fun z (f,n) => polyTimes z f n) p = r := by
  induction h with
  | nil => rfl
  | cons steps rest ih => simp only [List.foldl, steps.sound, ih]

theorem factorCheck_of_steps {p r : Polynomial} {c : Fraction}
    {fs : List (Polynomial × Nat)} (h : FactorSteps fs [⟨0,0,one⟩] r)
    (last : polyEq p (r.map fun t => { t with c := mul c t.c }) = true) :
    factorCheck p c fs = true := by
  unfold factorCheck
  rw [h.sound]
  exact last

end F4Heavy.Finite
