module

public import Std

/-!
Exact integer arithmetic for the ORIGINAL frozen Section 6 of version 2.10 of the manuscript.
Source: Section 6 and the Appendix tables of version 2.10 of the manuscript.
No simplifications, graph enumeration, native evaluation, or new axioms.
The graph interpretation and
the bridge from `bin` to Mathlib's `Nat.choose` are deliberately separate.
-/

@[expose] public section

namespace Erdos993Lean.Section6V210

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Falling factorial; zero automatically when the lower index exceeds n. -/
def falling (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => falling n k * (n - k)

/-- Kernel-friendly quotient, matching Fiber.Cert.bin's mathematical formula. -/
def bin (n k : Nat) : Nat := falling n k / fact k

/-- The paper's zero convention at negative lower indices is explicit. -/
def binZ (n : Nat) (k : Int) : Int :=
  if k < 0 then 0 else Int.ofNat (bin n k.toNat)

def catalan (j : Nat) : Int := Int.ofNat (bin (2*j) j / (j+1))

/-- One common scale for all printed rational entries and line normalizers. -/
def scale : Int := 27720

def scaled (num : Int) (den : Nat) : Int := num * (scale / Int.ofNat den)
def denominatorOK (den : Nat) : Bool := decide (0 < den ∧ scale % Int.ofNat den = 0)

def sumI (xs : List Int) : Int := xs.foldl (fun a b => a+b) 0
def levels (lo hi : Nat) : List Nat := (List.range (hi+1-lo)).map (fun j => lo+j)

structure Triple where
  n : Nat
  a : Nat
  k : Nat
  deriving BEq, DecidableEq, Repr

def mkTriple (a c k : Nat) : Triple := ⟨a+c,a,k⟩

structure Family where
  a : Nat
  k : Nat
  wn : Nat
  wd : Nat
  lo : Nat
  hi : Nat
  tangents : List Nat
  deriving Repr

/-- Table flx:tab:families, in printed row order. -/
def families : List Family :=
  [⟨8,4,1,2,4,4,[5,2]⟩,
   ⟨9,5,1,2,6,7,[7,5,2]⟩,
   ⟨10,5,1,2,5,6,[8,4]⟩,
   ⟨10,6,1,2,9,10,[8,7,5,2]⟩,
   ⟨11,6,1,2,6,9,[9,7,4]⟩,
   ⟨12,6,1,2,5,8,[10,7]⟩,
   ⟨12,7,1,2,9,11,[10,9,7,4]⟩,
   ⟨12,7,2,3,12,12,[11,9,8,6,3]⟩,
   ⟨13,7,1,2,6,10,[11,9,7]⟩,
   ⟨14,7,1,2,6,6,[11,8,6]⟩,
   ⟨14,8,1,2,9,10,[12,10,8,5]⟩,
   ⟨15,8,1,2,6,9,[13,10,7]⟩,
   ⟨16,8,1,2,7,7,[13,10,8]⟩,
   ⟨17,9,1,2,6,7,[14,10]⟩,
   ⟨18,9,1,2,6,6,[15,11]⟩]

def family (row : Nat) : Family :=
  families[row-1]?.getD ⟨0,0,0,1,0,0,[]⟩

def familyTriples : List Triple := families.flatMap fun r =>
  (levels r.lo r.hi).map fun c => mkTriple r.a c r.k

/-- Proposition flx:prop:catalan: one exceptional P1 plus seven P3 triples. -/
def catalanTriples : List Triple :=
  [⟨24,15,7⟩, ⟨24,13,7⟩, ⟨22,16,8⟩, ⟨24,16,8⟩,
   ⟨21,14,7⟩, ⟨22,14,7⟩, ⟨23,14,7⟩, ⟨24,14,7⟩]

def g (wn wd : Nat) (j : Int) (m : Nat) : Int :=
  (scale / Int.ofNat wd) *
    (Int.ofNat wd * binZ m j - Int.ofNat wn * binZ m (j-1) -
      (Int.ofNat wd - Int.ofNat wn) * binZ m (j+1))

def horizontal (j : Nat) : Int :=
  match j with
  | 1 | 2 | 3 => scaled (-1) 2
  | 4 => -scale
  | 5 => -2*scale
  | 6 => -4*scale
  | _ => 0

/-- (beta_h, q_h), each multiplied by scale. -/
def line (r : Family) (h : Nat) : Int × Int :=
  if h = 0 then (0,0)
  else if h ≤ r.tangents.length then
    let t := r.tangents[h-1]?.getD 0
    let j := Int.ofNat r.k - Int.ofNat h
    let q := g r.wn r.wd (j-1) (t-1)
    (g r.wn r.wd j t - q * Int.ofNat t, q)
  else if h < r.k then
    if 2*r.wn = r.wd then
      (min (horizontal (r.k-h)) (g r.wn r.wd (Int.ofNat r.k-Int.ofNat h) (r.a-h)),0)
    else (scaled (-2) 3,0)
  else if h = r.k then
    (scale - scaled (Int.ofNat (r.wd-r.wn)) r.wd * Int.ofNat (r.a-r.k),0)
  else if h = r.k+1 then (-(scaled (Int.ofNat (r.wd-r.wn)) r.wd),0)
  else (0,0)

def pSharp (r : Family) (h : Nat) : Int :=
  (line r h).1 + (line r h).2 * (Int.ofNat r.a - Int.ofNat h)

def pTilde (r : Family) (h : Nat) : Int :=
  let p := pSharp r h
  if p < 0 then p / Int.ofNat (bin h 2) else p

def lineDivisionsOK (r : Family) : Bool :=
  denominatorOK r.wd && (levels 2 (r.k+1)).all (fun h =>
    decide (pSharp r h < 0 → pSharp r h % Int.ofNat (bin h 2) = 0))

/-- Both affine coefficients are represented exactly at the common scale. -/
def coeffA (r : Family) (c : Nat) : Int :=
  g r.wn r.wd (Int.ofNat r.k) r.a +
  sumI ((levels 1 (r.k+1)).map fun h =>
    (line r h).1 * Int.ofNat (bin c h) +
    (line r h).2 * (Int.ofNat r.a-Int.ofNat h) * Int.ofNat (bin (c-1) h))

def coeffB (r : Family) (c : Nat) : Int :=
  (line r 1).2 + sumI ((levels 2 (r.k+1)).map fun h =>
    (line r h).2 * Int.ofNat (bin (c-2) (h-1)) -
    pTilde r h * Int.ofNat (bin (c-2) (h-2)))

def difference (f : Nat → Int) : Nat → Nat → Int
  | 0,c => f c
  | r+1,c => difference f r (c+1) - difference f r c

def rising (a c k : Nat) : Int :=
  binZ a (Int.ofNat k) - binZ a (Int.ofNat k-1) -
  sumI ((levels 1 (min c (k-1))).map fun h =>
    Int.ofNat (bin c h) * catalan (k-1-h))

end Erdos993Lean.Section6V210
