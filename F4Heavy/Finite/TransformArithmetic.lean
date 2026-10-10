module

public import F4Heavy.Finite.Arithmetic

/-! Exact coefficient reconstruction. Every input is a source rational with an
explicit integer numerator and natural denominator. -/

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Finite
open Fraction

def choose (n k : Nat) : Nat :=
  if k > n then 0 else
    (List.range k).foldl (fun acc i => acc * (n-i) / (i+1)) 1

def shifted (p : List Fraction) (a b : Fraction) : List Fraction :=
  (List.range p.length).map fun k =>
    mul (pow b k) (sum ((List.range (p.length-k)).map fun j =>
      let i := j+k
      mul (p[i]?.getD zero) (mul (ofInt (choose i k)) (pow a (i-k)))))

def bernstein (p : List Fraction) (a b : Fraction) (n : Nat) : List Fraction :=
  let q := shifted p a (sub b a)
  (List.range (n+1)).map fun i =>
    sum ((List.range (min (i+1) q.length)).map fun k =>
      mul (q[k]?.getD zero) ⟨choose i k, choose n k⟩)

def projective (p : List Fraction) : List Fraction :=
  let n := p.length-1
  (List.range p.length).map fun k =>
    sum ((List.range (k+1)).map fun i =>
      mul (p[i]?.getD zero)
        (ofInt (((-1 : Int)^(k-i)) * (choose (n-i) (k-i) : Int))))

def parentColumns (p : List (List Fraction)) (xl : Fraction) (degree : Nat) :
    List (List Fraction) := p.map (fun row => bernstein row xl one degree)

def column (p : List (List Fraction)) (j : Nat) : List Fraction :=
  p.map (fun row => row[j]?.getD zero)

def ordinaryControl (p : List (List Fraction)) (xl : Fraction) (degree j : Nat)
    (a b : Fraction) (useQ : Bool) (activityBernstein : Bool) : List Fraction :=
  let cc := column (parentColumns p xl degree) j
  let pp := if useQ then projective cc else cc
  let lo := if useQ then div a (add one a) else a
  let hi := if useQ then div b (add one b) else b
  if activityBernstein then bernstein pp lo hi (pp.length-1)
  else shifted pp (div (add lo hi) (ofInt 2)) one

def specialControl (p : List (List Fraction)) (xl a b : Fraction) (i : Nat)
    (project : Bool) : List Fraction :=
  let m := (p[0]?.getD []).length-1
  let cc := (List.range (m+1)).map fun j =>
    (bernstein (column p j) a b (p.length-1))[i]?.getD zero
  let bs := bernstein cc xl one m
  if project then bs.zipIdx |>.map fun (c,j) => mul c (ofInt (choose m j))
  else bs

def commonColumns (p : List (List Fraction)) (xl a b : Fraction) (useQ : Bool) :
    List (List Fraction) :=
  let m := (p[0]?.getD []).length-1
  let mat := parentColumns p xl m
  let lo := if useQ then div a (add one a) else a
  let hi := if useQ then div b (add one b) else b
  let center := div (add lo hi) (ofInt 2)
  (List.range (m+1)).map fun j =>
    let cc := (column mat j).map (fun c => mul c (ofInt (choose m j)))
    shifted (if useQ then projective cc else cc) center one

def projectiveParentColumns (p : List (List Fraction)) (xl : Fraction) :
    List (List Fraction) :=
  let m := (p[0]?.getD []).length-1
  let mat := parentColumns p xl m
  (List.range (m+1)).map fun j =>
    projective ((column mat j).map (fun c => mul c (ofInt (choose m j))))

def matrixEq (a b : List (List Fraction)) : Bool :=
  a.length == b.length && (a.zip b).all (fun (x,y) => allEq x y)

def polynomialAdd (a b : List Fraction) : List Fraction :=
  (List.range (max a.length b.length)).map fun i => add (a[i]?.getD zero) (b[i]?.getD zero)

def polynomialMul (a b : List Fraction) : List Fraction :=
  if a.isEmpty || b.isEmpty then [] else
  (List.range (a.length+b.length-1)).map fun k =>
    sum ((List.range (k+1)).map fun i => mul (a[i]?.getD zero) (b[k-i]?.getD zero))

def squareReconstruction (p quot : List Fraction) (center a0 a1 : Fraction) : Bool :=
  let square := [pow center 2, neg (mul (ofInt 2) center), one]
  let affine := [sub a0 (mul center a1), a1]
  allEq p (polynomialAdd affine (polynomialMul square quot)) &&
    eq (evalPoly p center) a0 && eq (evalPoly (derivative p) center) a1

end F4Heavy.Finite
