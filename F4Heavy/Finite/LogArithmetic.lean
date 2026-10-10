module

public import F4Heavy.Finite.Arithmetic

/-! Exact series arithmetic only. The implication to `Real.log` is not yet
formalized; these checks do not assert an analytic logarithm bound. -/

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Finite
open Fraction

def smallLogSeries (z : Fraction) : Fraction × Fraction :=
  let v := div (sub z one) (add z one)
  let lo := mul (ofInt 2) (sum ((List.range 32).map fun j =>
    div (pow v (2*j+1)) (ofInt (2*j+1))))
  let rem := div (mul (ofInt 2) (pow v 65))
    (mul (ofInt 65) (sub one (mul v v)))
  (lo, add lo rem)

def logSeriesCheck (z lo hi : Fraction) (k : Nat) : Bool :=
  let inverted := lt z one
  let w := if inverted then inv z else z
  let t := div w (ofInt ((2 : Int)^k))
  let (l,h) := smallLogSeries t
  let (l₂,h₂) := smallLogSeries (ofInt 2)
  let a := add l (mul (ofInt k) l₂)
  let b := add h (mul (ofInt k) h₂)
  positive z && le one t && lt t (ofInt 2) &&
    if inverted then eq lo (neg b) && eq hi (neg a)
    else eq lo a && eq hi b

end F4Heavy.Finite
