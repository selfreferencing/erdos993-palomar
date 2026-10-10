module

public import F4Heavy.Analysis.OrdinaryControlSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem ordinaryControl_bernstein_positive (p : List (List Fraction)) (saved : List Fraction)
    (xl a b : Fraction) (m j : Nat) (v : ℝ)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den)
    (hl : 0 < xl.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hab : fractionValue a < fractionValue b)
    (hv0 : fractionValue a ≤ v) (hv1 : v ≤ fractionValue b)
    (hreconstruct : Fraction.allEq (ordinaryControl p xl m j a b false true) saved = true)
    (hchecks : ∀ c ∈ saved, Fraction.positive c = true) :
    0 < realHorner ((column (parentColumns p xl m) j).map fractionValue) v := by
  let col := column (parentColumns p xl m) j
  have hc := column_den_pos (parentColumns p xl m) j (parentColumns_den_pos p xl m hp hl)
  change Fraction.allEq (bernstein col a b (col.length-1)) saved = true at hreconstruct
  exact bernstein_positive_of_allEq col saved a b (col.length-1) v hc ha hb
    (by omega) hab hv0 hv1 hreconstruct hchecks

end F4Heavy.Analysis
