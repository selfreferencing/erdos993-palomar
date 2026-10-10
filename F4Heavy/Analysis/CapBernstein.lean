module

public import F4Heavy.Analysis.BernsteinSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem cap_bernstein_positive_values (p controls : List Fraction) (a b : Fraction) (n : Nat) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hn : p.length ≤ n+1) (hab : fractionValue a < fractionValue b)
    (hx0 : fractionValue a ≤ x) (hx1 : x ≤ fractionValue b)
    (heq : Fraction.allEq (bernstein p a b n) controls = true)
    (hcheck : ∀ c ∈ controls, 0 < fractionValue c) :
    0 < realHorner (p.map fractionValue) x := by
  apply bernstein_positive_values p a b n x hp ha hb hn hab hx0 hx1
  intro c hc
  have hm : fractionValue c ∈ controls.map fractionValue := by
    rw [← fraction_allEq_sound _ _ heq]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact hcheck d hd

end F4Heavy.Analysis
