module

public import Erdos993Lean.BCFG.WholePolynomial

/-! Generic univariate Horner/full-sum and direct mapped-row interfaces.
No packet arithmetic. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

open scoped BigOperators

namespace Uni

theorem evalReal_eq_sum (p : Uni) (x : ℝ) :
    evalReal p x = ∑ i ∈ Finset.range p.length, (p.getD i 0 : ℝ) * x^i := by
  induction p with
  | nil => simp
  | cons a p ih =>
      rw [evalReal_cons, List.length_cons, Finset.sum_range_succ']
      have hzero : (a :: p).getD 0 0 = a := rfl
      have hsucc : ∀ i : Nat, (a :: p).getD (i+1) 0 = p.getD i 0 := by
        intro i
        rfl
      simp only [hzero, hsucc, pow_zero, mul_one]
      have htail :
          (∑ i ∈ Finset.range p.length, (p.getD i 0 : ℝ) * x^(i+1)) =
            x * evalReal p x := by
        rw [ih, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ]
        ring
      rw [htail]
      ring

theorem evalReal_eq_sum_of_length (p : Uni) (n : Nat) (h : p.length = n) (x : ℝ) :
    evalReal p x = ∑ i ∈ Finset.range n, (p.getD i 0 : ℝ) * x^i := by
  rw [evalReal_eq_sum, h]

end Uni

namespace Bi

theorem getD_range_map (n : Nat) (f : Nat → Uni) (i : Nat) (hi : i < n) :
    ((List.range n).map f).getD i [] = f i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem evalReal_range_map (n : Nat) (f : Nat → Uni) (s z : ℝ) :
    evalReal ((List.range n).map f) s z =
      ∑ i ∈ Finset.range n, Uni.evalReal (f i) z * s^i := by
  rw [evalReal_eq_sum, List.length_map, List.length_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [getD_range_map n f i (Finset.mem_range.mp hi)]

end Bi
end Erdos993Lean.BCFG
