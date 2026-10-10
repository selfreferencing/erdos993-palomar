module

public import Erdos993Lean.BCFG.Bivariate

/-!
Bridge from bounded source evaluation to the full dense polynomial.
This proof consumes a list-length hypothesis; it does not identify a Lean
literal with an external JSON file. No packet coefficient arithmetic occurs.

-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

open scoped BigOperators

namespace Bi

/-- Horner evaluation of every outer coefficient equals its full finite sum. -/
theorem evalReal_eq_sum (p : Bi) (lambda y : ℝ) :
    evalReal p lambda y =
      ∑ i ∈ Finset.range p.length, Uni.evalReal (p.getD i []) y * lambda^i := by
  induction p with
  | nil => simp
  | cons a p ih =>
      rw [evalReal_cons, List.length_cons, Finset.sum_range_succ']
      have hzero : (a :: p).getD 0 [] = a := rfl
      have hsucc : ∀ i : Nat, (a :: p).getD (i+1) [] = p.getD i [] := by
        intro i
        rfl
      simp only [hzero, hsucc, pow_zero, mul_one]
      have htail :
          (∑ i ∈ Finset.range p.length, Uni.evalReal (p.getD i []) y * lambda^(i+1)) =
            lambda * evalReal p lambda y := by
        rw [ih, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ]
        ring
      rw [htail]
      ring

/-- The checked row count closes the bounded-to-entire evaluation bridge. -/
theorem sourceEval_eq_evalReal (N : Nat) (p : Bi) (hp : p.length = N+1)
    (lambda y : ℝ) :
    sourceEval N p lambda y = evalReal p lambda y := by
  rw [evalReal_eq_sum, hp]
  rfl

end Bi
end Erdos993Lean.BCFG
