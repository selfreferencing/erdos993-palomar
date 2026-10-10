module

public import Erdos993Lean.BCFG.Bivariate

/-!
Optional computational alternative: build norm rows directly rather than
adding monomial tensors. The old fromNorm is preserved and its real semantics
are proved equal. Adopting the alternative check would require an explicitly
reviewed certificate-consumer adaptation; it is not silently substituted.

-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

open scoped BigOperators

namespace Bi

/-- Direct list of the N+1 supplied Bernstein rows. -/
def fromNormRows (N M : Nat) (A : Bi) : Bi :=
  (List.range (N+1)).map (fun i => Uni.bernVector M (A.getD i []))

theorem fromNormRows_length (N M : Nat) (A : Bi) :
    (fromNormRows N M A).length = N+1 := by
  simp [fromNormRows]

private theorem evalReal_append (p q : Bi) (s z : ℝ) :
    evalReal (p ++ q) s z = evalReal p s z + s^p.length * evalReal q s z := by
  induction p with
  | nil => simp
  | cons a p ih =>
      simp only [List.cons_append, evalReal_cons, List.length_cons, ih, pow_succ]
      ring

private theorem evalReal_map_range (f : Nat → Uni) (n : Nat) (s z : ℝ) :
    evalReal ((List.range n).map f) s z =
      ∑ i ∈ Finset.range n, Uni.evalReal (f i) z * s^i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, evalReal_append, Finset.sum_range_succ, ih]
      simp only [List.map_cons, List.map_nil, List.length_map, List.length_range,
        evalReal_cons, evalReal_nil, mul_zero, add_zero]
      ring

/-- Same real norm expansion, now read from a direct outer coefficient list. -/
theorem fromNormRows_sound (N M : Nat) (A : Bi) (s z : ℝ) :
    evalReal (fromNormRows N M A) s z =
      normEval N M (fun i j => ((A.getD i []).getD j 0 : ℝ)) s z := by
  unfold fromNormRows
  rw [evalReal_map_range, normEval_eq_double_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Uni.evalReal_bernVector, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  unfold bernsteinBasis
  ring

theorem fromNormRows_semantics (N M : Nat) (A : Bi) (s z : ℝ) :
    evalReal (fromNormRows N M A) s z = evalReal (fromNorm N M A) s z := by
  rw [fromNormRows_sound, fromNorm_sound]

/-- Alternate check has the identical expansion conclusion. This theorem is
available if the finite check input is changed accordingly. -/
theorem checked_expansion_rows (N M : Nat) (p A : Bi) (qc rq a b : Rat)
    (hcheck : checkEq (normalized N p qc rq a b) (fromNormRows N M A) = true)
    (s z q : ℝ) (hqdef : q = (qc : ℝ)+(rq : ℝ)*s) (hq : q ≠ 1) :
    (1-q)^N * sourceEval N p (q/(1-q)) ((a : ℝ)+(b : ℝ)*z) =
      normEval N M (fun i j => ((A.getD i []).getD j 0 : ℝ)) s z := by
  calc
    (1-q)^N * sourceEval N p (q/(1-q)) ((a : ℝ)+(b : ℝ)*z) =
        evalReal (normalized N p qc rq a b) s z :=
      (normalized_sound N p qc rq a b s z q hqdef hq).symm
    _ = evalReal (fromNormRows N M A) s z := checkEq_sound hcheck s z
    _ = normEval N M (fun i j => ((A.getD i []).getD j 0 : ℝ)) s z :=
      fromNormRows_sound N M A s z

end Bi
end Erdos993Lean.BCFG
