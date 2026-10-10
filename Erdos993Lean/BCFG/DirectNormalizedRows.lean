module

public import Erdos993Lean.BCFG.UniWholePolynomial
public import Erdos993Lean.BCFG.StructuralLengths
public import Erdos993Lean.BCFG.FromNormRowsFallback
public import Erdos993Lean.BCFG.RowChecksFallback

/-!
Compute one normalization row directly, without constructing or trimming the
other bivariate rows. Its equivalence to the original homogeneous formula is
proved generically by finite-sum interchange. No packet arithmetic is run here.

-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG

open scoped BigOperators

namespace Bi

/-- Coefficient row i in the outer variable, formed from univariate summands. -/
def normalizedRow (N : Nat) (p : Bi) (qc rq a b : Rat) (i : Nat) : Uni :=
  Uni.sumRange (fun k =>
    Uni.scale
      ((Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k))).getD i 0)
      (Uni.comp (p.getD k []) [a,b])) (N+1)

/-- This list is used only by the semantic assembly; finite checks call the
individual normalizedRow directly, avoiding getD of a whole normalization. -/
def normalizedRows (N : Nat) (p : Bi) (qc rq a b : Rat) : Bi :=
  (List.range (N+1)).map (normalizedRow N p qc rq a b)

theorem normalizedRows_length (N : Nat) (p : Bi) (qc rq a b : Rat) :
    (normalizedRows N p qc rq a b).length = N+1 := by
  simp [normalizedRows]

theorem evalReal_normalizedRow (N : Nat) (p : Bi) (qc rq a b : Rat) (i : Nat) (z : ℝ) :
    Uni.evalReal (normalizedRow N p qc rq a b i) z =
      ∑ k ∈ Finset.range (N+1),
        ((Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k))).getD i 0 : ℝ) *
          Uni.evalReal (Uni.comp (p.getD k []) [a,b]) z := by
  simp only [normalizedRow, Uni.evalReal_sumRange, Uni.evalReal_scale]

/-- The direct rows represent precisely the original bivariate normalization.
The homogeneous outer polynomial's full length is supplied by a structural
lemma; no coefficient computation or truncation assumption is introduced. -/
theorem normalizedRows_semantics (N : Nat) (p : Bi) (qc rq a b : Rat) (s z : ℝ) :
    evalReal (normalizedRows N p qc rq a b) s z =
      evalReal (normalized N p qc rq a b) s z := by
  unfold normalizedRows
  rw [evalReal_range_map]
  simp_rw [evalReal_normalizedRow, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold normalized
  rw [evalReal_sumRange]
  apply Finset.sum_congr rfl
  intro k hk
  rw [evalReal_tensor]
  let u := Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k))
  let v := Uni.comp (p.getD k []) [a,b]
  change (∑ i ∈ Finset.range (N+1), ((u.getD i 0 : ℝ) * Uni.evalReal v z) * s^i) =
    Uni.evalReal u s * Uni.evalReal v z
  have hu : u.length = N+1 :=
    Uni.outerhomogeneous_length N k qc rq (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  rw [Uni.evalReal_eq_sum_of_length u (N+1) hu s, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Assemble direct row checks using the already proved row-equality helper.
This is a proof implication, not a full-list kernel reduction. -/
theorem directRows_checkEq (N M : Nat) (p A : Bi) (qc rq a b : Rat)
    (hrows : ∀ i < N+1,
      Uni.checkEq (normalizedRow N p qc rq a b i)
        (Uni.bernVector M (A.getD i [])) = true) :
    checkEq (normalizedRows N p qc rq a b) (fromNormRows N M A) = true := by
  apply checkEq_of_bounded_row_checks (N+1)
    (normalizedRows N p qc rq a b) (fromNormRows N M A)
    (normalizedRows_length N p qc rq a b) (fromNormRows_length N M A)
  intro i hi
  unfold normalizedRows fromNormRows
  rw [getD_range_map (N+1) _ i hi, getD_range_map (N+1) _ i hi]
  exact hrows i hi

/-- Identical scaled source-polynomial expansion conclusion, now obtained from
independent direct row checks. No original data or activity domain is changed. -/
theorem checked_expansion_directRows (N M : Nat) (p A : Bi) (qc rq a b : Rat)
    (hrows : ∀ i < N+1,
      Uni.checkEq (normalizedRow N p qc rq a b i)
        (Uni.bernVector M (A.getD i [])) = true)
    (s z q : ℝ) (hqdef : q = (qc : ℝ)+(rq : ℝ)*s) (hq : q ≠ 1) :
    (1-q)^N * sourceEval N p (q/(1-q)) ((a : ℝ)+(b : ℝ)*z) =
      normEval N M (fun i j => ((A.getD i []).getD j 0 : ℝ)) s z := by
  calc
    (1-q)^N * sourceEval N p (q/(1-q)) ((a : ℝ)+(b : ℝ)*z) =
        evalReal (normalized N p qc rq a b) s z :=
      (normalized_sound N p qc rq a b s z q hqdef hq).symm
    _ = evalReal (normalizedRows N p qc rq a b) s z :=
      (normalizedRows_semantics N p qc rq a b s z).symm
    _ = evalReal (fromNormRows N M A) s z :=
      checkEq_sound (directRows_checkEq N M p A qc rq a b hrows) s z
    _ = normEval N M (fun i j => ((A.getD i []).getD j 0 : ℝ)) s z :=
      fromNormRows_sound N M A s z

end Bi
end Erdos993Lean.BCFG
