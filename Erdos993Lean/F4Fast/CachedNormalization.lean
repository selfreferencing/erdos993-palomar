module

public import Erdos993Lean.BCFG.DirectNormalizedRows

/-!
Exact list-equality adapters for cached components of normalization and
Bernstein coefficient rows. The cache correctness hypotheses retain each
original polynomial operation; the consumer concludes the original row check.
No certificate data is supplied by this module.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

namespace Uni

theorem sumRange_congr (f g : Nat → Uni) (n : Nat)
    (h : ∀ k < n, f k = g k) : sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change add (sumRange f n) (f n) = add (sumRange g n) (g n)
      rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

def cachedBernVector (M : Nat) (H : List Uni) (c : Uni) : Uni :=
  sumRange (fun j => scale (c.getD j 0) (H.getD j [])) (M+1)

theorem bernVector_eq_cached (M : Nat) (H : List Uni) (c : Uni)
    (hH : ∀ j < M+1, bernBasis M j = H.getD j []) :
    bernVector M c = cachedBernVector M H c := by
  unfold bernVector bernPoly cachedBernVector
  apply sumRange_congr
  intro j hj
  rw [hH j hj]

end Uni

namespace Bi

def cachedNormalizedRow (N : Nat) (C W : Bi) (i : Nat) : Uni :=
  Uni.sumRange (fun k =>
    Uni.scale ((W.getD k []).getD i 0) (C.getD k [])) (N+1)

theorem normalizedRow_eq_cached (N : Nat) (p : Bi) (qc rq a b : Rat)
    (C W : Bi) (i : Nat)
    (hC : ∀ k < N+1, Uni.comp (p.getD k []) [a,b] = C.getD k [])
    (hW : ∀ k < N+1,
      Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k)) = W.getD k []) :
    normalizedRow N p qc rq a b i = cachedNormalizedRow N C W i := by
  unfold normalizedRow cachedNormalizedRow
  apply Uni.sumRange_congr
  intro k hk
  rw [hC k hk, hW k hk]

theorem normalizedRow_checkEq_of_cached (N M : Nat) (p A : Bi)
    (qc rq a b : Rat) (C W H : Bi) (i : Nat)
    (hC : ∀ k < N+1, Uni.comp (p.getD k []) [a,b] = C.getD k [])
    (hW : ∀ k < N+1,
      Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k)) = W.getD k [])
    (hH : ∀ j < M+1, Uni.bernBasis M j = H.getD j [])
    (hcheck : Uni.checkEq (cachedNormalizedRow N C W i)
      (Uni.cachedBernVector M H (A.getD i [])) = true) :
    Uni.checkEq (normalizedRow N p qc rq a b i)
      (Uni.bernVector M (A.getD i [])) = true := by
  rw [normalizedRow_eq_cached N p qc rq a b C W i hC hW,
    Uni.bernVector_eq_cached M H (A.getD i []) hH]
  exact hcheck

end Bi

end Erdos993Lean.BCFG
