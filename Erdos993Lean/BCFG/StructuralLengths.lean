module

public import Erdos993Lean.BCFG.Bivariate

/-!
Length proofs inspect list structure, never
evaluate packet rational coefficients.
No existing definition or data array is changed.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

namespace Uni

theorem length_add (p q : Uni) :
    (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
      cases q with
      | nil => simp [add]
      | cons b q =>
          simp only [add, List.length_cons, ih]
          omega

theorem length_scale (a : Rat) (p : Uni) :
    (scale a p).length = p.length := by
  induction p with
  | nil => rfl
  | cons b p ih => simp only [scale, List.length_cons, ih]

theorem length_mul_cons (a b : Rat) (p q : Uni) :
    (mul (a :: p) (b :: q)).length = p.length + q.length + 1 := by
  induction p generalizing a with
  | nil =>
      simp only [mul, length_add, length_scale, List.length_cons, List.length_nil]
      omega
  | cons c p ih =>
      change (add (scale a (b :: q)) (0 :: mul (c :: p) (b :: q))).length = _
      rw [length_add, length_scale]
      simp only [List.length_cons, ih]
      omega

theorem length_mul_of_nonempty (p q : Uni)
    (hp : 0 < p.length) (hq : 0 < q.length) :
    (mul p q).length = p.length + q.length - 1 := by
  cases p with
  | nil => simp at hp
  | cons a p =>
      cases q with
      | nil => simp at hq
      | cons b q =>
          rw [length_mul_cons]
          simp only [List.length_cons]
          omega

theorem length_pow_affine (a b : Rat) (n : Nat) :
    (pow [a, b] n).length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (mul (pow [a, b] n) [a, b]).length = (n+1)+1
      rw [length_mul_of_nonempty _ _ (by rw [ih]; omega) (by simp)]
      simp only [ih, List.length_cons, List.length_nil]
      omega

/-- No coefficient or nonzero leading-coefficient hypothesis is needed:
these executable lists retain their structural zero padding. -/
theorem outerhomogeneous_length (N k : Nat) (qc rq : Rat) (hk : k ≤ N) :
    (mul (pow [qc, rq] k) (pow [1-qc, -rq] (N-k))).length = N+1 := by
  rw [length_mul_of_nonempty _ _
    (by rw [length_pow_affine]; omega)
    (by rw [length_pow_affine]; omega)]
  rw [length_pow_affine, length_pow_affine]
  omega

theorem length_monomial (a : Rat) (n : Nat) :
    (monomial a n).length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [monomial, List.length_cons, ih]

end Uni

namespace Bi

theorem length_add (p q : Bi) :
    (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
      cases q with
      | nil => simp [add]
      | cons b q =>
          simp only [add, List.length_cons, ih]
          omega

theorem length_tensor (u v : Uni) :
    (tensor u v).length = u.length := by
  simp [tensor]

theorem length_sumRange_le (f : Nat → Bi) (n L : Nat)
    (h : ∀ i < n, (f i).length ≤ L) :
    (sumRange f n).length ≤ L := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
      rw [sumRange, length_add]
      exact max_le
        (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
        (h n (Nat.lt_succ_self n))

theorem length_sumRange_eq_of_last (f : Nat → Bi) (n L : Nat)
    (h : ∀ i < n+1, (f i).length ≤ L) (hlast : (f n).length = L) :
    (sumRange f (n+1)).length = L := by
  rw [sumRange, length_add, hlast]
  apply max_eq_right
  exact length_sumRange_le f n L
    (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))

theorem normalized_length (N : Nat) (p : Bi) (qc rq a b : Rat) :
    (normalized N p qc rq a b).length = N+1 := by
  unfold normalized
  apply length_sumRange_eq_of_last
  · intro i hi
    rw [length_tensor, Uni.outerhomogeneous_length N i qc rq (by omega)]
  · rw [length_tensor, Uni.outerhomogeneous_length N N qc rq (Nat.le_refl N)]

theorem fromNorm_length (N M : Nat) (A : Bi) :
    (fromNorm N M A).length = N+1 := by
  unfold fromNorm
  apply length_sumRange_eq_of_last
  · intro i hi
    rw [length_tensor, Uni.length_monomial]
    omega
  · rw [length_tensor, Uni.length_monomial]

end Bi
end Erdos993Lean.BCFG
