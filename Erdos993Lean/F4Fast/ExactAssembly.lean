module

public import Erdos993Lean.BCFG.DirectNormalizedRows
public import Erdos993Lean.F4Fast.CachedNormalization
public import Mathlib.Data.List.GetD

/-! Exact executable-list assembly of independent normalization row checks.
No concrete rational arithmetic, evaluation semantics, or source certificate
data occurs in these proofs. All original list padding and trims are retained. -/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG
namespace LightAssembly

theorem uni_add_nil (p : Uni) : Uni.add p [] = p := by
  cases p <;> rfl

theorem bi_getD_add (p q : Bi) (i : Nat) :
    (Bi.add p q).getD i [] = Uni.add (p.getD i []) (q.getD i []) := by
  induction p generalizing q i with
  | nil => simp [Bi.add, Uni.add]
  | cons a p ih =>
      cases q with
      | nil => simp only [Bi.add, List.getD_nil, uni_add_nil]
      | cons b q =>
          cases i with
          | zero => rfl
          | succ i =>
              simpa only [Bi.add, List.getD_cons_succ] using ih q i

theorem bi_getD_sumRange (f : Nat → Bi) (n i : Nat) :
    (Bi.sumRange f n).getD i [] = Uni.sumRange (fun k => (f k).getD i []) n := by
  induction n with
  | zero => simp [Bi.sumRange, Uni.sumRange]
  | succ n ih => rw [Bi.sumRange, bi_getD_add, ih, Uni.sumRange]

theorem bi_getD_tensor (u v : Uni) (i : Nat) (hi : i < u.length) :
    (Bi.tensor u v).getD i [] = Uni.scale (u.getD i 0) v := by
  unfold Bi.tensor
  rw [List.getD_eq_getElem _ [] (by simpa using hi),
      List.getD_eq_getElem _ 0 hi]
  simp only [List.getElem_map]

theorem uni_scale_one (p : Uni) : Uni.scale 1 p = p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [Uni.scale, one_mul, ih]

theorem uni_add_scale_zero (p q : Uni) (hlen : p.length = q.length) :
    Uni.add p (Uni.scale 0 q) = p := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => rfl
      | cons b q => simp at hlen
  | cons a p ih =>
      cases q with
      | nil => simp at hlen
      | cons b q =>
          have ht : p.length = q.length := Nat.succ.inj hlen
          simp only [Uni.scale, Uni.add, zero_mul, add_zero, ih q ht]

theorem uni_length_sumRange_le (f : Nat → Uni) (n L : Nat)
    (h : ∀ i < n, (f i).length ≤ L) :
    (Uni.sumRange f n).length ≤ L := by
  induction n with
  | zero => simp [Uni.sumRange]
  | succ n ih =>
      rw [Uni.sumRange, Uni.length_add]
      exact max_le
        (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
        (h n (Nat.lt_succ_self n))

theorem uni_length_sumRange_eq_of_last (f : Nat → Uni) (n L : Nat)
    (h : ∀ i < n+1, (f i).length ≤ L) (hlast : (f n).length = L) :
    (Uni.sumRange f (n+1)).length = L := by
  rw [Uni.sumRange, Uni.length_add, hlast]
  apply max_eq_right
  exact uni_length_sumRange_le f n L
    (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))

theorem uni_length_bernBasis (M j : Nat) (hj : j ≤ M) :
    (Uni.bernBasis M j).length = M+1 := by
  unfold Uni.bernBasis
  rw [Uni.length_scale, Uni.length_mul_of_nonempty _ _
    (by rw [Uni.length_monomial]; omega)
    (by rw [Uni.length_pow_affine]; omega)]
  rw [Uni.length_monomial, Uni.length_pow_affine]
  omega

theorem uni_length_bernVector (M : Nat) (c : Uni) :
    (Uni.bernVector M c).length = M+1 := by
  unfold Uni.bernVector Uni.bernPoly
  apply uni_length_sumRange_eq_of_last
  · intro j hj
    rw [Uni.length_scale, uni_length_bernBasis M j (by omega)]
  · rw [Uni.length_scale, uni_length_bernBasis M M (Nat.le_refl M)]

theorem bi_add_tensor_monomial (rows : Bi) (v : Uni)
    (hrows : ∀ row ∈ rows, row.length = v.length) :
    Bi.add rows (Bi.tensor (Uni.monomial 1 rows.length) v) = rows ++ [v] := by
  induction rows with
  | nil => simp only [List.length_nil, Uni.monomial, Bi.tensor, List.map_cons,
      List.map_nil, Bi.add, List.nil_append, uni_scale_one]
  | cons row rows ih =>
      have hhead : row.length = v.length := hrows row (by simp)
      have htail : ∀ r ∈ rows, r.length = v.length := by
        intro r hr
        exact hrows r (by simp [hr])
      change Uni.add row (Uni.scale 0 v) ::
        Bi.add rows (Bi.tensor (Uni.monomial 1 rows.length) v) =
          row :: (rows ++ [v])
      rw [uni_add_scale_zero row v hhead, ih htail]

theorem bi_add_tensor_monomial_of_length (rows : Bi) (v : Uni) (n : Nat)
    (hlen : rows.length = n) (hrows : ∀ row ∈ rows, row.length = v.length) :
    Bi.add rows (Bi.tensor (Uni.monomial 1 n) v) = rows ++ [v] := by
  rw [← hlen]
  exact bi_add_tensor_monomial rows v hrows

theorem bi_sumRange_tensor_monomial (f : Nat → Uni) (n L : Nat)
    (h : ∀ i < n+1, (f i).length = L) :
    Bi.sumRange (fun i => Bi.tensor (Uni.monomial 1 i) (f i)) (n+1) =
      (List.range (n+1)).map f := by
  induction n with
  | zero => simp [Bi.sumRange, Bi.add, Bi.tensor, Uni.monomial, uni_scale_one]
  | succ n ih =>
      rw [Bi.sumRange, ih (fun i hi => h i (by omega))]
      have hrows : ∀ row ∈ (List.range (n+1)).map f, row.length = (f (n+1)).length := by
        intro row hr
        rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
        have hiBound : i < n+1 := List.mem_range.mp hi
        rw [h i (by omega), h (n+1) (by omega)]
      rw [bi_add_tensor_monomial_of_length _ _ (n+1) (by simp) hrows,
        List.range_succ (n := n+1), List.map_append]
      rfl

end LightAssembly
namespace Bi

theorem normalized_getD_eq_normalizedRow (N : Nat) (p : Bi) (qc rq a b : Rat)
    (i : Nat) (hi : i < N+1) :
    (normalized N p qc rq a b).getD i [] = normalizedRow N p qc rq a b i := by
  unfold normalized normalizedRow
  rw [LightAssembly.bi_getD_sumRange]
  apply Uni.sumRange_congr
  intro k hk
  apply LightAssembly.bi_getD_tensor
  rw [Uni.outerhomogeneous_length N k qc rq (by omega)]
  exact hi

/-- Literal equality of the original bivariate normalization and direct rows.
The homogeneous outer lengths are proved structurally for every summand. -/
theorem normalized_eq_normalizedRows (N : Nat) (p : Bi) (qc rq a b : Rat) :
    normalized N p qc rq a b = normalizedRows N p qc rq a b := by
  apply List.ext_getElem
  · rw [normalized_length, normalizedRows_length]
  · intro i hi hj
    have hiN : i < N+1 := by simpa only [normalized_length] using hi
    have h := normalized_getD_eq_normalizedRow N p qc rq a b i hiN
    have hr : (normalizedRows N p qc rq a b).getD i [] =
        normalizedRow N p qc rq a b i := by
      unfold normalizedRows
      exact getD_range_map (N+1) _ i hiN
    rw [← List.getD_eq_getElem _ [] hi, ← List.getD_eq_getElem _ [] hj, h, hr]

/-- Literal equality of the original monomial tensor reconstruction and direct
Bernstein rows. Every Bernstein vector has the same structural list length. -/
theorem fromNorm_eq_fromNormRows (N M : Nat) (A : Bi) :
    fromNorm N M A = fromNormRows N M A := by
  unfold fromNorm fromNormRows
  apply LightAssembly.bi_sumRange_tensor_monomial _ N (M+1)
  intro i hi
  exact LightAssembly.uni_length_bernVector M (A.getD i [])

/-- Consume bounded exact row checks into the unchanged original Bi Boolean. -/
theorem normalization_checkEq_of_directRows (N M : Nat) (p A : Bi) (qc rq a b : Rat)
    (hrows : ∀ i < N+1,
      Uni.checkEq (normalizedRow N p qc rq a b i)
        (Uni.bernVector M (A.getD i [])) = true) :
    checkEq (normalized N p qc rq a b) (fromNorm N M A) = true := by
  rw [normalized_eq_normalizedRows, fromNorm_eq_fromNormRows]
  exact directRows_checkEq N M p A qc rq a b hrows

end Bi
end Erdos993Lean.BCFG

#print axioms Erdos993Lean.BCFG.Bi.normalized_eq_normalizedRows
#print axioms Erdos993Lean.BCFG.Bi.fromNorm_eq_fromNormRows
#print axioms Erdos993Lean.BCFG.Bi.normalization_checkEq_of_directRows
