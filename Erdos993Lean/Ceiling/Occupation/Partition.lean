module

public import Mathlib
public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Floor.TreeDecomp

/-!
# B5, part 1: the hard-core sums at activity `7/3` inside a fixed graph

For a vertex set `s` of a graph `G`, `Z(s) = ∑_{t ⊆ s independent} (7/3)^|t|` (`Zq`) and
`S(s) = ∑_t |t| (7/3)^|t|` (`Sq`); the hard-core mean of `G[s]` at activity `λ = 7/3` is
`μ(s) = S(s) / Z(s)`.  They are the values at `7/3` of `I(s)` and `x I'(s)` (`indepPoly`), which
gives the recurrences used by the occupation bound B5 (the ceiling proof,
Appendix R3):

* the vertex recurrence `Z(s) = Z(s - v) + λ Z(s - N[v])`, `S(s) = S(s - v) + λ (Z + S)(s - N[v])`
  (`Zq_erase`, `Sq_erase`);
* products over edge-free disjoint unions, with the Leibniz rule for `S` (`Zq_union`, `Sq_union`);
* isolated vertices, pendant vertices and edgeless sets (`Zq_isolated`, `Zq_pendant`,
  `Zq_Sq_edgeless`);
* positivity and monotonicity (`Zq_pos`, `Zq_mono`), and the removal bound
  `Z(s) ≤ (10/3)^|r| Z(s - r)` (`Zq_le_sdiff`; in the paper: each absence probability is at least
  `1/b`, `b = 10/3`).
-/

@[expose] public section

namespace Erdos993Lean
namespace Occupation

open Finset Polynomial

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `Z(s) = ∑_{t ⊆ s independent} (7/3)^|t|`. -/
noncomputable def Zq (s : Finset V) : ℚ := Polynomial.aeval (7 / 3 : ℚ) (indepPoly G s)

/-- `S(s) = ∑_{t ⊆ s independent} |t| (7/3)^|t|`. -/
noncomputable def Sq (s : Finset V) : ℚ :=
  Polynomial.aeval (7 / 3 : ℚ) (X * derivative (indepPoly G s))

omit [DecidableEq V] in
/-- `Z(s)` as a sum over the independent subsets of `s`. -/
theorem Zq_eq_sum (s : Finset V) :
    Zq G s = ∑ t ∈ s.powerset.filter (IsIndepFinset G), (7 / 3 : ℚ) ^ t.card := by
  simp [Zq, indepPoly, map_sum]

omit [DecidableEq V] in
/-- `S(s)` as a sum over the independent subsets of `s`. -/
theorem Sq_eq_sum (s : Finset V) :
    Sq G s = ∑ t ∈ s.powerset.filter (IsIndepFinset G), (t.card : ℚ) * (7 / 3 : ℚ) ^ t.card := by
  simp only [Sq, indepPoly, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [derivative_X_pow]
  rcases Nat.eq_zero_or_pos t.card with h | h
  · simp [h]
  · have : (X : ℤ[X]) * (C (t.card : ℤ) * X ^ (t.card - 1)) = C (t.card : ℤ) * X ^ t.card := by
      rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel h]
    rw [this]
    simp

/-- The vertex recurrence for `Z`: `Z(s) = Z(s - v) + (7/3) Z(s - N[v])`. -/
theorem Zq_erase {s : Finset V} {v : V} (hv : v ∈ s) :
    Zq G s = Zq G (s.erase v) + 7 / 3 * Zq G (outsideClosedNbhd G s v) := by
  simp only [Zq]
  rw [indepPoly_erase_add G hv]
  simp [map_add, map_mul]

/-- The vertex recurrence for `S`: `S(s) = S(s - v) + (7/3) (Z + S)(s - N[v])`. -/
theorem Sq_erase {s : Finset V} {v : V} (hv : v ∈ s) :
    Sq G s = Sq G (s.erase v) +
      7 / 3 * (Zq G (outsideClosedNbhd G s v) + Sq G (outsideClosedNbhd G s v)) := by
  simp only [Sq, Zq]
  rw [indepPoly_erase_add G hv]
  simp only [derivative_mul, derivative_X, one_mul, map_add, map_mul, aeval_X]
  ring

/-- `Z` is multiplicative over an edge-free disjoint union. -/
theorem Zq_union {s t : Finset V} (hst : Disjoint s t) (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    Zq G (s ∪ t) = Zq G s * Zq G t := by
  simp only [Zq]
  rw [indepPoly_union G hst hno, map_mul]

/-- The Leibniz rule for `S` over an edge-free disjoint union. -/
theorem Sq_union {s t : Finset V} (hst : Disjoint s t) (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    Sq G (s ∪ t) = Sq G s * Zq G t + Zq G s * Sq G t := by
  simp only [Sq, Zq]
  rw [indepPoly_union G hst hno, derivative_mul]
  simp only [map_mul, map_add, aeval_X]
  ring

omit [DecidableEq V] in
theorem Zq_empty : Zq G (∅ : Finset V) = 1 := by
  simp [Zq, indepPoly_empty]

omit [DecidableEq V] in
theorem Sq_empty : Sq G (∅ : Finset V) = 0 := by
  simp [Sq, indepPoly_empty]

theorem Zq_singleton (v : V) : Zq G {v} = 10 / 3 := by
  simp only [Zq, indepPoly_singleton]
  simp
  norm_num

theorem Sq_singleton (v : V) : Sq G {v} = 7 / 3 := by
  simp only [Sq, indepPoly_singleton]
  simp

omit [DecidableEq V] in
/-- `Z(s) ≥ 1 > 0` (the empty set). -/
theorem Zq_pos (s : Finset V) : 0 < Zq G s := by
  rw [Zq_eq_sum]
  have h0 : (∅ : Finset V) ∈ s.powerset.filter (IsIndepFinset G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
    exact fun v hv => absurd hv (Finset.notMem_empty v)
  calc (0 : ℚ) < (7 / 3 : ℚ) ^ (∅ : Finset V).card := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun t : Finset V => (7 / 3 : ℚ) ^ t.card)
        (fun t _ => by positivity) h0

omit [DecidableEq V] in
/-- `Z` is monotone under inclusion. -/
theorem Zq_mono {s s' : Finset V} (h : s ⊆ s') : Zq G s ≤ Zq G s' := by
  rw [Zq_eq_sum, Zq_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.powerset_mono.mpr h)
  · intro t _ _
    positivity

omit [DecidableEq V] in
theorem Sq_nonneg (s : Finset V) : 0 ≤ Sq G s := by
  rw [Sq_eq_sum]
  exact Finset.sum_nonneg fun t _ => by positivity

/-- `s - N[v] = (s - v) - N_s(v)`. -/
theorem outsideClosedNbhd_eq (s : Finset V) (v : V) :
    outsideClosedNbhd G s v = (s.erase v) \ nbrsIn G s v := by
  ext w
  simp only [outsideClosedNbhd, nbrsIn, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
  tauto

theorem outsideClosedNbhd_subset (s : Finset V) (v : V) :
    outsideClosedNbhd G s v ⊆ s.erase v := by
  rw [outsideClosedNbhd_eq]
  exact Finset.sdiff_subset

/-- Removing one vertex decreases `Z` by a factor of at most `10/3`. -/
theorem Zq_le_erase {s : Finset V} {v : V} (hv : v ∈ s) :
    Zq G s ≤ 10 / 3 * Zq G (s.erase v) := by
  rw [Zq_erase G hv]
  have := Zq_mono G (outsideClosedNbhd_subset G s v)
  linarith

/-- Removing a set `r` of vertices decreases `Z` by a factor of at most `(10/3)^|r|`. -/
theorem Zq_le_sdiff {s r : Finset V} (hr : r ⊆ s) :
    Zq G s ≤ (10 / 3) ^ r.card * Zq G (s \ r) := by
  induction r using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    have hr' : r ⊆ s := (Finset.subset_insert a r).trans hr
    have has : a ∈ s \ r := Finset.mem_sdiff.mpr ⟨hr (Finset.mem_insert_self a r), har⟩
    have heq : s \ insert a r = (s \ r).erase a := by
      ext w
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      tauto
    rw [heq, Finset.card_insert_of_notMem har, pow_succ]
    have h1 := ih hr'
    have h2 := Zq_le_erase G has
    have h3 : (0 : ℚ) ≤ (10 / 3) ^ r.card := by positivity
    calc Zq G s ≤ (10 / 3) ^ r.card * Zq G (s \ r) := h1
      _ ≤ (10 / 3) ^ r.card * (10 / 3 * Zq G ((s \ r).erase a)) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by ring

/-- An isolated vertex of `s` multiplies `Z` by `10/3`. -/
theorem Zq_isolated {s : Finset V} {x : V} (hx : x ∈ s) (hxn : nbrsIn G s x = ∅) :
    Zq G s = 10 / 3 * Zq G (s.erase x) := by
  rw [Zq_erase G hx, outsideClosedNbhd_eq, hxn, Finset.sdiff_empty]
  ring

/-- An isolated vertex `x` of `s`: `S(s) = (10/3) S(s - x) + (7/3) Z(s - x)`. -/
theorem Sq_isolated {s : Finset V} {x : V} (hx : x ∈ s) (hxn : nbrsIn G s x = ∅) :
    Sq G s = 10 / 3 * Sq G (s.erase x) + 7 / 3 * Zq G (s.erase x) := by
  rw [Sq_erase G hx, outsideClosedNbhd_eq, hxn, Finset.sdiff_empty]
  ring

/-- A pendant vertex `ℓ` with stem `a`: `Z(s) = Z(s - ℓ) + (7/3) Z(s - ℓ - a)`. -/
theorem Zq_pendant {s : Finset V} {ℓ a : V} (hℓ : ℓ ∈ s) (hn : nbrsIn G s ℓ = {a}) :
    Zq G s = Zq G (s.erase ℓ) + 7 / 3 * Zq G ((s.erase ℓ).erase a) := by
  rw [Zq_erase G hℓ, outsideClosedNbhd_eq, hn, Finset.sdiff_singleton_eq_erase]

/-- A pendant vertex `ℓ` with stem `a`: `S(s) = S(s - ℓ) + (7/3) (Z + S)(s - ℓ - a)`. -/
theorem Sq_pendant {s : Finset V} {ℓ a : V} (hℓ : ℓ ∈ s) (hn : nbrsIn G s ℓ = {a}) :
    Sq G s = Sq G (s.erase ℓ) +
      7 / 3 * (Zq G ((s.erase ℓ).erase a) + Sq G ((s.erase ℓ).erase a)) := by
  rw [Sq_erase G hℓ, outsideClosedNbhd_eq, hn, Finset.sdiff_singleton_eq_erase]

/-- An edgeless vertex set `r`: `Z(r) = (10/3)^|r|` and `S(r) = (7/10) |r| (10/3)^|r|`. -/
theorem Zq_Sq_edgeless {r : Finset V} (hr : ∀ a ∈ r, ∀ b ∈ r, ¬ G.Adj a b) :
    Zq G r = (10 / 3) ^ r.card ∧ Sq G r = 7 / 10 * r.card * (10 / 3) ^ r.card := by
  induction r using Finset.induction_on with
  | empty => simp [Zq_empty, Sq_empty]
  | insert a r har ih =>
    have hr' : ∀ x ∈ r, ∀ y ∈ r, ¬ G.Adj x y := fun x hx y hy =>
      hr x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
    obtain ⟨ih1, ih2⟩ := ih hr'
    have hdisj : Disjoint ({a} : Finset V) r := Finset.disjoint_singleton_left.mpr har
    have hno : ∀ x ∈ ({a} : Finset V), ∀ y ∈ r, ¬ G.Adj x y := by
      intro x hx y hy
      rw [Finset.mem_singleton] at hx
      subst hx
      exact hr x (Finset.mem_insert_self x r) y (Finset.mem_insert_of_mem hy)
    have hins : insert a r = {a} ∪ r := Finset.insert_eq a r
    rw [hins, Zq_union G hdisj hno, Sq_union G hdisj hno, Zq_singleton, Sq_singleton, ih1, ih2,
      Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    constructor
    · ring
    · push_cast
      ring

omit [DecidableEq V] in
/-- `Z(s) = ∑_k i_k(s) (7/3)^k`. -/
theorem Zq_eq_sum_count (s : Finset V) :
    Zq G s = ∑ k ∈ range (s.card + 1), (indepCount G s k : ℚ) * (7 / 3 : ℚ) ^ k := by
  rw [Zq_eq_sum]
  have hmaps : ∀ t ∈ s.powerset.filter (IsIndepFinset G), t.card ∈ range (s.card + 1) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card ht.1))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const,
    nsmul_eq_mul]
  rfl

omit [DecidableEq V] in
/-- `S(s) = ∑_k k i_k(s) (7/3)^k`. -/
theorem Sq_eq_sum_count (s : Finset V) :
    Sq G s = ∑ k ∈ range (s.card + 1), (k : ℚ) * (indepCount G s k : ℚ) * (7 / 3 : ℚ) ^ k := by
  rw [Sq_eq_sum]
  have hmaps : ∀ t ∈ s.powerset.filter (IsIndepFinset G), t.card ∈ range (s.card + 1) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card ht.1))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const,
    nsmul_eq_mul]
  unfold indepCount
  ring

end Occupation
end Erdos993Lean
