module

public import Mathlib
public import Erdos993Lean.Sequences

/-!
# Independence counts and the independence polynomial of an induced subgraph

For a simple graph `G` on a vertex type `V` and a finite vertex set `s`, `indepCount G s k` is the
number of independent `k`-subsets of `s`, and `indepPoly G s` is the independence polynomial of
the subgraph induced on `s`.  Working with vertex *subsets* of one fixed graph (instead of
induced subgraphs on subtypes) keeps every recurrence inside one vertex type.

Main results:
* `indepPoly_erase_add`: the vertex recurrence `I(s) = I(s - v) + x · I(s - N[v])`;
* `indepPoly_union`: multiplicativity over a disjoint union with no edges between the parts;
* `indepCount_noInternalZeros`: every independence sequence has no internal zeros;
* `indepCount_univ`: for `s = univ` the count is Mathlib's `(G.indepSetFinset k).card`.
-/

@[expose] public section

namespace Erdos993Lean

open Polynomial Finset

section General

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A finite vertex set is independent in `G`: no two of its vertices are adjacent. -/
def IsIndepFinset (t : Finset V) : Prop :=
  ∀ v ∈ t, ∀ w ∈ t, ¬ G.Adj v w

instance (t : Finset V) : Decidable (IsIndepFinset G t) := by
  unfold IsIndepFinset
  infer_instance

/-- The number of independent `k`-element subsets of `s`. -/
def indepCount (s : Finset V) (k : ℕ) : ℕ :=
  ((s.powerset.filter (IsIndepFinset G)).filter (fun t => t.card = k)).card

/-- The independence polynomial of the subgraph of `G` induced on `s`. -/
noncomputable def indepPoly (s : Finset V) : ℤ[X] :=
  ∑ t ∈ s.powerset.filter (IsIndepFinset G), X ^ t.card

/-- The vertices of `s` outside the closed neighbourhood of `v`, i.e. `s \ N[v]`. -/
def outsideClosedNbhd (s : Finset V) (v : V) : Finset V :=
  s.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)

omit [DecidableEq V] in
theorem indepPoly_coeff (s : Finset V) (k : ℕ) :
    (indepPoly G s).coeff k = (indepCount G s k : ℤ) := by
  simp [indepPoly, indepCount, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow,
    Finset.sum_boole, eq_comm]

omit [DecidableEq V] in
theorem indepPoly_empty : indepPoly G (∅ : Finset V) = 1 := by
  have h : IsIndepFinset G (∅ : Finset V) := fun v hv => absurd hv (Finset.notMem_empty v)
  rw [indepPoly, Finset.powerset_empty, Finset.filter_singleton, if_pos h, Finset.sum_singleton,
    Finset.card_empty, pow_zero]

theorem indepPoly_singleton (v : V) : indepPoly G {v} = 1 + X := by
  have h : ({v} : Finset V).powerset.filter (IsIndepFinset G) = {∅, {v}} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      intro a ha b hb
      rcases h with rfl | rfl
      · exact absurd ha (Finset.notMem_empty a)
      · rw [Finset.mem_singleton] at ha hb
        subst ha
        subst hb
        exact G.irrefl
  rw [indepPoly, h, Finset.sum_pair (Finset.singleton_ne_empty v).symm, Finset.card_empty,
    Finset.card_singleton, pow_zero, pow_one]

/-- The vertex recurrence: `I(G[s]) = I(G[s - v]) + x · I(G[s - N[v]])` for `v ∈ s`. -/
theorem indepPoly_erase_add {s : Finset V} {v : V} (hv : v ∈ s) :
    indepPoly G s = indepPoly G (s.erase v) + X * indepPoly G (outsideClosedNbhd G s v) := by
  unfold indepPoly
  rw [← Finset.sum_filter_not_add_sum_filter (s.powerset.filter (IsIndepFinset G))
    (fun t => v ∈ t) (fun t => (X : ℤ[X]) ^ t.card)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
    tauto
  · rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun t => t.erase v) (fun u => insert v u) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_powerset] at ht ⊢
      obtain ⟨⟨hts, hti⟩, hvt⟩ := ht
      refine ⟨?_, ?_⟩
      · intro w hw
        rw [Finset.mem_erase] at hw
        simp only [outsideClosedNbhd, Finset.mem_filter]
        exact ⟨hts hw.2, hw.1, hti v hvt w hw.2⟩
      · exact fun a ha b hb => hti a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_powerset] at hu ⊢
      obtain ⟨hus, hui⟩ := hu
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self v u⟩
      · intro w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact hv
        · exact (Finset.mem_filter.mp (hus hw)).1
      · intro a ha b hb
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact G.irrefl
        · exact (Finset.mem_filter.mp (hus hb)).2.2
        · exact fun h => (Finset.mem_filter.mp (hus ha)).2.2 h.symm
        · exact hui a ha b hb
    · intro t ht
      simp only [Finset.mem_filter] at ht
      exact Finset.insert_erase ht.2
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_powerset] at hu
      apply Finset.erase_insert
      intro hvu
      exact (Finset.mem_filter.mp (hu.1 hvu)).2.1 rfl
    · intro t ht
      simp only [Finset.mem_filter] at ht
      rw [← Finset.card_erase_add_one ht.2, pow_succ']

/-- Multiplicativity over a disjoint union with no edges between the two parts. -/
theorem indepPoly_union {s t : Finset V} (hst : Disjoint s t)
    (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    indepPoly G (s ∪ t) = indepPoly G s * indepPoly G t := by
  unfold indepPoly
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun u => (u ∩ s, u ∩ t)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hu ⊢
    obtain ⟨_, hui⟩ := hu
    refine ⟨⟨Finset.inter_subset_right, ?_⟩, ⟨Finset.inter_subset_right, ?_⟩⟩
    · exact fun a ha b hb => hui a (Finset.mem_of_mem_inter_left ha) b
        (Finset.mem_of_mem_inter_left hb)
    · exact fun a ha b hb => hui a (Finset.mem_of_mem_inter_left ha) b
        (Finset.mem_of_mem_inter_left hb)
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hab ⊢
    obtain ⟨⟨has, hai⟩, ⟨hbt, hbi⟩⟩ := hab
    refine ⟨Finset.union_subset_union has hbt, ?_⟩
    intro x hx y hy
    rw [Finset.mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hai x hx y hy
    · exact hno x (has hx) y (hbt hy)
    · exact fun h => hno y (has hy) x (hbt hx) h.symm
    · exact hbi x hx y hy
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    dsimp only
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hu.1]
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hab
    obtain ⟨⟨has, _⟩, ⟨hbt, _⟩⟩ := hab
    have h1 : Disjoint b s := (hst.mono_right hbt).symm
    have h2 : Disjoint a t := hst.mono_left has
    simp only [Prod.mk.injEq]
    constructor
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr has,
        Finset.disjoint_iff_inter_eq_empty.mp h1, Finset.union_empty]
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hbt,
        Finset.disjoint_iff_inter_eq_empty.mp h2, Finset.empty_union]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    have hu' : u = u ∩ s ∪ u ∩ t := by
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hu.1]
    have hd : Disjoint (u ∩ s) (u ∩ t) :=
      hst.mono Finset.inter_subset_right Finset.inter_subset_right
    rw [← pow_add, ← Finset.card_union_of_disjoint hd, ← hu']

/-- The same multiplicativity at the level of counts (Cauchy product). -/
theorem indepCount_union {s t : Finset V} (hst : Disjoint s t)
    (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) (k : ℕ) :
    indepCount G (s ∪ t) k =
      ∑ i ∈ Finset.range (k + 1), indepCount G s i * indepCount G t (k - i) := by
  have h := congrArg (fun p => Polynomial.coeff p k) (indepPoly_union G hst hno)
  simp only [Polynomial.coeff_mul, indepPoly_coeff] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  exact_mod_cast h

theorem indepCount_zero (s : Finset V) : indepCount G s 0 = 1 := by
  unfold indepCount
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext t
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro rfl
    exact ⟨⟨Finset.empty_subset _, fun v hv => absurd hv (Finset.notMem_empty v)⟩, rfl⟩

omit [DecidableEq V] in
theorem indepCount_eq_zero_of_card_lt (s : Finset V) {k : ℕ} (hk : s.card < k) :
    indepCount G s k = 0 := by
  unfold indepCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_powerset] at ht
  have := Finset.card_le_card ht.1
  omega

omit [DecidableEq V] in
theorem indepCount_finitelySupported (s : Finset V) : FinitelySupported (indepCount G s) := by
  exact ⟨s.card + 1, fun k hk => indepCount_eq_zero_of_card_lt G s (by omega)⟩

omit [DecidableEq V] in
/-- `indepCount G s k` is nonzero exactly when `s` has an independent `k`-subset. -/
theorem indepCount_ne_zero_iff (s : Finset V) (k : ℕ) :
    indepCount G s k ≠ 0 ↔ ∃ t ⊆ s, IsIndepFinset G t ∧ t.card = k := by
  unfold indepCount
  rw [Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  simp only [Finset.Nonempty, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨t, ⟨hts, hti⟩, htk⟩
    exact ⟨t, hts, hti, htk⟩
  · rintro ⟨t, hts, hti, htk⟩
    exact ⟨t, ⟨hts, hti⟩, htk⟩

omit [DecidableEq V] in
/-- Every independence sequence has no internal zeros (subsets of independent sets are
independent). -/
theorem indepCount_noInternalZeros (s : Finset V) : NoInternalZeros (indepCount G s) := by
  intro i j k _ hjk _ hk
  rw [indepCount_ne_zero_iff] at hk ⊢
  obtain ⟨t, hts, hti, htk⟩ := hk
  obtain ⟨u, hut, huj⟩ := Finset.exists_subset_card_eq (show j ≤ t.card by omega)
  exact ⟨u, hut.trans hts, fun a ha b hb => hti a (hut ha) b (hut hb), huj⟩

end General

section Fintype

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For the whole vertex set, the count is Mathlib's count of independent `k`-sets. -/
theorem indepCount_univ (k : ℕ) :
    indepCount G Finset.univ k = (G.indepSetFinset k).card := by
  unfold indepCount
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
    SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff, SimpleGraph.isIndepSet_iff]
  constructor
  · rintro ⟨hti, htk⟩
    exact ⟨fun v hv w hw _ => hti v hv w hw, htk⟩
  · rintro ⟨hti, htk⟩
    refine ⟨fun v hv w hw hvw => ?_, htk⟩
    by_cases h : v = w
    · subst h
      exact G.irrefl hvw
    · exact hti hv hw h hvw

end Fintype

end Erdos993Lean
