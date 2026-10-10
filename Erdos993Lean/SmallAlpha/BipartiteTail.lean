module

public import Mathlib

/-!
# Small independence number, part 1: half-size independent sets and the bipartite tail

**Theorems** (every forest `G` on a finite vertex type, `α = G.indepNum`, `i_k` the number of
independent `k`-sets):

* `SmallAlpha.exists_isIndepSet_subset_two_mul`: every finite vertex set `s` of a forest contains
  an independent subset with at least `|s| / 2` elements (the larger class of a proper
  two-colouring, Mathlib's `SimpleGraph.IsAcyclic.coloringTwo`).
* `SmallAlpha.card_le_two_mul_indepNum`: a forest on `n` vertices has `n ≤ 2 α`.
* `SmallAlpha.bipartite_tail`: **the bipartite tail** `(k + 1) i_{k+1} ≤ 2 (α − k) i_k` for every
  `k` (natural subtraction).
* `SmallAlpha.card_indepSetFinset_succ_le`: hence `i_{k+1} ≤ i_k` whenever `2 α ≤ 3 k + 1`, i.e.
  the independence sequence of a forest is nonincreasing from `⌈(2α − 1)/3⌉` on.

**Proof of the tail.**  Double counting: each independent `(k+1)`-set contains `k + 1` independent
`k`-sets, and each independent `k`-set `I` lies in at most `|W_I|` independent `(k+1)`-sets, where
`W_I` is the set of vertices outside `I` with no neighbour in `I`.  The induced forest on `W_I`
has an independent set `T` with `|W_I| ≤ 2 |T|`, and `I ∪ T` is independent, so
`k + |T| ≤ α` and `|W_I| ≤ 2 (α − k)`.

**Provenance.**  The decrease from `⌈(2α − 1)/3⌉` follows from the self-contained
bipartite tail `(k+1) s_{k+1} ≤ 2(α−k) s_k`.
The
decrease from `⌈(2α − 1)/3⌉` for bipartite graphs is classical (V. E. Levit, E. Mandrescu); the
proof here is a two-colour argument.

**Grade.**  PROVED IN LEAN (no `sorry`, standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean

namespace SmallAlpha

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In a forest, every finite vertex set `s` contains an independent subset with at least half of
the vertices of `s`: the larger colour class of a proper two-colouring. -/
theorem exists_isIndepSet_subset_two_mul (hG : G.IsAcyclic) (s : Finset V) :
    ∃ t ⊆ s, G.IsIndepSet (t : Set V) ∧ s.card ≤ 2 * t.card := by
  let C := hG.coloringTwo
  have hclass : ∀ c : Fin 2,
      G.IsIndepSet ((s.filter (fun v => C v = c) : Finset V) : Set V) := by
    intro c v hv w hw _ hadj
    rw [Finset.mem_coe, Finset.mem_filter] at hv hw
    exact C.valid hadj (hv.2.trans hw.2.symm)
  have hsplit : (s.filter (fun v => C v = 0)).card + (s.filter (fun v => C v = 1)).card =
      s.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := s) (fun v => C v = 0)]
    congr 2
    apply Finset.filter_congr
    intro v _
    generalize C v = x
    revert x
    decide
  rcases le_total (s.filter (fun v => C v = 0)).card (s.filter (fun v => C v = 1)).card with h | h
  · exact ⟨_, Finset.filter_subset _ _, hclass 1, by omega⟩
  · exact ⟨_, Finset.filter_subset _ _, hclass 0, by omega⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **A forest on `n` vertices has `n ≤ 2 α`.** -/
theorem card_le_two_mul_indepNum (hG : G.IsAcyclic) : Fintype.card V ≤ 2 * G.indepNum := by
  obtain ⟨t, -, ht, hcard⟩ := exists_isIndepSet_subset_two_mul hG Finset.univ
  rw [Finset.card_univ] at hcard
  exact hcard.trans (Nat.mul_le_mul_left 2 ht.card_le_indepNum)

/-- The one-vertex extensions of a vertex set `I`: the vertices outside `I` with no neighbour
in `I`. -/
def extensions (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ I ∧ ∀ w ∈ I, ¬ G.Adj v w)

theorem mem_extensions {I : Finset V} {v : V} :
    v ∈ extensions G I ↔ v ∉ I ∧ ∀ w ∈ I, ¬ G.Adj v w := by
  simp [extensions]

/-- An independent `k`-set of a forest has at most `2 (α − k)` one-vertex extensions. -/
theorem card_extensions_le (hG : G.IsAcyclic) {k : ℕ} {I : Finset V} (hI : G.IsNIndepSet k I) :
    (extensions G I).card ≤ 2 * (G.indepNum - k) := by
  obtain ⟨t, hts, ht, hcard⟩ := exists_isIndepSet_subset_two_mul hG (extensions G I)
  have hdisj : Disjoint I t := by
    rw [Finset.disjoint_left]
    intro v hvI hvt
    exact (mem_extensions.mp (hts hvt)).1 hvI
  have hind : G.IsIndepSet ((I ∪ t : Finset V) : Set V) := by
    rw [Finset.coe_union]
    intro v hv w hw hne hadj
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · exact hI.isIndepSet hv hw hne hadj
    · exact (mem_extensions.mp (hts (Finset.mem_coe.mp hw))).2 v (Finset.mem_coe.mp hv) hadj.symm
    · exact (mem_extensions.mp (hts (Finset.mem_coe.mp hv))).2 w (Finset.mem_coe.mp hw) hadj
    · exact ht hv hw hne hadj
  have hle := hind.card_le_indepNum
  rw [Finset.card_union_of_disjoint hdisj, hI.card_eq] at hle
  omega

/-- **The bipartite tail**: for every forest and every `k`,
`(k + 1) i_{k+1} ≤ 2 (α − k) i_k` (natural subtraction; for `k ≥ α` both sides vanish). -/
theorem bipartite_tail (hG : G.IsAcyclic) (k : ℕ) :
    (k + 1) * (G.indepSetFinset (k + 1)).card ≤
      2 * (G.indepNum - k) * (G.indepSetFinset k).card := by
  have key := Finset.card_mul_le_card_mul (s := G.indepSetFinset (k + 1))
    (t := G.indepSetFinset k) (r := fun A B => B ⊆ A) (m := k + 1)
    (n := 2 * (G.indepNum - k)) ?_ ?_
  · calc (k + 1) * (G.indepSetFinset (k + 1)).card
        = (G.indepSetFinset (k + 1)).card * (k + 1) := by ring
      _ ≤ (G.indepSetFinset k).card * (2 * (G.indepNum - k)) := key
      _ = 2 * (G.indepNum - k) * (G.indepSetFinset k).card := by ring
  · -- each independent `(k+1)`-set has `k + 1` independent `k`-subsets
    intro A hA
    rw [SimpleGraph.mem_indepSetFinset_iff] at hA
    have hsub : A.powersetCard k ⊆
        (G.indepSetFinset k).bipartiteAbove (fun A B => B ⊆ A) A := by
      intro B hB
      rw [Finset.mem_powersetCard] at hB
      rw [Finset.mem_bipartiteAbove, SimpleGraph.mem_indepSetFinset_iff]
      exact ⟨⟨hA.isIndepSet.mono (Finset.coe_subset.mpr hB.1), hB.2⟩, hB.1⟩
    have h := Finset.card_le_card hsub
    rwa [Finset.card_powersetCard, hA.card_eq, Nat.choose_succ_self_right] at h
  · -- each independent `k`-set lies in at most `2 (α − k)` independent `(k+1)`-sets
    intro B hB
    rw [SimpleGraph.mem_indepSetFinset_iff] at hB
    refine le_trans ?_ (card_extensions_le hG hB)
    have hsub : (G.indepSetFinset (k + 1)).bipartiteBelow (fun A B => B ⊆ A) B ⊆
        (extensions G B).image (fun v => insert v B) := by
      intro A hA
      rw [Finset.mem_bipartiteBelow, SimpleGraph.mem_indepSetFinset_iff] at hA
      obtain ⟨hAind, hBA⟩ := hA
      have hcard : (A \ B).card = 1 := by
        rw [Finset.card_sdiff_of_subset hBA, hAind.card_eq, hB.card_eq]
        omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
      have hvA : v ∈ A \ B := by rw [hv]; exact Finset.mem_singleton_self v
      rw [Finset.mem_sdiff] at hvA
      have hAeq : insert v B = A := by
        rw [Finset.insert_eq, ← hv, Finset.union_comm, Finset.union_sdiff_of_subset hBA]
      rw [Finset.mem_image]
      refine ⟨v, ?_, hAeq⟩
      rw [mem_extensions]
      refine ⟨hvA.2, fun w hw hadj => ?_⟩
      have hne : v ≠ w := fun h => hvA.2 (h ▸ hw)
      exact hAind.isIndepSet (Finset.mem_coe.mpr hvA.1) (Finset.mem_coe.mpr (hBA hw)) hne hadj
    exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- **Decrease from `⌈(2α − 1)/3⌉`**: `i_{k+1} ≤ i_k` whenever `2 α ≤ 3 k + 1`. -/
theorem card_indepSetFinset_succ_le (hG : G.IsAcyclic) {k : ℕ}
    (hk : 2 * G.indepNum ≤ 3 * k + 1) :
    (G.indepSetFinset (k + 1)).card ≤ (G.indepSetFinset k).card := by
  have h := bipartite_tail hG k
  have h2 : 2 * (G.indepNum - k) ≤ k + 1 := by omega
  have h3 : (k + 1) * (G.indepSetFinset (k + 1)).card ≤ (k + 1) * (G.indepSetFinset k).card :=
    h.trans (Nat.mul_le_mul_right _ h2)
  exact Nat.le_of_mul_le_mul_left h3 (Nat.succ_pos k)

end SmallAlpha

end Erdos993Lean
