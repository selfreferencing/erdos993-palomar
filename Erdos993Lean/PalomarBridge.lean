module

public import Mathlib
public import Erdos993Lean.Statement

/-!
# From `Erdos993Lean.Erdos993Statement` to the Palomar Challenge statement

The final theorem proves `Erdos993Lean.Erdos993Statement`:
every `FiniteForest` (an acyclic simple graph on `Fin n`) has an independence sequence, counted with Mathlib's
`indepSetFinset`, that is unimodal up to its independence number. The Challenge asks instead about any acyclic graph
on a finite type `V`, counts independent sets with `Nat.card` of a subtype of `Finset V`, and asks for a peak on all
of `ℕ`. The lemmas below close the three gaps:
transport along `Fintype.equivFin V`; equality of the two counts; and
the vanishing of the counts above the independence number.

The bridge lemmas take the forest statement as an explicit hypothesis; Solution supplies the unconditional final theorem.
-/

@[expose] public section

namespace Erdos993Lean.PalomarBridge

open SimpleGraph

/-- A peak up to `N`, followed by zeros above `N`, is a peak on all of `ℕ`. -/
theorem unimodal_of_unimodalUpTo_of_zero {N : ℕ} {a : ℕ → ℕ} (h : UnimodalUpTo N a)
    (hz : ∀ k, N < k → a k = 0) :
    ∃ m, (∀ i, i < m → a i ≤ a (i + 1)) ∧ (∀ i, m ≤ i → a (i + 1) ≤ a i) := by
  obtain ⟨peak, _hpN, hup, hdown⟩ := h
  refine ⟨peak, hup, ?_⟩
  intro i hi
  by_cases hiN : i < N
  · exact hdown i hi hiN
  · rw [hz (i + 1) (by omega)]
    exact Nat.zero_le _

/-- The finite forest on `Fin (Fintype.card V)` obtained from an acyclic graph on a finite type `V`. -/
noncomputable def forestOf {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) : FiniteForest where
  n := Fintype.card V
  graph := G.comap (Fintype.equivFin V).symm.toEmbedding
  isForest := IsAcyclic.of_comap (Fintype.equivFin V).symm.toEmbedding hG

/-- Transporting a finite set along `Fintype.equivFin V` preserves independence. -/
theorem isIndepSet_map_iff {V : Type} [Fintype V] (G : SimpleGraph V) (s : Finset V) :
    (G.comap (Fintype.equivFin V).symm.toEmbedding).IsIndepSet
        (↑(s.map (Fintype.equivFin V).toEmbedding) : Set (Fin (Fintype.card V))) ↔
      G.IsIndepSet (s : Set V) := by
  constructor
  · intro h a ha b hb hab hadj
    have ha' : (Fintype.equivFin V) a ∈ (↑(s.map (Fintype.equivFin V).toEmbedding) : Set _) := by
      simpa using ha
    have hb' : (Fintype.equivFin V) b ∈ (↑(s.map (Fintype.equivFin V).toEmbedding) : Set _) := by
      simpa using hb
    exact h ha' hb' (fun e => hab ((Fintype.equivFin V).injective e)) (by simpa using hadj)
  · intro h a ha b hb hab hadj
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact h ha' hb' (fun e => hab (e ▸ rfl)) (by simpa using hadj)

/-- The two ways of counting `k`-element independent sets agree. -/
theorem count_eq {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) (k : ℕ) :
    Nat.card {s : Finset V // s.card = k ∧ G.IsIndepSet (s : Set V)} =
      independenceCount (forestOf G hG) k := by
  classical
  unfold independenceCount forestOf
  dsimp only
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine (Fintype.equivFin V).finsetCongr.subtypeEquiv ?_
  intro s
  rw [mem_indepSetFinset_iff, isNIndepSet_iff, Equiv.finsetCongr_apply, Finset.card_map]
  exact and_comm.trans (and_congr_left fun _ => (isIndepSet_map_iff G s).symm)

/-- There are no independent sets larger than the independence number. -/
theorem count_eq_zero_of_indepNum_lt (F : FiniteForest) {k : ℕ} (hk : independenceNumber F < k) :
    independenceCount F k = 0 := by
  classical
  simp only [independenceCount, Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  rw [mem_indepSetFinset_iff, isNIndepSet_iff] at hs
  have hle := hs.1.card_le_indepNum
  simp only [independenceNumber] at hk
  omega

/-- **The bridge.** Given the internal statement, every acyclic graph on a finite type has a unimodal independence
sequence in the Challenge's sense. -/
theorem unimodal_nat_card_of_acyclic (hS : Erdos993Statement) {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) :
    ∃ m, (∀ i, i < m → Nat.card {s : Finset V // s.card = i ∧ G.IsIndepSet (s : Set V)} ≤
        Nat.card {s : Finset V // s.card = (i + 1) ∧ G.IsIndepSet (s : Set V)}) ∧
      (∀ i, m ≤ i → Nat.card {s : Finset V // s.card = (i + 1) ∧ G.IsIndepSet (s : Set V)} ≤
        Nat.card {s : Finset V // s.card = i ∧ G.IsIndepSet (s : Set V)}) := by
  have hU : independenceSequenceUnimodal (forestOf G hG) := hS (forestOf G hG)
  have := unimodal_of_unimodalUpTo_of_zero hU
    (fun k hk => count_eq_zero_of_indepNum_lt (forestOf G hG) hk)
  simpa only [count_eq G hG] using this

end Erdos993Lean.PalomarBridge
