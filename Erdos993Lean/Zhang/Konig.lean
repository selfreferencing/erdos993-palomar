module

public import Mathlib
public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Ceiling.Statement
public import Erdos993Lean.Ceiling.Occupation.Main
public import Erdos993Lean.SmallAlpha.BipartiteTail

/-!
# Zhang's finite part, 1: König's theorem for forests

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Section 2.1, identity (1): a forest on `n` vertices with independence number
`a` and matching number `v` has `a + v = n` (and `δ = a - v ≥ 0`).

Main results:
* `Zhang.alphaIn G s`: the independence number of the subgraph induced on a finite vertex set `s`
  (the companion of the package's `Occupation.nuIn`, the matching number of `G[s]`).
* `Zhang.alphaIn_isolated`, `Zhang.alphaIn_pendant`: deleting an isolated vertex, or a pendant
  vertex together with its neighbour, lowers `α` by one (the paper's leaf-deletion step).
* `Zhang.alphaIn_add_nuIn`: **König for forests, Finset form**: `α(G[s]) + ν(G[s]) = |s|` for
  every finite vertex set `s` of an acyclic graph (induction; the matching side is the package's
  `Occupation.nuIn_isolated`, `Occupation.nuIn_pendant`, the leaf from `Occupation.exists_leafStem`).
* `Zhang.indepNum_add_matchingNumber`: **König for forests**: for an acyclic graph on a finite
  type, `G.indepNum + matchingNumber G = Fintype.card V`.  (The package had the inequality `≤`,
  `Ceiling.card_add_matchingNumber_le`.)
* `Zhang.matchingNumber_le_indepNum`: `δ = a - v ≥ 0` (from `n ≤ 2a`,
  `SmallAlpha.card_le_two_mul_indepNum`).

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean
namespace Zhang

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The independence number of an induced subgraph -/

variable (G) in
/-- The independence number `α(G[s])` of the subgraph induced on the finite vertex set `s`. -/
noncomputable def alphaIn (s : Finset V) : ℕ :=
  (s.powerset.filter (IsIndepFinset G)).sup Finset.card

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem isIndepFinset_empty : IsIndepFinset G (∅ : Finset V) :=
  fun v hv => absurd hv (Finset.notMem_empty v)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem isIndepFinset_mono {t u : Finset V} (ht : IsIndepFinset G t) (hut : u ⊆ t) :
    IsIndepFinset G u :=
  fun a ha b hb => ht a (hut ha) b (hut hb)

omit [DecidableEq V] in
theorem le_alphaIn {s t : Finset V} (hts : t ⊆ s) (ht : IsIndepFinset G t) :
    t.card ≤ alphaIn G s := by
  unfold alphaIn
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hts, ht⟩

omit [DecidableEq V] in
variable (G) in
theorem exists_alphaIn (s : Finset V) :
    ∃ t ⊆ s, IsIndepFinset G t ∧ t.card = alphaIn G s := by
  unfold alphaIn
  have hne : (s.powerset.filter (IsIndepFinset G)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset s, isIndepFinset_empty⟩⟩
  obtain ⟨t, ht, hteq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at ht
  exact ⟨t, ht.1, ht.2, hteq.symm⟩

omit [DecidableEq V] in
theorem alphaIn_empty : alphaIn G (∅ : Finset V) = 0 := by
  obtain ⟨t, hts, -, htc⟩ := exists_alphaIn G (∅ : Finset V)
  rw [Finset.subset_empty] at hts
  rw [← htc, hts, Finset.card_empty]

omit [DecidableEq V] in
theorem alphaIn_mono {s s' : Finset V} (hss : s ⊆ s') : alphaIn G s ≤ alphaIn G s' := by
  obtain ⟨t, hts, ht, htc⟩ := exists_alphaIn G s
  rw [← htc]
  exact le_alphaIn (hts.trans hss) ht

omit [DecidableEq V] in
theorem alphaIn_le_card (s : Finset V) : alphaIn G s ≤ s.card := by
  obtain ⟨t, hts, -, htc⟩ := exists_alphaIn G s
  rw [← htc]
  exact Finset.card_le_card hts

/-- Deleting an isolated vertex of `G[s]` lowers the independence number by one. -/
theorem alphaIn_isolated {s : Finset V} {x : V} (hx : x ∈ s) (hxn : nbrsIn G s x = ∅) :
    alphaIn G s = alphaIn G (s.erase x) + 1 := by
  have key : ∀ y ∈ s, ¬ G.Adj x y := by
    intro y hy hxy
    have hmem : y ∈ nbrsIn G s x := mem_nbrsIn.mpr ⟨hy, hxy⟩
    rw [hxn] at hmem
    exact Finset.notMem_empty y hmem
  apply le_antisymm
  · obtain ⟨t, hts, ht, htc⟩ := exists_alphaIn G s
    have h1 : t.erase x ⊆ s.erase x := Finset.erase_subset_erase x hts
    have h2 := le_alphaIn h1 (isIndepFinset_mono ht (Finset.erase_subset x t))
    have h3 := Finset.pred_card_le_card_erase (s := t) (a := x)
    omega
  · obtain ⟨t, hts, ht, htc⟩ := exists_alphaIn G (s.erase x)
    have hxt : x ∉ t := fun h => (Finset.mem_erase.mp (hts h)).1 rfl
    have hts' : t ⊆ s := hts.trans (Finset.erase_subset x s)
    have hind : IsIndepFinset G (insert x t) := by
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb] at hab
        exact G.irrefl hab
      · rw [ha] at hab
        exact key b (hts' hb) hab
      · rw [hb] at hab
        exact key a (hts' ha) hab.symm
      · exact ht a ha b hb hab
    have := le_alphaIn (Finset.insert_subset hx hts') hind
    rw [Finset.card_insert_of_notMem hxt] at this
    omega

/-- Deleting a pendant vertex `ℓ` of `G[s]` together with its neighbour `a` lowers the
independence number by one (a maximum independent set may be chosen to contain the leaf). -/
theorem alphaIn_pendant {s : Finset V} {ℓ a : V} (hℓ : ℓ ∈ s) (hn : nbrsIn G s ℓ = {a}) :
    alphaIn G s = alphaIn G ((s.erase ℓ).erase a) + 1 := by
  have ha : a ∈ nbrsIn G s ℓ := by
    rw [hn]
    exact Finset.mem_singleton_self a
  obtain ⟨has, hadj⟩ := mem_nbrsIn.mp ha
  apply le_antisymm
  · obtain ⟨t, hts, ht, htc⟩ := exists_alphaIn G s
    have h1 : (t.erase ℓ).erase a ⊆ (s.erase ℓ).erase a :=
      Finset.erase_subset_erase a (Finset.erase_subset_erase ℓ hts)
    have h2 := le_alphaIn h1 (isIndepFinset_mono ht ((Finset.erase_subset a _).trans (Finset.erase_subset ℓ t)))
    -- `t` cannot contain both `ℓ` and `a`
    have h3 : t.card ≤ ((t.erase ℓ).erase a).card + 1 := by
      by_cases hℓt : ℓ ∈ t
      · have hat : a ∉ t := fun hat => ht ℓ hℓt a hat hadj
        have hat' : a ∉ t.erase ℓ := fun h => hat (Finset.mem_of_mem_erase h)
        rw [Finset.erase_eq_of_notMem hat', Finset.card_erase_of_mem hℓt]
        omega
      · rw [Finset.erase_eq_of_notMem hℓt]
        have := Finset.pred_card_le_card_erase (s := t) (a := a)
        omega
    omega
  · obtain ⟨t, hts, ht, htc⟩ := exists_alphaIn G ((s.erase ℓ).erase a)
    have hℓt : ℓ ∉ t := by
      intro h
      have := hts h
      simp at this
    have hts' : t ⊆ s := hts.trans ((Finset.erase_subset a _).trans (Finset.erase_subset ℓ s))
    have key : ∀ y ∈ t, ¬ G.Adj ℓ y := by
      intro y hy hly
      have hy' := hts hy
      have hmem : y ∈ nbrsIn G s ℓ := mem_nbrsIn.mpr ⟨hts' hy, hly⟩
      rw [hn, Finset.mem_singleton] at hmem
      rw [hmem] at hy'
      simp at hy'
    have hind : IsIndepFinset G (insert ℓ t) := by
      intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rw [hx, hy] at hxy
        exact G.irrefl hxy
      · rw [hx] at hxy
        exact key y hy hxy
      · rw [hy] at hxy
        exact key x hx hxy.symm
      · exact ht x hx y hy hxy
    have := le_alphaIn (Finset.insert_subset hℓ hts') hind
    rw [Finset.card_insert_of_notMem hℓt] at this
    omega

/-! ### König's theorem for forests -/

/-- **König's theorem for forests, Finset form** (Zhang, (1)): for every finite vertex set `s` of
an acyclic graph, `α(G[s]) + ν(G[s]) = |s|`.  Induction by deleting an isolated vertex, or a leaf
together with its neighbour (the paper's proof). -/
theorem alphaIn_add_nuIn (hG : G.IsAcyclic) (s : Finset V) :
    alphaIn G s + Occupation.nuIn G s = s.card := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hiso : ∃ x ∈ s, nbrsIn G s x = ∅
    · obtain ⟨x, hx, hxn⟩ := hiso
      rw [alphaIn_isolated hx hxn, Occupation.nuIn_isolated hx hxn]
      have h1 := ih _ (Finset.erase_ssubset hx)
      have h2 := Finset.card_erase_add_one hx
      omega
    · push_neg at hiso
      rcases s.eq_empty_or_nonempty with rfl | hne
      · rw [alphaIn_empty, Occupation.nuIn_eq_zero_of_edgeless (by simp), Finset.card_empty]
      · obtain ⟨v, hv, hΛ, -⟩ := Occupation.exists_leafStem hG hiso hne
        obtain ⟨ℓ, hℓ⟩ := hΛ
        obtain ⟨hℓN, hℓn⟩ := Occupation.mem_leavesAt.mp hℓ
        have hℓs : ℓ ∈ s := (mem_nbrsIn.mp hℓN).1
        have hvℓ : v ≠ ℓ := G.ne_of_adj (mem_nbrsIn.mp hℓN).2
        have hvE : v ∈ s.erase ℓ := Finset.mem_erase.mpr ⟨hvℓ, hv⟩
        rw [alphaIn_pendant hℓs hℓn, Occupation.nuIn_pendant hℓs hℓn]
        have hsub : (s.erase ℓ).erase v ⊂ s :=
          (Finset.erase_subset v _).trans_ssubset (Finset.erase_ssubset hℓs)
        have h1 := ih _ hsub
        have h2 := Finset.card_erase_add_one hvE
        have h3 := Finset.card_erase_add_one hℓs
        omega

section Fintype

variable [Fintype V]

omit [DecidableEq V] in
/-- On the whole vertex set, `alphaIn` is Mathlib's independence number. -/
theorem alphaIn_univ : alphaIn G Finset.univ = G.indepNum := by
  apply le_antisymm
  · obtain ⟨t, -, ht, htc⟩ := exists_alphaIn G (Finset.univ : Finset V)
    rw [← htc]
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro v hv w hw _ hadj
    exact ht v hv w hw hadj
  · obtain ⟨t, ht⟩ := G.exists_isNIndepSet_indepNum
    rw [← ht.card_eq]
    apply le_alphaIn (Finset.subset_univ t)
    intro v hv w hw hadj
    exact ht.isIndepSet hv hw (G.ne_of_adj hadj) hadj

omit [DecidableEq V] in
/-- On the whole vertex set, `Occupation.nuIn` is `matchingNumber` (for any finite vertex type;
the package's `Occupation.nuIn_univ` is the case `Fin n`). -/
theorem nuIn_univ_eq_matchingNumber : Occupation.nuIn G Finset.univ = matchingNumber G := by
  symm
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨M, hM, hMc⟩ := Occupation.exists_isMatchingIn_card_eq G Finset.univ
    refine ⟨(M : Set (Sym2 V)), fun e he => (hM.1 e he).1, ?_, M.finite_toSet, ?_⟩
    · rw [Set.ncard_coe_finset, hMc]
    · intro e he f hf hef
      exact hM.2 e he f hf hef
  · rintro k ⟨M, hMsub, rfl, hMfin, hMdisj⟩
    have h : Occupation.IsMatchingIn G Finset.univ hMfin.toFinset := by
      refine ⟨fun e he => ?_, fun e he f hf hef => ?_⟩
      · rw [Set.Finite.mem_toFinset] at he
        exact ⟨hMsub he, fun a _ => Finset.mem_univ a⟩
      · rw [Set.Finite.mem_toFinset] at he hf
        exact hMdisj he hf hef
    rw [Set.ncard_eq_toFinset_card M hMfin]
    exact Occupation.le_nuIn h

/-- **König's theorem for forests** (Zhang, identity (1) `a + v = n`): for an acyclic graph on a
finite vertex type, the independence number plus the matching number is the number of
vertices. -/
theorem indepNum_add_matchingNumber (hG : G.IsAcyclic) :
    G.indepNum + matchingNumber G = Fintype.card V := by
  rw [← alphaIn_univ, ← nuIn_univ_eq_matchingNumber, alphaIn_add_nuIn hG, Finset.card_univ]

/-- `v = n - a`. -/
theorem matchingNumber_eq_card_sub (hG : G.IsAcyclic) :
    matchingNumber G = Fintype.card V - G.indepNum := by
  have := indepNum_add_matchingNumber hG
  omega

/-- `δ = a - v ≥ 0`: the matching number of a forest is at most its independence number. -/
theorem matchingNumber_le_indepNum (hG : G.IsAcyclic) : matchingNumber G ≤ G.indepNum := by
  have h1 := indepNum_add_matchingNumber hG
  have h2 := SmallAlpha.card_le_two_mul_indepNum hG
  omega

end Fintype

/-- König for the package's `FiniteForest`: `independenceNumber F + matchingNumber F.graph = F.n`. -/
theorem independenceNumber_add_matchingNumber (F : FiniteForest) :
    independenceNumber F + matchingNumber F.graph = F.n := by
  classical
  unfold independenceNumber
  have := indepNum_add_matchingNumber (G := F.graph) F.isForest
  rwa [Fintype.card_fin] at this

end Zhang
end Erdos993Lean
