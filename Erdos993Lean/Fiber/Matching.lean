module

public import Mathlib
public import Erdos993Lean.Zhang.Konig

/-!
# Fibers, 1: the saturating matching of a maximum independent set of a forest, exposed leaves

Source: the binomial-fiber note (29 September 2026), Lemmas 2.1 and 2.2.


Setting: `F` a finite forest, `A` an independent set of maximum cardinality, `C = V \ A` (in Lean
`Aᶜ`), `a = |A|`, `c = |C|`.

Main results:
* `Fiber.card_le_card_biUnion_filter_adj` (**Hall's condition for `C`**): for every `U ⊆ C`, the set
  `N_A(U)` of the vertices of `A` with a neighbour in `U` has at least `|U|` elements.  Proof: split
  `U` by a proper two-colouring (Mathlib's `SimpleGraph.IsAcyclic.coloringTwo`) into independent
  sets `U₀, U₁`; `(A \ N_A(Uᵢ)) ∪ Uᵢ` is independent, so `|Uᵢ| ≤ |N_A(Uᵢ)|` by maximality; `N_A(U₀)`
  and `N_A(U₁)` lie in opposite colour classes, hence are disjoint.
* `Fiber.exists_saturating_matching` (**Lemma 2.1**): there is `μ`, injective on `C`, with `μ v ∈ A`
  adjacent to `v` for every `v ∈ C` (Hall's theorem,
  `Finset.all_card_le_biUnion_card_iff_exists_injective`).
* `Fiber.matchingOf A μ` (the matching `{v μ(v) : v ∈ C}`), `Fiber.isMatchingIn_matchingOf`,
  `Fiber.card_matchingOf`: it is a matching of the package's type `Occupation.IsMatchingIn` with
  `c` edges.
* `Fiber.exists_maxIndep`: the hypotheses are satisfiable (every forest has a maximum independent
  set).
* Consequences: `Fiber.card_compl_le_card` (`c ≤ a`), `Fiber.card_compl_le_matchingNumber`
  (`c ≤ ν(F)`), `Fiber.matchingNumber_eq_of_maxIndep` (`ν(F) = n - a`, with the easy half of König
  `Ceiling.card_add_matchingNumber_le`), `Fiber.card_eq_independenceNumber` (`a = α(F)`; with
  `Zhang.independenceNumber_add_matchingNumber` this is König's `a + ν = n` again).
* `Fiber.card_le_card_biUnion_neighborFinset` (**forest expansion**): in a forest, a vertex set `W`
  all of whose vertices have degree at least 2 has at least `|W|` neighbours.  Proof: induction on
  `W`; a leaf of the induced forest on `W ∪ N(W)` (the package's `Occupation.exists_leafStem`) lies
  in `N(W)` and has exactly one neighbour `w ∈ W`; delete `w`.
* `Fiber.exists_saturating_matching_exposedLeaves` (**Lemma 2.2**): `μ` can be chosen so that every
  `a ∈ A \ μ(C)` has degree at most 1.

**Proof of Lemma 2.2 (differs from the return's alternating-path flip; same statement).**  One
application of Hall's theorem to the index set `C ⊔ D`, where `D` has `a - c` elements, each
allowed exactly the set `L` of the vertices of `A` of degree at most 1 (`v ∈ C` is allowed
`N_A(v)`).  Hall's condition: an index set without elements of `D` is Lemma 2.1's condition; an
index set `U ⊔ E` with `E ≠ ∅` needs `|U| + |E| ≤ |N_A(U) ∪ L|`, and `W = A \ (N_A(U) ∪ L)`
consists of vertices of degree at least 2 whose neighbours all lie in `C \ U`, so forest expansion
gives `|W| ≤ |C \ U|`, i.e. `|N_A(U) ∪ L| ≥ a - c + |U| ≥ |E| + |U|`.  The injection has `a`
values, all in `A`, so it hits all of `A`; a vertex of `A` missed by `μ(C)` is hit by an element
of `D`, hence lies in `L`.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean
namespace Fiber

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Hall's condition for `C` -/

omit [Fintype V] in
/-- For an independent `U` disjoint from a maximum independent set `A`, `|U| ≤ |N_A(U)|`: the set
`(A \ N_A(U)) ∪ U` is independent. -/
theorem card_le_card_biUnion_filter_adj_of_isIndepSet {A U : Finset V}
    (hA : G.IsIndepSet (A : Set V))
    (hmax : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ A.card)
    (hU : G.IsIndepSet (U : Set V)) (hUA : Disjoint U A) :
    U.card ≤ (U.biUnion (fun v => A.filter (G.Adj v))).card := by
  set N := U.biUnion (fun v => A.filter (G.Adj v)) with hN
  have hNA : N ⊆ A := by
    intro x hx
    rw [hN, Finset.mem_biUnion] at hx
    obtain ⟨v, -, hx⟩ := hx
    exact (Finset.mem_filter.mp hx).1
  have hmemN : ∀ {x u : V}, u ∈ U → x ∈ A → G.Adj u x → x ∈ N := by
    intro x u hu hx hux
    rw [hN, Finset.mem_biUnion]
    exact ⟨u, hu, Finset.mem_filter.mpr ⟨hx, hux⟩⟩
  have hind : G.IsIndepSet (((A \ N) ∪ U : Finset V) : Set V) := by
    intro x hx y hy hxy hadj
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff] at hx hy
    rcases hx with ⟨hxA, hxN⟩ | hxU <;> rcases hy with ⟨hyA, hyN⟩ | hyU
    · exact hA (Finset.mem_coe.mpr hxA) (Finset.mem_coe.mpr hyA) hxy hadj
    · exact hxN (hmemN hyU hxA hadj.symm)
    · exact hyN (hmemN hxU hyA hadj)
    · exact hU (Finset.mem_coe.mpr hxU) (Finset.mem_coe.mpr hyU) hxy hadj
  have hdisj : Disjoint (A \ N) U :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset hUA.symm
  have h1 := hmax _ hind
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hNA] at h1
  have h2 := Finset.card_le_card hNA
  omega

omit [Fintype V] in
/-- **Hall's condition for `C`** (Lemma 2.1 of the binomial-fiber return): in a forest, for a
maximum independent set `A` and every `U` disjoint from `A`, `|U| ≤ |N_A(U)|`.  The two colour
classes of `U` are independent, and their `A`-neighbourhoods are disjoint. -/
theorem card_le_card_biUnion_filter_adj (hG : G.IsAcyclic) {A U : Finset V}
    (hA : G.IsIndepSet (A : Set V))
    (hmax : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ A.card)
    (hUA : Disjoint U A) :
    U.card ≤ (U.biUnion (fun v => A.filter (G.Adj v))).card := by
  let col := hG.coloringTwo
  have hcol : ∀ {v w : V}, G.Adj v w → col v ≠ col w := fun h => col.valid h
  have key : ∀ p q : Fin 2, ¬ p = 0 → ¬ q = 0 → p = q := by decide
  set U₀ := U.filter (fun v => col v = 0) with hU₀
  set U₁ := U.filter (fun v => ¬ col v = 0) with hU₁
  have hi₀ : G.IsIndepSet (U₀ : Set V) := by
    intro x hx y hy _ hadj
    rw [Finset.mem_coe, hU₀, Finset.mem_filter] at hx hy
    exact hcol hadj (hx.2.trans hy.2.symm)
  have hi₁ : G.IsIndepSet (U₁ : Set V) := by
    intro x hx y hy _ hadj
    rw [Finset.mem_coe, hU₁, Finset.mem_filter] at hx hy
    exact hcol hadj (key _ _ hx.2 hy.2)
  have h₀ := card_le_card_biUnion_filter_adj_of_isIndepSet hA hmax hi₀
    (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hUA)
  have h₁ := card_le_card_biUnion_filter_adj_of_isIndepSet hA hmax hi₁
    (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hUA)
  have hdisj : Disjoint (U₀.biUnion (fun v => A.filter (G.Adj v)))
      (U₁.biUnion (fun v => A.filter (G.Adj v))) := by
    rw [Finset.disjoint_left]
    intro x hx₀ hx₁
    rw [Finset.mem_biUnion] at hx₀ hx₁
    obtain ⟨u, hu, hux⟩ := hx₀
    obtain ⟨w, hw, hwx⟩ := hx₁
    rw [hU₀, Finset.mem_filter] at hu
    rw [hU₁, Finset.mem_filter] at hw
    rw [Finset.mem_filter] at hux hwx
    have c1 : ¬ col x = 0 := by
      intro h
      exact hcol hux.2 (hu.2.trans h.symm)
    exact hcol hwx.2 (key _ _ hw.2 c1)
  have hsplit : U₀.card + U₁.card = U.card :=
    Finset.card_filter_add_card_filter_not (s := U) (fun v => col v = 0)
  have hsub : U₀.biUnion (fun v => A.filter (G.Adj v)) ∪ U₁.biUnion (fun v => A.filter (G.Adj v)) ⊆
      U.biUnion (fun v => A.filter (G.Adj v)) :=
    Finset.union_subset
      (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))
      (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h3
  omega

/-! ### Lemma 2.1 -/

/-- **Lemma 2.1 (saturating matching), general form.**  In a forest, for an independent set `A` of
maximum cardinality there is `μ`, injective on `C = Aᶜ`, with `μ v ∈ A` adjacent to `v` for every
`v ∈ C`. -/
theorem exists_saturating_matching_of_isAcyclic (hG : G.IsAcyclic) {A : Finset V}
    (hA : G.IsIndepSet (A : Set V))
    (hmax : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ A.card) :
    ∃ μ : V → V, Set.InjOn μ (Aᶜ : Finset V) ∧ ∀ v ∈ Aᶜ, μ v ∈ A ∧ G.Adj v (μ v) := by
  let t : {v : V // v ∈ Aᶜ} → Finset V := fun v => A.filter (G.Adj v.1)
  have hHall : ∀ s : Finset {v : V // v ∈ Aᶜ}, s.card ≤ (s.biUnion t).card := by
    intro s
    have hUA : Disjoint (s.image Subtype.val) A := by
      rw [Finset.disjoint_left]
      intro x hx hxA
      rw [Finset.mem_image] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact (Finset.mem_compl.mp y.2) hxA
    have h := card_le_card_biUnion_filter_adj hG hA hmax hUA
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.image_biUnion] at h
    exact h
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  refine ⟨fun v => if h : v ∈ Aᶜ then f ⟨v, h⟩ else v, ?_, ?_⟩
  · intro v hv w hw hvw
    rw [Finset.mem_coe] at hv hw
    simp only [dif_pos hv, dif_pos hw] at hvw
    exact congrArg Subtype.val (hfinj hvw)
  · intro v hv
    simp only [dif_pos hv]
    exact Finset.mem_filter.mp (hf ⟨v, hv⟩)

/-! ### The matching `{v μ(v)}` -/

/-- The matching `{v μ(v) : v ∈ Aᶜ}` of a saturating map `μ` (as a finset of edges). -/
def matchingOf (A : Finset V) (μ : V → V) : Finset (Sym2 V) :=
  (Aᶜ).image (fun v => s(v, μ v))

/-- The matching `{v μ(v)}` has `|Aᶜ|` edges. -/
theorem card_matchingOf {A : Finset V} {μ : V → V} (hμA : ∀ v ∈ Aᶜ, μ v ∈ A) :
    (matchingOf A μ).card = (Aᶜ).card := by
  unfold matchingOf
  apply Finset.card_image_of_injOn
  intro v hv w hw hvw
  rw [Finset.mem_coe] at hv hw
  simp only [Sym2.eq_iff] at hvw
  rcases hvw with ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exfalso
    apply Finset.mem_compl.mp hv
    rw [h]
    exact hμA w hw

omit [DecidableRel G.Adj] in
/-- The edges `v μ(v)` form a matching of `G` (the package's `Occupation.IsMatchingIn`). -/
theorem isMatchingIn_matchingOf {A : Finset V} {μ : V → V}
    (hinj : Set.InjOn μ (Aᶜ : Finset V)) (hμ : ∀ v ∈ Aᶜ, μ v ∈ A ∧ G.Adj v (μ v)) :
    Occupation.IsMatchingIn G Finset.univ (matchingOf A μ) := by
  refine ⟨fun e he => ?_, fun e he e' he' hee' => ?_⟩
  · unfold matchingOf at he
    rw [Finset.mem_image] at he
    obtain ⟨v, hv, rfl⟩ := he
    refine ⟨?_, fun a _ => Finset.mem_univ a⟩
    rw [SimpleGraph.mem_edgeSet]
    exact (hμ v hv).2
  · unfold matchingOf at he he'
    rw [Finset.mem_image] at he he'
    obtain ⟨v, hv, rfl⟩ := he
    obtain ⟨w, hw, rfl⟩ := he'
    have hvw : v ≠ w := by
      rintro rfl
      exact hee' rfl
    have hvA := Finset.mem_compl.mp hv
    have hwA := Finset.mem_compl.mp hw
    intro x hx hx'
    rw [Sym2.mem_iff] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h
    · exact hvw h
    · apply hvA
      rw [h]
      exact (hμ w hw).1
    · apply hwA
      rw [← h]
      exact (hμ v hv).1
    · exact hvw (hinj (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw) h)

/-! ### Forest expansion -/

/-- **Forest expansion.**  In a forest, a set `W` of vertices of degree at least 2 has at least
`|W|` neighbours: `|W| ≤ |N(W)|`, `N(W)` the set of the vertices adjacent to some vertex of `W`.
Induction on `W`: a leaf `ℓ` of the induced forest on `W ∪ N(W)` is not in `W` (degree at least 2),
so it lies in `N(W)` and its only neighbour there is some `w ∈ W`; deleting `w` removes `ℓ` from
`N(W)`. -/
theorem card_le_card_biUnion_neighborFinset (hG : G.IsAcyclic) (W : Finset V)
    (hdeg : ∀ w ∈ W, 2 ≤ G.degree w) :
    W.card ≤ (W.biUnion (fun w => G.neighborFinset w)).card := by
  induction W using Finset.strongInduction with
  | H W ih =>
    rcases W.eq_empty_or_nonempty with hW | hne
    · rw [hW, Finset.card_empty]
      exact Nat.zero_le _
    have hmemN : ∀ {x : V}, x ∈ W.biUnion (fun w => G.neighborFinset w) ↔ ∃ w ∈ W, G.Adj w x := by
      intro x
      simp only [Finset.mem_biUnion, SimpleGraph.mem_neighborFinset]
    have htwo : ∀ w ∈ W, ∃ x y, x ≠ y ∧ G.Adj w x ∧ G.Adj w y := by
      intro w hw
      have h := hdeg w hw
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at h
      obtain ⟨x, hx, y, hy, hxy⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset w).card)
      rw [SimpleGraph.mem_neighborFinset] at hx hy
      exact ⟨x, y, hxy, hx, hy⟩
    set N := W.biUnion (fun w => G.neighborFinset w) with hN
    set s := W ∪ N with hs
    have hsne : ∀ x ∈ s, (nbrsIn G s x).Nonempty := by
      intro x hx
      rw [hs, Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨y, -, -, hxy, -⟩ := htwo x hx
        exact ⟨y, mem_nbrsIn.mpr ⟨Finset.mem_union_right _ (hmemN.mpr ⟨x, hx, hxy⟩), hxy⟩⟩
      · obtain ⟨w, hw, hwx⟩ := hmemN.mp hx
        exact ⟨w, mem_nbrsIn.mpr ⟨Finset.mem_union_left _ hw, hwx.symm⟩⟩
    obtain ⟨v, -, ⟨ℓ, hℓ⟩, -⟩ :=
      Occupation.exists_leafStem hG hsne (hne.mono Finset.subset_union_left)
    obtain ⟨hℓv, hℓn⟩ := Occupation.mem_leavesAt.mp hℓ
    have hℓs : ℓ ∈ s := (mem_nbrsIn.mp hℓv).1
    -- the only neighbour of `ℓ` in `s` is `v`
    have honly : ∀ y ∈ s, G.Adj ℓ y → y = v := by
      intro y hy hadj
      have hy' : y ∈ nbrsIn G s ℓ := mem_nbrsIn.mpr ⟨hy, hadj⟩
      rw [hℓn, Finset.mem_singleton] at hy'
      exact hy'
    -- `ℓ` has degree at least 2 if it lies in `W`, so it lies in `N`
    have hℓW : ℓ ∉ W := by
      intro hℓW
      obtain ⟨x, y, hxy, hx, hy⟩ := htwo ℓ hℓW
      have hx' := honly x (Finset.mem_union_right _ (hmemN.mpr ⟨ℓ, hℓW, hx⟩)) hx
      have hy' := honly y (Finset.mem_union_right _ (hmemN.mpr ⟨ℓ, hℓW, hy⟩)) hy
      exact hxy (hx'.trans hy'.symm)
    have hℓN : ℓ ∈ N := by
      rw [hs, Finset.mem_union] at hℓs
      exact hℓs.resolve_left hℓW
    obtain ⟨w, hw, hwℓ⟩ := hmemN.mp hℓN
    have hwv : w = v := honly w (Finset.mem_union_left _ hw) hwℓ.symm
    -- delete `w`
    have ih' := ih (W.erase w) (Finset.erase_ssubset hw)
      (fun x hx => hdeg x (Finset.mem_of_mem_erase hx))
    have hsub : (W.erase w).biUnion (fun w => G.neighborFinset w) ⊆ N.erase ℓ := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨w', hw', hx⟩ := hx
      rw [SimpleGraph.mem_neighborFinset] at hx
      have hw'W := Finset.mem_of_mem_erase hw'
      refine Finset.mem_erase.mpr ⟨?_, hmemN.mpr ⟨w', hw'W, hx⟩⟩
      intro hxℓ
      rw [hxℓ] at hx
      exact Finset.ne_of_mem_erase hw'
        ((honly w' (Finset.mem_union_left _ hw'W) hx.symm).trans hwv.symm)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_add_one hℓN
    have h3 := Finset.card_erase_add_one hw
    omega

/-! ### Lemma 2.2 -/

/-- **Lemma 2.2 (exposed leaves), general form.**  In a forest, for an independent set `A` of
maximum cardinality, the map `μ` of Lemma 2.1 can be chosen so that every vertex of `A \ μ(Aᶜ)` has
degree at most 1.  (One application of Hall's theorem with `|A| - |Aᶜ|` extra indices, each allowed
the vertices of `A` of degree at most 1; Hall's condition from Lemma 2.1's and from forest
expansion.) -/
theorem exists_saturating_matching_exposedLeaves_of_isAcyclic (hG : G.IsAcyclic) {A : Finset V}
    (hA : G.IsIndepSet (A : Set V))
    (hmax : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ A.card) :
    ∃ μ : V → V, Set.InjOn μ (Aᶜ : Finset V) ∧ (∀ v ∈ Aᶜ, μ v ∈ A ∧ G.Adj v (μ v)) ∧
      ∀ a ∈ A \ (Aᶜ).image μ, G.degree a ≤ 1 := by
  have hca : (Aᶜ).card ≤ A.card := by
    obtain ⟨μ, hinj, hμ⟩ := exists_saturating_matching_of_isAcyclic hG hA hmax
    exact Finset.card_le_card_of_injOn μ
      (fun v hv => Finset.mem_coe.mpr (hμ v (Finset.mem_coe.mp hv)).1) hinj
  set L := A.filter (fun a => G.degree a ≤ 1) with hL
  set d := A.card - (Aᶜ).card with hd
  -- the index set `C ⊔ D`, `|D| = a - c`
  let t : {v : V // v ∈ Aᶜ} ⊕ Fin d → Finset V :=
    Sum.elim (fun v => A.filter (G.Adj v.1)) (fun _ => L)
  have htA : ∀ i, t i ⊆ A := by
    rintro (v | k)
    · exact Finset.filter_subset _ _
    · exact Finset.filter_subset _ _
  have hHall : ∀ s : Finset ({v : V // v ∈ Aᶜ} ⊕ Fin d), s.card ≤ (s.biUnion t).card := by
    intro s
    set U := s.toLeft.image Subtype.val with hU
    have hUc : U ⊆ Aᶜ := by
      intro x hx
      rw [hU, Finset.mem_image] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have hUA : Disjoint U A := by
      rw [Finset.disjoint_left]
      intro x hx hxA
      exact Finset.mem_compl.mp (hUc hx) hxA
    have hcardU : U.card = s.toLeft.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    set N := U.biUnion (fun v => A.filter (G.Adj v)) with hN
    have hHallC : U.card ≤ N.card := card_le_card_biUnion_filter_adj hG hA hmax hUA
    have hNA : N ⊆ A := by
      intro x hx
      rw [hN, Finset.mem_biUnion] at hx
      obtain ⟨v, -, hx⟩ := hx
      exact (Finset.mem_filter.mp hx).1
    have hNsub : N ⊆ s.biUnion t := by
      intro x hx
      rw [hN, Finset.mem_biUnion] at hx
      obtain ⟨u, hu, hx⟩ := hx
      rw [hU, Finset.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [Finset.mem_toLeft] at hv
      exact Finset.mem_biUnion.mpr ⟨Sum.inl v, hv, hx⟩
    have hsplit := Finset.card_toLeft_add_card_toRight (u := s)
    rcases s.toRight.eq_empty_or_nonempty with hR | ⟨k, hk⟩
    · -- no index from `D`: Lemma 2.1's condition
      rw [hR, Finset.card_empty] at hsplit
      have := Finset.card_le_card hNsub
      omega
    · -- an index from `D`: every vertex of `L` is available
      have hLsub : L ⊆ s.biUnion t := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨Sum.inr k, Finset.mem_toRight.mp hk, hx⟩
      have hRd : s.toRight.card ≤ d := by
        calc s.toRight.card ≤ Fintype.card (Fin d) := Finset.card_le_univ _
          _ = d := Fintype.card_fin d
      -- `W`: the vertices of `A` of degree at least 2 with no neighbour in `U`
      set W := A \ (N ∪ L) with hW
      have hNL : N ∪ L ⊆ A := Finset.union_subset hNA (Finset.filter_subset _ _)
      have hWcard : W.card + (N ∪ L).card = A.card := Finset.card_sdiff_add_card_eq_card hNL
      have hWdeg : ∀ w ∈ W, 2 ≤ G.degree w := by
        intro w hw
        rw [hW, Finset.mem_sdiff, Finset.mem_union, not_or, hL, Finset.mem_filter] at hw
        obtain ⟨hwA, -, hwL⟩ := hw
        by_contra hlt
        exact hwL ⟨hwA, by omega⟩
      have hWnbr : W.biUnion (fun w => G.neighborFinset w) ⊆ Aᶜ \ U := by
        intro x hx
        rw [Finset.mem_biUnion] at hx
        obtain ⟨w, hw, hwx⟩ := hx
        rw [SimpleGraph.mem_neighborFinset] at hwx
        rw [hW, Finset.mem_sdiff, Finset.mem_union, not_or] at hw
        obtain ⟨hwA, hwN, -⟩ := hw
        rw [Finset.mem_sdiff, Finset.mem_compl]
        refine ⟨fun hxA =>
          hA (Finset.mem_coe.mpr hwA) (Finset.mem_coe.mpr hxA) (G.ne_of_adj hwx) hwx,
          fun hxU => hwN ?_⟩
        rw [hN, Finset.mem_biUnion]
        exact ⟨x, hxU, Finset.mem_filter.mpr ⟨hwA, hwx.symm⟩⟩
      have hexp := card_le_card_biUnion_neighborFinset hG W hWdeg
      have h1 := Finset.card_le_card hWnbr
      rw [Finset.card_sdiff_of_subset hUc] at h1
      have h3 := Finset.card_le_card (Finset.union_subset hNsub hLsub)
      have h4 := Finset.card_le_card hUc
      omega
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  -- `f` has `a` values, all in `A`: it hits every vertex of `A`
  have himage : Finset.univ.image f = A := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact htA i (hf i)
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_sum,
        Fintype.card_coe, Fintype.card_fin]
      omega
  refine ⟨fun v => if h : v ∈ Aᶜ then f (Sum.inl ⟨v, h⟩) else v, ?_, ?_, ?_⟩
  · intro v hv w hw hvw
    rw [Finset.mem_coe] at hv hw
    simp only [dif_pos hv, dif_pos hw] at hvw
    have h := hfinj hvw
    simp only [Sum.inl.injEq, Subtype.mk.injEq] at h
    exact h
  · intro v hv
    simp only [dif_pos hv]
    exact Finset.mem_filter.mp (hf (Sum.inl ⟨v, hv⟩))
  · intro a ha
    rw [Finset.mem_sdiff, Finset.mem_image] at ha
    obtain ⟨haA, hnot⟩ := ha
    rw [← himage, Finset.mem_image] at haA
    obtain ⟨i, -, rfl⟩ := haA
    rcases i with v | k
    · exfalso
      exact hnot ⟨v.1, v.2, dif_pos v.2⟩
    · exact (Finset.mem_filter.mp (hf (Sum.inr k))).2

end General

/-! ### The statements for `FiniteForest` -/

section Forest

variable (F : FiniteForest) (A : Finset (Fin F.n))

/-- The hypotheses of Lemmas 2.1 and 2.2 are satisfiable: every finite forest (the empty one
included) has an independent set of maximum cardinality. -/
theorem exists_maxIndep : ∃ B : Finset (Fin F.n), F.graph.IsIndepSet (B : Set (Fin F.n)) ∧
    ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ B.card := by
  obtain ⟨t, ht⟩ := F.graph.exists_isNIndepSet_indepNum
  refine ⟨t, ht.isIndepSet, fun S hS => ?_⟩
  rw [ht.card_eq]
  exact hS.card_le_indepNum

/-- **Lemma 2.1 (saturating matching).**  For a finite forest `F` and an independent set `A` of
maximum cardinality, there is `μ`, injective on `C = Aᶜ`, with `μ v ∈ A` adjacent to `v` for every
`v ∈ C`. -/
theorem exists_saturating_matching (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card) :
    ∃ μ : Fin F.n → Fin F.n, Set.InjOn μ (Aᶜ : Finset (Fin F.n)) ∧
      ∀ v ∈ Aᶜ, μ v ∈ A ∧ F.graph.Adj v (μ v) := by
  classical
  exact exists_saturating_matching_of_isAcyclic F.isForest hA hmax

/-- `c ≤ a`: `μ` maps `C` injectively into `A`. -/
theorem card_compl_le_card (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card) :
    (Aᶜ).card ≤ A.card := by
  obtain ⟨μ, hinj, hμ⟩ := exists_saturating_matching F A hA hmax
  exact Finset.card_le_card_of_injOn μ
    (fun v hv => Finset.mem_coe.mpr (hμ v (Finset.mem_coe.mp hv)).1) hinj

/-- `c ≤ ν(F)`: the matching `{v μ(v) : v ∈ C}` has `c` edges. -/
theorem card_compl_le_matchingNumber (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card) :
    (Aᶜ).card ≤ matchingNumber F.graph := by
  classical
  obtain ⟨μ, hinj, hμ⟩ := exists_saturating_matching F A hA hmax
  have h := Occupation.le_nuIn (isMatchingIn_matchingOf hinj hμ)
  rw [card_matchingOf (fun v hv => (hμ v hv).1), Occupation.nuIn_univ] at h
  exact h

/-- **`ν(F) = n - a`** for a maximum independent set `A` (from `c ≤ ν` and the easy half of König,
`Ceiling.card_add_matchingNumber_le`). -/
theorem matchingNumber_eq_of_maxIndep (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card) :
    matchingNumber F.graph = F.n - A.card := by
  have h1 := Ceiling.card_add_matchingNumber_le F.graph A hA
  have h2 := card_compl_le_matchingNumber F A hA hmax
  have h3 : (Aᶜ).card = F.n - A.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  omega

/-- A maximum independent set has `independenceNumber F` elements (so `a = α(F)`, and
`Zhang.independenceNumber_add_matchingNumber` is `a + ν = n`). -/
theorem card_eq_independenceNumber (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card) :
    A.card = independenceNumber F := by
  unfold independenceNumber
  apply le_antisymm
  · exact hA.card_le_indepNum
  · obtain ⟨t, ht⟩ := F.graph.exists_isNIndepSet_indepNum
    rw [← ht.card_eq]
    exact hmax t ht.isIndepSet

/-- **Lemma 2.2 (exposed leaves).**  For a finite forest `F` and an independent set `A` of maximum
cardinality, the saturating map `μ` of Lemma 2.1 can be chosen so that every `a ∈ A \ μ(C)`,
`C = Aᶜ`, has degree at most 1 in `F` (the unmatched vertices of `A` are leaves or isolated). -/
theorem exists_saturating_matching_exposedLeaves [DecidableRel F.graph.Adj]
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card) :
    ∃ μ : Fin F.n → Fin F.n, Set.InjOn μ (Aᶜ : Finset (Fin F.n)) ∧
      (∀ v ∈ Aᶜ, μ v ∈ A ∧ F.graph.Adj v (μ v)) ∧
      ∀ a ∈ A \ (Aᶜ).image μ, F.graph.degree a ≤ 1 :=
  exists_saturating_matching_exposedLeaves_of_isAcyclic F.isForest hA hmax

end Forest

end Fiber
end Erdos993Lean
