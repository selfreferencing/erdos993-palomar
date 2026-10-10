module

public import Mathlib
public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Zhang.Konig
public import Erdos993Lean.Zhang.Decomposition
public import Erdos993Lean.Zhang.CoefficientBounds

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

-- Fiber-floor package: the source imports `Erdos993Lean.Zhang.Finite60`,
-- which is not part of this package; this file only needs the modules below (no other change).

/-!
# Zhang's finite part, row soundness 1: edge counts, colourings, double counting

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Section 2.  Shared combinatorics for the proofs
of the row families of Section 2.9 (`Zhang/Rows/*.lean`), on finite vertex sets of one graph:

* `edgesIn G s`, `eIn G s`: the edges of `G[s]`, taken as the non-independent `2`-subsets of `s`,
  so that `indepCount_two_add_eIn` is `T_2 + e = C(v, 2)` (Zhang (12)).
* `eIn_insert`, `eIn_erase`: adding or deleting a vertex changes `e` by its degree in `s`;
  `eIn_union_indep`: `e(A ∪ B) = e(A) + Σ_{b ∈ B} |N_A(b)|` for an independent `B` disjoint
  from `A`.
* `eIn_lt_card`: the **forest edge bound** `e(G[s]) < |s|` for a nonempty `s` of an acyclic
  graph (isolated-vertex / leaf induction, `Occupation.exists_leafStem`).
* `not_adj_of_adj_adj`: an acyclic graph has no triangles; `card_le_two_mul_alphaIn`:
  `|s| ≤ 2 α(G[s])`; `exists_colorClass`: when `2 α(G[s]) = |s|`, the colour class of any vertex
  (Mathlib's `IsAcyclic.coloringTwo`) is a maximum independent set with independent complement.
* `indepSets G Y j` (the independent `j`-subsets of `Y`), `extIn G S K` (the extensions of `K`
  inside `S`), and `sum_sum_erase`, **the reverse count**
  `Σ_{J} Σ_{u ∈ J} f(J − u) = Σ_{K} ext(K) f(K)` (independent `(r+1)`- and `r`-subsets), with its
  upper form `sum_sum_erase_le` (`ext(K) ≤ |S| − r`) and lower form `le_sum_sum_erase`;
  `succ_mul_indepCount_le`: `(r + 1) i_{r+1}(S) ≤ (|S| − r) i_r(S)`.
* `card_sdiff_le_extIn_add_eIn`: `|S \ K| ≤ ext(K) + e(G[S])` (a non-extending vertex has an edge
  into `K`); `card_nonindep_le`: at most `e(G[S]) C(|S| − 2, r − 2)` of the `r`-subsets of `S` are
  not independent (union bound over edges).

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Edges inside a vertex set -/

variable (G) in
/-- The edges of `G[s]`, as the non-independent `2`-subsets of `s`. -/
def edgesIn (s : Finset V) : Finset (Finset V) :=
  (s.powersetCard 2).filter (fun p => ¬ IsIndepFinset G p)

variable (G) in
/-- `e(G[s])`: the number of edges of the subgraph induced on `s`. -/
def eIn (s : Finset V) : ℕ := (edgesIn G s).card

omit [DecidableEq V] in
theorem mem_edgesIn {s p : Finset V} :
    p ∈ edgesIn G s ↔ p ⊆ s ∧ p.card = 2 ∧ ¬ IsIndepFinset G p := by
  unfold edgesIn
  rw [mem_filter, mem_powersetCard, and_assoc]

omit [DecidableEq V] in
theorem indepCount_eq_card_filter (s : Finset V) (k : ℕ) :
    indepCount G s k = ((s.powersetCard k).filter (IsIndepFinset G)).card := by
  unfold indepCount
  congr 1
  ext t
  simp only [mem_filter, mem_powerset, mem_powersetCard]
  tauto

omit [DecidableEq V] in
/-- `T_2 + e = C(v, 2)`: a `2`-subset is independent unless it is an edge. -/
theorem indepCount_two_add_eIn (s : Finset V) : indepCount G s 2 + eIn G s = s.card.choose 2 := by
  rw [indepCount_eq_card_filter, eIn, edgesIn, card_filter_add_card_filter_not,
    card_powersetCard]

omit [DecidableEq V] in
theorem eIn_eq_zero_of_indep {t : Finset V} (ht : IsIndepFinset G t) : eIn G t = 0 := by
  unfold eIn edgesIn
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp hnp
  exact hnp (isIndepFinset_mono ht (mem_powersetCard.mp hp).1)

omit [DecidableEq V] in
theorem eIn_empty : eIn G (∅ : Finset V) = 0 := eIn_eq_zero_of_indep isIndepFinset_empty

/-- Adding a vertex `x` adds its neighbours in `s` to the edge count. -/
theorem eIn_insert {s : Finset V} {x : V} (hx : x ∉ s) :
    eIn G (insert x s) = eIn G s + (nbrsIn G s x).card := by
  have h1 := indepCount_two_add_eIn (G := G) (insert x s)
  have h2 := indepCount_two_add_eIn (G := G) s
  have h3 := indepCount_succ_erase (G := G) (mem_insert_self x s) 1
  rw [erase_insert hx, show (1 : ℕ) + 1 = 2 from rfl] at h3
  have h4 : outsideClosedNbhd G (insert x s) x = s.filter (fun w => ¬ G.Adj x w) := by
    ext w
    simp only [outsideClosedNbhd, mem_filter, mem_insert]
    constructor
    · rintro ⟨hw | hw, hne, hadj⟩
      · exact absurd hw hne
      · exact ⟨hw, hadj⟩
    · rintro ⟨hw, hadj⟩
      exact ⟨Or.inr hw, fun h => hx (h ▸ hw), hadj⟩
  rw [h4, indepCount_one] at h3
  have h5 := card_filter_add_card_filter_not (s := s) (fun w => G.Adj x w)
  have h6 : nbrsIn G s x = s.filter (fun w => G.Adj x w) := rfl
  have h7 : (s.card + 1).choose 2 = s.card.choose 1 + s.card.choose 2 :=
    Nat.choose_succ_succ' s.card 1
  rw [card_insert_of_notMem hx, h7, Nat.choose_one_right] at h1
  rw [h6]
  omega

theorem nbrsIn_erase_self (s : Finset V) (x : V) : nbrsIn G (s.erase x) x = nbrsIn G s x := by
  ext w
  simp only [mem_nbrsIn, mem_erase]
  constructor
  · rintro ⟨⟨-, hw⟩, hadj⟩
    exact ⟨hw, hadj⟩
  · rintro ⟨hw, hadj⟩
    exact ⟨⟨(G.ne_of_adj hadj).symm, hw⟩, hadj⟩

/-- Deleting a vertex `x ∈ s` removes its neighbours in `s` from the edge count. -/
theorem eIn_erase {s : Finset V} {x : V} (hx : x ∈ s) :
    eIn G s = eIn G (s.erase x) + (nbrsIn G s x).card := by
  have h := eIn_insert (G := G) (notMem_erase x s)
  rwa [insert_erase hx, nbrsIn_erase_self] at h

/-- **Forest edge bound**: a nonempty vertex set of an acyclic graph spans fewer edges than
vertices. -/
theorem eIn_lt_card (hG : G.IsAcyclic) {s : Finset V} (hs : s.Nonempty) : eIn G s < s.card := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hiso : ∃ x ∈ s, nbrsIn G s x = ∅
    · obtain ⟨x, hx, hxn⟩ := hiso
      rw [eIn_erase hx, hxn, card_empty, add_zero]
      have hc := card_erase_add_one hx
      rcases (s.erase x).eq_empty_or_nonempty with he | he
      · rw [he, eIn_empty]
        omega
      · have := ih _ (erase_ssubset hx) he
        omega
    · push_neg at hiso
      obtain ⟨w, hw, ⟨ℓ, hℓ⟩, -⟩ := Occupation.exists_leafStem hG hiso hs
      obtain ⟨hℓN, hℓn⟩ := Occupation.mem_leavesAt.mp hℓ
      have hℓs : ℓ ∈ s := (mem_nbrsIn.mp hℓN).1
      have hwℓ : w ≠ ℓ := G.ne_of_adj (mem_nbrsIn.mp hℓN).2
      rw [eIn_erase hℓs, hℓn, card_singleton]
      have hne : (s.erase ℓ).Nonempty := ⟨w, mem_erase.mpr ⟨hwℓ, hw⟩⟩
      have := ih _ (erase_ssubset hℓs) hne
      have := card_erase_add_one hℓs
      omega

theorem eIn_le_card_sub_one (hG : G.IsAcyclic) (s : Finset V) : eIn G s ≤ s.card - 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [eIn_empty]
    exact Nat.zero_le _
  · have := eIn_lt_card hG hs
    omega

/-- Edges of `A ∪ B` for an independent `B` disjoint from `A`: `e(A ∪ B) = e(A) + Σ_b |N_A(b)|`. -/
theorem eIn_union_indep {A B : Finset V} (hAB : Disjoint A B) (hB : IsIndepFinset G B) :
    eIn G (A ∪ B) = eIn G A + ∑ b ∈ B, (nbrsIn G A b).card := by
  induction B using Finset.induction_on with
  | empty => rw [union_empty, sum_empty, add_zero]
  | @insert b B hb ih =>
    have hB' : IsIndepFinset G B := isIndepFinset_mono hB (subset_insert b B)
    have hAB' : Disjoint A B := disjoint_of_subset_right (subset_insert b B) hAB
    have hbA : b ∉ A := fun h => disjoint_left.mp hAB h (mem_insert_self b B)
    have hbAB : b ∉ A ∪ B := by
      rw [mem_union]
      rintro (h | h)
      · exact hbA h
      · exact hb h
    rw [union_insert, eIn_insert hbAB, ih hAB' hB', sum_insert hb]
    have hN : nbrsIn G (A ∪ B) b = nbrsIn G A b := by
      ext y
      simp only [mem_nbrsIn, mem_union]
      constructor
      · rintro ⟨hy | hy, hadj⟩
        · exact ⟨hy, hadj⟩
        · exact absurd hadj (hB b (mem_insert_self b B) y (mem_insert_of_mem hy))
      · rintro ⟨hy, hadj⟩
        exact ⟨Or.inl hy, hadj⟩
    rw [hN]
    ring

/-! ### Triangles and two-colourings -/

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- An acyclic graph has no triangles. -/
theorem not_adj_of_adj_adj (hG : G.IsAcyclic) {i y z : V} (hiy : G.Adj i y) (hiz : G.Adj i z)
    (hyz : G.Adj y z) : False := by
  have h := IsAcyclic.eq_of_adj_of_walk hG hiy hiz
    (SimpleGraph.Walk.cons hyz.symm SimpleGraph.Walk.nil) (by
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨G.ne_of_adj hiz, G.ne_of_adj hiy⟩)
  exact G.ne_of_adj hyz h

theorem fin_two_eq_of_ne {a b c : Fin 2} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

omit [DecidableEq V] in
/-- `|s| ≤ 2 α(G[s])` for an acyclic graph (a colour class has at least half the vertices). -/
theorem card_le_two_mul_alphaIn (hG : G.IsAcyclic) (s : Finset V) : s.card ≤ 2 * alphaIn G s := by
  set c := hG.coloringTwo
  have h1 : IsIndepFinset G (s.filter (fun y => c y = 0)) := by
    intro u hu w hw hadj
    exact c.valid hadj ((mem_filter.mp hu).2.trans (mem_filter.mp hw).2.symm)
  have h2 : IsIndepFinset G (s.filter (fun y => ¬ c y = 0)) := by
    intro u hu w hw hadj
    exact c.valid hadj (fin_two_eq_of_ne (mem_filter.mp hu).2 (mem_filter.mp hw).2)
  have h3 := le_alphaIn (filter_subset _ s) h1
  have h4 := le_alphaIn (filter_subset _ s) h2
  have h5 := card_filter_add_card_filter_not (s := s) (fun y => c y = 0)
  omega

/-- If `2 α(G[s]) = |s|`, the colour class of any vertex is a maximum independent set of `s`
with an independent complement. -/
theorem exists_colorClass (hG : G.IsAcyclic) (s : Finset V) (hs : 2 * alphaIn G s = s.card)
    (x : V) :
    ∃ I ⊆ s, IsIndepFinset G I ∧ I.card = alphaIn G s ∧ IsIndepFinset G (s \ I) ∧
      (x ∈ s → x ∈ I) := by
  set c := hG.coloringTwo
  have hA : IsIndepFinset G (s.filter (fun y => c y = c x)) := by
    intro u hu w hw hadj
    exact c.valid hadj ((mem_filter.mp hu).2.trans (mem_filter.mp hw).2.symm)
  have hB : IsIndepFinset G (s.filter (fun y => ¬ c y = c x)) := by
    intro u hu w hw hadj
    exact c.valid hadj (fin_two_eq_of_ne (mem_filter.mp hu).2 (mem_filter.mp hw).2)
  have hBeq : s \ s.filter (fun y => c y = c x) = s.filter (fun y => ¬ c y = c x) := by
    ext y
    simp only [mem_sdiff, mem_filter]
    tauto
  refine ⟨s.filter (fun y => c y = c x), filter_subset _ _, hA, ?_, ?_, ?_⟩
  · have h3 := le_alphaIn (filter_subset _ s) hA
    have h4 := le_alphaIn (filter_subset _ s) hB
    have h5 := card_filter_add_card_filter_not (s := s) (fun y => c y = c x)
    omega
  · rw [hBeq]
    exact hB
  · intro hx
    exact mem_filter.mpr ⟨hx, rfl⟩

/-! ### Independent `j`-subsets, extensions and deletions -/

variable (G) in
/-- The independent `j`-subsets of `Y`. -/
def indepSets (Y : Finset V) (j : ℕ) : Finset (Finset V) :=
  (Y.powersetCard j).filter (IsIndepFinset G)

omit [DecidableEq V] in
theorem mem_indepSets {Y J : Finset V} {j : ℕ} :
    J ∈ indepSets G Y j ↔ J ⊆ Y ∧ J.card = j ∧ IsIndepFinset G J := by
  unfold indepSets
  rw [mem_filter, mem_powersetCard, and_assoc]

omit [DecidableEq V] in
theorem indepCount_eq_card_indepSets (Y : Finset V) (j : ℕ) :
    indepCount G Y j = (indepSets G Y j).card :=
  indepCount_eq_card_filter Y j

variable (G) in
/-- The vertices of `S \ K` that extend `K` to a larger independent set. -/
def extIn (S K : Finset V) : Finset V :=
  (S \ K).filter (fun u => IsIndepFinset G (insert u K))

omit [DecidableRel G.Adj] in
theorem isIndepFinset_insert {K : Finset V} {u : V} (hK : IsIndepFinset G K)
    (hu : ∀ k ∈ K, ¬ G.Adj u k) : IsIndepFinset G (insert u K) := by
  intro a ha b hb hab
  rw [mem_insert] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb] at hab
    exact G.irrefl hab
  · rw [ha] at hab
    exact hu b hb hab
  · rw [hb] at hab
    exact hu a ha hab.symm
  · exact hK a ha b hb hab

/-- **Double counting of deletions** (the reverse count of Lemmas 2.3, 2.6, 2.7):
`Σ_{J} Σ_{u ∈ J} f(J − u) = Σ_{K} ext(K) f(K)`, over the independent `(r+1)`- and `r`-subsets
of `S`. -/
theorem sum_sum_erase (S : Finset V) (r : ℕ) (f : Finset V → ℚ) :
    ∑ J ∈ indepSets G S (r + 1), ∑ u ∈ J, f (J.erase u) =
      ∑ K ∈ indepSets G S r, ((extIn G S K).card : ℚ) * f K := by
  have hR : ∀ K ∈ indepSets G S r,
      ((extIn G S K).card : ℚ) * f K = ∑ _u ∈ extIn G S K, f K := by
    intro K _
    rw [sum_const, nsmul_eq_mul]
  rw [sum_congr rfl hR, sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.1.erase x.2, x.2⟩) (fun y _ => ⟨insert y.2 y.1, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨J, u⟩ hx
    rw [mem_sigma] at hx ⊢
    obtain ⟨hJ, hu⟩ := hx
    obtain ⟨hJS, hJc, hJi⟩ := mem_indepSets.mp hJ
    refine ⟨mem_indepSets.mpr ⟨(erase_subset u J).trans hJS, ?_,
      isIndepFinset_mono hJi (erase_subset u J)⟩, ?_⟩
    · rw [card_erase_of_mem hu, hJc]
      rfl
    · unfold extIn
      rw [mem_filter, mem_sdiff, insert_erase hu]
      exact ⟨⟨hJS hu, notMem_erase u J⟩, hJi⟩
  · rintro ⟨K, u⟩ hy
    rw [mem_sigma] at hy ⊢
    obtain ⟨hK, hu⟩ := hy
    obtain ⟨hKS, hKc, -⟩ := mem_indepSets.mp hK
    unfold extIn at hu
    rw [mem_filter, mem_sdiff] at hu
    obtain ⟨⟨huS, huK⟩, hind⟩ := hu
    exact ⟨mem_indepSets.mpr ⟨insert_subset huS hKS, by rw [card_insert_of_notMem huK, hKc],
      hind⟩, mem_insert_self u K⟩
  · rintro ⟨J, u⟩ hx
    rw [mem_sigma] at hx
    simp only [insert_erase hx.2]
  · rintro ⟨K, u⟩ hy
    rw [mem_sigma] at hy
    have huK : u ∉ K := by
      have := hy.2
      unfold extIn at this
      exact (mem_sdiff.mp (mem_filter.mp this).1).2
    simp only [erase_insert huK]
  · rintro ⟨J, u⟩ _
    rfl

/-- Upper form: every independent `r`-set has at most `|S| − r` extensions. -/
theorem sum_sum_erase_le (S : Finset V) (r : ℕ) (f : Finset V → ℚ)
    (hf : ∀ K ∈ indepSets G S r, 0 ≤ f K) :
    ∑ J ∈ indepSets G S (r + 1), ∑ u ∈ J, f (J.erase u) ≤
      ((S.card : ℚ) - r) * ∑ K ∈ indepSets G S r, f K := by
  rw [sum_sum_erase, mul_sum]
  apply sum_le_sum
  intro K hK
  apply mul_le_mul_of_nonneg_right _ (hf K hK)
  obtain ⟨hKS, hKc, -⟩ := mem_indepSets.mp hK
  have h1 : (extIn G S K).card ≤ (S \ K).card := card_le_card (filter_subset _ _)
  have h2 : (S \ K).card + K.card = S.card := card_sdiff_add_card_eq_card hKS
  have h3 : (extIn G S K).card + r ≤ S.card := by omega
  have h4 : ((extIn G S K).card : ℚ) + r ≤ S.card := by exact_mod_cast h3
  linarith

/-- Lower form: a uniform lower bound `c` on the number of extensions. -/
theorem le_sum_sum_erase (S : Finset V) (r : ℕ) (f : Finset V → ℚ) (c : ℚ)
    (hf : ∀ K ∈ indepSets G S r, 0 ≤ f K)
    (hc : ∀ K ∈ indepSets G S r, c ≤ (extIn G S K).card) :
    c * ∑ K ∈ indepSets G S r, f K ≤ ∑ J ∈ indepSets G S (r + 1), ∑ u ∈ J, f (J.erase u) := by
  rw [sum_sum_erase, mul_sum]
  exact sum_le_sum fun K hK => mul_le_mul_of_nonneg_right (hc K hK) (hf K hK)

/-- The down-up inequality `(r + 1) i_{r+1}(S) ≤ (|S| − r) i_r(S)`. -/
theorem succ_mul_indepCount_le (S : Finset V) (r : ℕ) :
    ((r : ℚ) + 1) * indepCount G S (r + 1) ≤ ((S.card : ℚ) - r) * indepCount G S r := by
  have h := sum_sum_erase_le (G := G) S r (fun _ => (1 : ℚ)) (fun _ _ => zero_le_one)
  simp only [sum_const, nsmul_eq_mul, mul_one] at h
  rw [indepCount_eq_card_indepSets, indepCount_eq_card_indepSets]
  have h2 : ∑ J ∈ indepSets G S (r + 1), (J.card : ℚ) =
      ((r : ℚ) + 1) * (indepSets G S (r + 1)).card := by
    rw [sum_congr rfl (fun J hJ => by
      rw [(mem_indepSets.mp hJ).2.1]), sum_const, nsmul_eq_mul]
    push_cast
    ring
  linarith

/-- **Forbidden extensions are paid by edges**: `|S \ K| ≤ ext(K) + e(G[S])` for an independent
`K ⊆ S` (each non-extending vertex has an edge into `K`, and these edges are distinct). -/
theorem card_sdiff_le_extIn_add_eIn {S K : Finset V} (hKS : K ⊆ S) (hK : IsIndepFinset G K) :
    (S \ K).card ≤ (extIn G S K).card + eIn G S := by
  set B := (S \ K).filter (fun u => ¬ IsIndepFinset G (insert u K)) with hB
  have h1 : (extIn G S K).card + B.card = (S \ K).card :=
    card_filter_add_card_filter_not _
  have h2 : B.card ≤ eIn G S := by
    set P := (B ×ˢ K).filter (fun q => G.Adj q.1 q.2) with hP
    have h3 : B ⊆ P.image Prod.fst := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := mem_filter.mp hu
      have : ∃ k ∈ K, G.Adj u k := by
        by_contra hcon
        push_neg at hcon
        exact hu2 (isIndepFinset_insert hK hcon)
      obtain ⟨k, hk, hadj⟩ := this
      exact mem_image.mpr ⟨(u, k), mem_filter.mpr ⟨mem_product.mpr ⟨hu, hk⟩, hadj⟩, rfl⟩
    have h4 : P.card ≤ eIn G S := by
      unfold eIn
      apply card_le_card_of_injOn (fun q => ({q.1, q.2} : Finset V))
      · intro q hq
        obtain ⟨hq1, hadj⟩ := mem_filter.mp (mem_coe.mp hq)
        obtain ⟨hqB, hqK⟩ := mem_product.mp hq1
        have hqS : q.1 ∈ S := (mem_sdiff.mp (mem_filter.mp hqB).1).1
        rw [mem_coe, mem_edgesIn]
        refine ⟨insert_subset hqS (singleton_subset_iff.mpr (hKS hqK)),
          card_pair (G.ne_of_adj hadj), ?_⟩
        intro hind
        exact hind q.1 (mem_insert_self _ _) q.2 (mem_insert_of_mem (mem_singleton_self _)) hadj
      · intro q hq q' hq' heq
        obtain ⟨hq1, -⟩ := mem_filter.mp (mem_coe.mp hq)
        obtain ⟨hq1', -⟩ := mem_filter.mp (mem_coe.mp hq')
        obtain ⟨hqB, hqK⟩ := mem_product.mp hq1
        obtain ⟨hqB', hqK'⟩ := mem_product.mp hq1'
        have hnK : q.1 ∉ K := (mem_sdiff.mp (mem_filter.mp hqB).1).2
        have hnK' : q'.1 ∉ K := (mem_sdiff.mp (mem_filter.mp hqB').1).2
        simp only at heq
        have e1 : q.1 ∈ ({q'.1, q'.2} : Finset V) := heq ▸ mem_insert_self _ _
        have e2 : q.2 ∈ ({q'.1, q'.2} : Finset V) :=
          heq ▸ mem_insert_of_mem (mem_singleton_self _)
        rw [mem_insert, mem_singleton] at e1 e2
        have f1 : q.1 = q'.1 := by
          rcases e1 with h | h
          · exact h
          · exact absurd (h ▸ hqK') hnK
        have f2 : q.2 = q'.2 := by
          rcases e2 with h | h
          · exact absurd (h ▸ hqK) hnK'
          · exact h
        exact Prod.ext f1 f2
    exact (card_le_card h3).trans (card_image_le.trans h4)
  omega

/-- **Union bound over edges**: at most `e(G[S]) C(|S| − 2, r − 2)` of the `r`-subsets of `S` are
not independent. -/
theorem card_nonindep_le (S : Finset V) (r : ℕ) :
    ((S.powersetCard r).filter (fun J => ¬ IsIndepFinset G J)).card ≤
      eIn G S * (S.card - 2).choose (r - 2) := by
  have hsub : (S.powersetCard r).filter (fun J => ¬ IsIndepFinset G J) ⊆
      (edgesIn G S).biUnion (fun P => (S.powersetCard r).filter (fun J => P ⊆ J)) := by
    intro J hJ
    obtain ⟨hJp, hJn⟩ := mem_filter.mp hJ
    have hJS := (mem_powersetCard.mp hJp).1
    have : ∃ a ∈ J, ∃ b ∈ J, G.Adj a b := by
      by_contra hcon
      push_neg at hcon
      exact hJn (fun a ha b hb => hcon a ha b hb)
    obtain ⟨a, ha, b, hb, hab⟩ := this
    rw [mem_biUnion]
    refine ⟨{a, b}, ?_, mem_filter.mpr ⟨hJp, insert_subset ha (singleton_subset_iff.mpr hb)⟩⟩
    rw [mem_edgesIn]
    refine ⟨insert_subset (hJS ha) (singleton_subset_iff.mpr (hJS hb)),
      card_pair (G.ne_of_adj hab), ?_⟩
    intro hind
    exact hind a (mem_insert_self _ _) b (mem_insert_of_mem (mem_singleton_self _)) hab
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [eIn, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro P hP
  obtain ⟨hPS, hPc, -⟩ := mem_edgesIn.mp hP
  have h := card_le_card_of_injOn (fun J => J \ P)
    (s := (S.powersetCard r).filter (fun J => P ⊆ J)) (t := (S \ P).powersetCard (r - 2)) ?_ ?_
  · rwa [card_powersetCard, card_sdiff_of_subset hPS, hPc] at h
  · intro J hJ
    obtain ⟨hJp, hPJ⟩ := mem_filter.mp (mem_coe.mp hJ)
    obtain ⟨hJS, hJc⟩ := mem_powersetCard.mp hJp
    rw [mem_coe, mem_powersetCard]
    exact ⟨sdiff_subset_sdiff hJS subset_rfl, by rw [card_sdiff_of_subset hPJ, hJc, hPc]⟩
  · intro J hJ J' hJ' heq
    have hPJ := (mem_filter.mp (mem_coe.mp hJ)).2
    have hPJ' := (mem_filter.mp (mem_coe.mp hJ')).2
    simp only at heq
    rw [← sdiff_union_of_subset hPJ, ← sdiff_union_of_subset hPJ', heq]

end General

end Rows
end Zhang
end Erdos993Lean
