module

public import Mathlib
public import Erdos993Lean.Fiber.Charges

/-!
# The subset-level count identities of the basic inventory relaxation

Source: the 29 Sep 2026 binomial-fiber return (see `Erdos993Lean/Fiber/Charges.lean`), Section 4:
subset availability (8), the edge-union payment (9) and the independent-pair extension
payment (10), each as an exact count identity whose remainder is a sum over the non-independent
`h`-subsets of `C`.

## Objects

For a simple graph `G` on `V` and finite vertex sets `J`, `C`:
* `edgesIn G J`: the edges of `G` inside `J`, as the 2-subsets of `J` that are not independent
  (`mem_edgesIn`: exactly the pairs `{x, y}` with `x, y ∈ J`, `x ~ y`);
  `edgeCount G J = e(G[J])` its cardinality.
* `dependentSubsets G C h`: the `h`-subsets of `C` that are not independent.
* `N_h = indepCount G C h` (the package's count of independent `h`-subsets of `C`),
  `e_C = edgeCount G C`, with `edgeCount_add_indepCount_two`: `e_C + N_2 = C(c, 2)`.

## Main results (all for `2 ≤ h`; the source states (9), (10) for `3 ≤ h ≤ c`)

* `card_dependentSubsets_add` (**(8)**): `|{J : |J| = h, J not independent}| + N_h = C(c, h)`.
* `sum_card_filter_powersetCard_two`: the double count behind (9) and (10): for any property `Q` of
  2-subsets, `Σ_{J ⊆ C, |J| = h} #{P ⊆ J : |P| = 2, Q P} = #{P ⊆ C : |P| = 2, Q P} C(c-2, h-2)`.
* `sum_edgeCount_sub_one_add`, `sum_edgeCount_sub_one`, `edgeUnion_nonneg` (**(9)**):
  `Σ_{J not independent} (e(G[J]) - 1) = N_h - C(c, h) + e_C C(c-2, h-2)`, `e_C = C(c, 2) - N_2`,
  hence `S^-_h = N_h - C(c, h) + e_C C(c-2, h-2) ≥ 0`.
* `sum_choose_two_sub_edgeCount_add`, `sum_choose_two_sub_edgeCount`, `pairExtension_nonneg`
  (**(10)**): `Σ_{J not independent} (C(h, 2) - e(G[J])) = C(c-2, h-2) N_2 - C(h, 2) N_h`,
  hence `S^+_h = C(c-2, h-2) N_2 - C(h, 2) N_h ≥ 0`.

No acyclicity is used.  Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean
namespace Fiber

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Objects -/

variable (G) in
/-- The edges of `G` inside `J`, as the 2-subsets of `J` that are not independent
(`mem_edgesIn`). -/
def edgesIn (J : Finset V) : Finset (Finset V) :=
  (J.powersetCard 2).filter (fun P => ¬ IsIndepFinset G P)

variable (G) in
/-- `e(G[J])`: the number of edges of `G` with both ends in `J`. -/
def edgeCount (J : Finset V) : ℕ :=
  (edgesIn G J).card

variable (G) in
/-- The `h`-subsets of `C` that are not independent. -/
def dependentSubsets (C : Finset V) (h : ℕ) : Finset (Finset V) :=
  (C.powersetCard h).filter (fun J => ¬ IsIndepFinset G J)

/-! ### Edges inside a set -/

/-- The members of `edgesIn G J` are exactly the pairs `{x, y}` with `x, y ∈ J` and `x ~ y`. -/
theorem mem_edgesIn {J P : Finset V} :
    P ∈ edgesIn G J ↔ ∃ x ∈ J, ∃ y ∈ J, G.Adj x y ∧ P = {x, y} := by
  unfold edgesIn
  rw [mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨⟨hPJ, hP2⟩, hP⟩
    unfold IsIndepFinset at hP
    push_neg at hP
    obtain ⟨v, hv, w, hw, hvw⟩ := hP
    refine ⟨v, hPJ hv, w, hPJ hw, hvw, ?_⟩
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      rw [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hv
      · exact hw
    · rw [hP2, card_pair (G.ne_of_adj hvw)]
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨⟨insert_subset hx (singleton_subset_iff.mpr hy), card_pair (G.ne_of_adj hxy)⟩, ?_⟩
    intro hind
    exact hind x (mem_insert_self x {y}) y (mem_insert_of_mem (mem_singleton_self y)) hxy

/-- `J` is independent iff it contains no edge. -/
theorem isIndepFinset_iff_edgeCount_eq_zero {J : Finset V} :
    IsIndepFinset G J ↔ edgeCount G J = 0 := by
  unfold edgeCount
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  constructor
  · intro hJ P hP
    obtain ⟨x, hx, y, hy, hxy, -⟩ := mem_edgesIn.mp hP
    exact hJ x hx y hy hxy
  · intro h x hx y hy hxy
    exact h {x, y} (mem_edgesIn.mpr ⟨x, hx, y, hy, hxy, rfl⟩)

omit [DecidableEq V] in
/-- The 2-subsets of `J` split into independent pairs and edges:
`#{independent pairs of J} + e(G[J]) = C(|J|, 2)`. -/
theorem card_indepPairs_add_edgeCount (J : Finset V) :
    ((J.powersetCard 2).filter (IsIndepFinset G)).card + edgeCount G J = J.card.choose 2 := by
  unfold edgeCount edgesIn
  rw [card_filter_add_card_filter_not, card_powersetCard]

omit [DecidableEq V] in
/-- `e_C + N_2 = C(c, 2)`, i.e. `e_C = C(c, 2) - N_2`. -/
theorem edgeCount_add_indepCount_two (C : Finset V) :
    edgeCount G C + indepCount G C 2 = C.card.choose 2 := by
  rw [← card_indepSubsets, add_comm]
  exact card_indepPairs_add_edgeCount C

omit [DecidableEq V] in
/-- **(8), subset availability**: `|{J ⊆ C : |J| = h, J not independent}| + N_h = C(c, h)`. -/
theorem card_dependentSubsets_add (C : Finset V) (h : ℕ) :
    (dependentSubsets G C h).card + indepCount G C h = C.card.choose h := by
  rw [← card_indepSubsets, add_comm]
  unfold dependentSubsets indepSubsets
  rw [card_filter_add_card_filter_not, card_powersetCard]

/-! ### The double count -/

/-- **Double counting pairs inside `h`-subsets.**  For any property `Q` of 2-subsets and `2 ≤ h`,
`Σ_{J ⊆ C, |J| = h} #{P ⊆ J : |P| = 2, Q P} = #{P ⊆ C : |P| = 2, Q P} C(c-2, h-2)`: each pair
of `C` lies in `C(c-2, h-2)` of the `h`-subsets. -/
theorem sum_card_filter_powersetCard_two (C : Finset V) (Q : Finset V → Prop) [DecidablePred Q]
    {h : ℕ} (h2 : 2 ≤ h) :
    ∑ J ∈ C.powersetCard h, ((J.powersetCard 2).filter Q).card =
      ((C.powersetCard 2).filter Q).card * (C.card - 2).choose (h - 2) := by
  have step1 : ∀ J ∈ C.powersetCard h, ((J.powersetCard 2).filter Q).card =
      ((C.powersetCard 2).filter (fun P => P ⊆ J ∧ Q P)).card := by
    intro J hJ
    rw [mem_powersetCard] at hJ
    congr 1
    ext P
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hPJ, hP2⟩, hQ⟩
      exact ⟨⟨hPJ.trans hJ.1, hP2⟩, hPJ, hQ⟩
    · rintro ⟨⟨_, hP2⟩, hPJ, hQ⟩
      exact ⟨⟨hPJ, hP2⟩, hQ⟩
  have hswap : ∑ J ∈ C.powersetCard h, ((C.powersetCard 2).filter (fun P => P ⊆ J ∧ Q P)).card =
      ∑ P ∈ C.powersetCard 2, ((C.powersetCard h).filter (fun J => P ⊆ J ∧ Q P)).card := by
    simp only [card_filter]
    exact sum_comm
  have step2 : ∀ P ∈ C.powersetCard 2,
      ((C.powersetCard h).filter (fun J => P ⊆ J ∧ Q P)).card =
        if Q P then (C.card - 2).choose (h - 2) else 0 := by
    intro P hP
    rw [mem_powersetCard] at hP
    by_cases hQ : Q P
    · rw [if_pos hQ]
      have h1 := card_powersetCard_filter_superset hP.1 (h := h) (by rw [hP.2]; exact h2)
      rw [hP.2] at h1
      rw [← h1]
      congr 1
      apply filter_congr
      intro J _
      exact and_iff_left hQ
    · rw [if_neg hQ, card_eq_zero, filter_eq_empty_iff]
      intro J _ hJ
      exact hQ hJ.2
  rw [sum_congr rfl step1, hswap, sum_congr rfl step2, ← sum_filter, sum_const, smul_eq_mul]

/-! ### (9): the edge-union payment -/

/-- The edges inside the `h`-subsets of `C`: `Σ_{J ⊆ C, |J| = h} e(G[J]) = e_C C(c-2, h-2)`. -/
theorem sum_edgeCount_powersetCard (C : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    ∑ J ∈ C.powersetCard h, edgeCount G J = edgeCount G C * (C.card - 2).choose (h - 2) := by
  unfold edgeCount edgesIn
  exact sum_card_filter_powersetCard_two C _ h2

/-- **(9), natural-number form**: `Σ_{J not independent} (e(G[J]) - 1) + C(c, h) =
N_h + e_C C(c-2, h-2)` (sum over the non-independent `h`-subsets `J` of `C`; the subtraction is
exact, every such `J` contains an edge). -/
theorem sum_edgeCount_sub_one_add (C : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    ∑ J ∈ dependentSubsets G C h, (edgeCount G J - 1) + C.card.choose h =
      indepCount G C h + edgeCount G C * (C.card - 2).choose (h - 2) := by
  have hsplit : ∑ J ∈ C.powersetCard h, edgeCount G J =
      ∑ J ∈ dependentSubsets G C h, edgeCount G J := by
    unfold dependentSubsets
    rw [← sum_filter_add_sum_filter_not (C.powersetCard h) (IsIndepFinset G)]
    have hzero : ∑ J ∈ (C.powersetCard h).filter (IsIndepFinset G), edgeCount G J = 0 := by
      apply sum_eq_zero
      intro J hJ
      exact isIndepFinset_iff_edgeCount_eq_zero.mp (mem_filter.mp hJ).2
    rw [hzero, zero_add]
  have hone : ∑ J ∈ dependentSubsets G C h, (edgeCount G J - 1) +
      (dependentSubsets G C h).card = ∑ J ∈ dependentSubsets G C h, edgeCount G J := by
    rw [card_eq_sum_ones, ← sum_add_distrib]
    apply sum_congr rfl
    intro J hJ
    simp only [dependentSubsets, mem_filter] at hJ
    have hpos : edgeCount G J ≠ 0 := fun h0 => hJ.2 (isIndepFinset_iff_edgeCount_eq_zero.mpr h0)
    omega
  rw [← card_dependentSubsets_add (G := G) C h, ← add_assoc, hone, ← hsplit,
    sum_edgeCount_powersetCard C h2, add_comm]

/-- **(9), the edge-union payment**: for `2 ≤ h`,
`Σ_{J not independent} (e(G[J]) - 1) = N_h - C(c, h) + e_C C(c-2, h-2)` with
`e_C = C(c, 2) - N_2` (in `ℤ`; the sum is over the non-independent `h`-subsets `J` of `C`). -/
theorem sum_edgeCount_sub_one (C : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    ∑ J ∈ dependentSubsets G C h, ((edgeCount G J : ℤ) - 1) =
      (indepCount G C h : ℤ) - (C.card.choose h : ℕ) +
        ((C.card.choose 2 : ℕ) - (indepCount G C 2 : ℤ)) * ((C.card - 2).choose (h - 2) : ℕ) := by
  have hcast : ∑ J ∈ dependentSubsets G C h, ((edgeCount G J : ℤ) - 1) =
      ((∑ J ∈ dependentSubsets G C h, (edgeCount G J - 1) : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro J hJ
    simp only [dependentSubsets, mem_filter] at hJ
    have hpos : 1 ≤ edgeCount G J :=
      Nat.one_le_iff_ne_zero.mpr (fun h0 => hJ.2 (isIndepFinset_iff_edgeCount_eq_zero.mpr h0))
    rw [Nat.cast_sub hpos, Nat.cast_one]
  have hNZ : ((∑ J ∈ dependentSubsets G C h, (edgeCount G J - 1) : ℕ) : ℤ) +
      (C.card.choose h : ℕ) =
        (indepCount G C h : ℤ) + (edgeCount G C : ℤ) * ((C.card - 2).choose (h - 2) : ℕ) := by
    exact_mod_cast sum_edgeCount_sub_one_add (G := G) C h2
  have heZ : (edgeCount G C : ℤ) = (C.card.choose 2 : ℕ) - (indepCount G C 2 : ℤ) := by
    rw [← edgeCount_add_indepCount_two (G := G) C, Nat.cast_add]
    ring
  rw [heZ] at hNZ
  rw [hcast]
  linear_combination hNZ

/-- **(9), nonnegativity**: `S^-_h = N_h - C(c, h) + (C(c, 2) - N_2) C(c-2, h-2) ≥ 0` for
`2 ≤ h`. -/
theorem edgeUnion_nonneg (C : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    0 ≤ (indepCount G C h : ℤ) - (C.card.choose h : ℕ) +
      ((C.card.choose 2 : ℕ) - (indepCount G C 2 : ℤ)) * ((C.card - 2).choose (h - 2) : ℕ) := by
  rw [← sum_edgeCount_sub_one C h2]
  apply sum_nonneg
  intro J hJ
  simp only [dependentSubsets, mem_filter] at hJ
  have hpos : 1 ≤ edgeCount G J :=
    Nat.one_le_iff_ne_zero.mpr (fun h0 => hJ.2 (isIndepFinset_iff_edgeCount_eq_zero.mpr h0))
  have : (1 : ℤ) ≤ edgeCount G J := by exact_mod_cast hpos
  linarith

/-! ### (10): the independent-pair extension payment -/

omit [DecidableEq V] in
/-- `e(G[J]) ≤ C(|J|, 2)`. -/
theorem edgeCount_le_choose_two (J : Finset V) : edgeCount G J ≤ J.card.choose 2 := by
  rw [← card_indepPairs_add_edgeCount (G := G) J]
  exact Nat.le_add_left _ _

/-- **(10), natural-number form**: `Σ_{J not independent} (C(h, 2) - e(G[J])) + C(h, 2) N_h =
C(c-2, h-2) N_2` (sum over the non-independent `h`-subsets `J` of `C`; the subtraction is exact). -/
theorem sum_choose_two_sub_edgeCount_add (C : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    ∑ J ∈ dependentSubsets G C h, (h.choose 2 - edgeCount G J) + h.choose 2 * indepCount G C h =
      (C.card - 2).choose (h - 2) * indepCount G C 2 := by
  have htot : ∑ J ∈ C.powersetCard h, ((J.powersetCard 2).filter (IsIndepFinset G)).card =
      indepCount G C 2 * (C.card - 2).choose (h - 2) := by
    rw [sum_card_filter_powersetCard_two C _ h2, ← card_indepSubsets]
    rfl
  have hJ2 : ∀ J ∈ C.powersetCard h,
      ((J.powersetCard 2).filter (IsIndepFinset G)).card = h.choose 2 - edgeCount G J := by
    intro J hJ
    rw [mem_powersetCard] at hJ
    have := card_indepPairs_add_edgeCount (G := G) J
    rw [hJ.2] at this
    omega
  have hindep : ∀ J ∈ indepSubsets G C h, h.choose 2 - edgeCount G J = h.choose 2 := by
    intro J hJ
    simp only [indepSubsets, mem_filter] at hJ
    rw [isIndepFinset_iff_edgeCount_eq_zero.mp hJ.2, Nat.sub_zero]
  have hsplit : ∑ J ∈ C.powersetCard h, (h.choose 2 - edgeCount G J) =
      ∑ J ∈ indepSubsets G C h, (h.choose 2 - edgeCount G J) +
        ∑ J ∈ dependentSubsets G C h, (h.choose 2 - edgeCount G J) :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [sum_congr rfl hJ2, hsplit, sum_congr rfl hindep, sum_const, smul_eq_mul,
    card_indepSubsets] at htot
  rw [mul_comm ((C.card - 2).choose (h - 2)), ← htot]
  ring

/-- **(10), the independent-pair extension payment**: for `2 ≤ h`,
`Σ_{J not independent} (C(h, 2) - e(G[J])) = C(c-2, h-2) N_2 - C(h, 2) N_h` (in `ℤ`; the sum is
over the non-independent `h`-subsets `J` of `C`). -/
theorem sum_choose_two_sub_edgeCount (C : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    ∑ J ∈ dependentSubsets G C h, ((h.choose 2 : ℕ) - (edgeCount G J : ℤ)) =
      ((C.card - 2).choose (h - 2) : ℕ) * (indepCount G C 2 : ℤ) -
        (h.choose 2 : ℕ) * (indepCount G C h : ℤ) := by
  have hcast : ∑ J ∈ dependentSubsets G C h, ((h.choose 2 : ℕ) - (edgeCount G J : ℤ)) =
      ((∑ J ∈ dependentSubsets G C h, (h.choose 2 - edgeCount G J) : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro J hJ
    simp only [dependentSubsets, mem_filter, mem_powersetCard] at hJ
    have hle : edgeCount G J ≤ h.choose 2 := by
      have := edgeCount_le_choose_two (G := G) J
      rwa [hJ.1.2] at this
    rw [Nat.cast_sub hle]
  have hNZ : ((∑ J ∈ dependentSubsets G C h, (h.choose 2 - edgeCount G J) : ℕ) : ℤ) +
      (h.choose 2 : ℕ) * (indepCount G C h : ℤ) =
        ((C.card - 2).choose (h - 2) : ℕ) * (indepCount G C 2 : ℤ) := by
    exact_mod_cast sum_choose_two_sub_edgeCount_add (G := G) C h2
  rw [hcast]
  linear_combination hNZ

/-- **(10), nonnegativity**: `S^+_h = C(c-2, h-2) N_2 - C(h, 2) N_h ≥ 0` for `2 ≤ h`. -/
theorem pairExtension_nonneg (C : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    0 ≤ ((C.card - 2).choose (h - 2) : ℕ) * (indepCount G C 2 : ℤ) -
      (h.choose 2 : ℕ) * (indepCount G C h : ℤ) := by
  rw [← sum_choose_two_sub_edgeCount C h2]
  apply sum_nonneg
  intro J hJ
  simp only [dependentSubsets, mem_filter, mem_powersetCard] at hJ
  have hle : edgeCount G J ≤ h.choose 2 := by
    have := edgeCount_le_choose_two (G := G) J
    rwa [hJ.1.2] at this
  have : (edgeCount G J : ℤ) ≤ (h.choose 2 : ℕ) := by exact_mod_cast hle
  linarith

end Fiber
end Erdos993Lean
