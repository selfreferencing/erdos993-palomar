module

public import Mathlib
public import Erdos993Lean.Fiber.Counts

/-!
# The matching-excess row and the count identities in the inventory variables `N[y, m]`

Source: the 29 Sep 2026 binomial-fiber return (see `Erdos993Lean/Fiber/Charges.lean`), Sections 1,
3 and 4.  The source states Theorem 3.1 and the identities (8)-(10) as linear rows on the inventory
`N[y, m] = #{J ⊆ C independent : |J| = y, |A \ N_A(J)| = m}`; this is T. Zhang's `t_{y,m}`,
`Zhang.tCount G s I y m` with `I = A` and `s \ I = C` (`Erdos993Lean/Zhang/Decomposition.lean`).
This file rewrites the objects of `Charges.lean` and `Counts.lean` in these variables.

## Main results (`a = |I|`, `c = |s \ I|`, sums over `m ∈ range (a + 1)`)

* `sum_mul_tCount`: `Σ_m g(m) N[y, m] = Σ_J g(m(J))` over the independent `y`-subsets of `s \ I`.
* `blockerCharge_eq_sum_tCount`: `R_h = Σ_m (a - m - h) N[h, m]`.
* `card_crossEdges_eq_sum_tCount`: `D = Σ_m (a - m) N[1, m]` (singleton fibers).
* `blockerCharge_le_inventory` (**Theorem 3.1 as an inventory row**):
  `Σ_m (a - m - h) N[h, m] ≤ (Σ_m (a - m) N[1, m] - c) C(c-2, h-1) + (a - c) C(c-2, h-2)`.
* `edgeUnion_nonneg_inventory` (**(9)**), `pairExtension_nonneg_inventory` (**(10)**), with
  `N_h = Σ_m N[h, m]` (`Zhang.sum_tCount`).

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean
namespace Fiber

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Fiberwise sums**: `Σ_{m ≤ a} g(m) N[y, m] = Σ_J g(|A \ N_A(J)|)`, the sum over the
independent `y`-subsets `J` of `s \ I` (`A = I`). -/
theorem sum_mul_tCount (s I : Finset V) (y : ℕ) (g : ℕ → ℕ) :
    ∑ m ∈ range (I.card + 1), g m * Zhang.tCount G s I y m =
      ∑ J ∈ indepSubsets G (s \ I) y, g (Zhang.avail G I J).card := by
  have hmaps : ∀ J ∈ indepSubsets G (s \ I) y, (Zhang.avail G I J).card ∈ range (I.card + 1) := by
    intro J _
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (Zhang.avail_subset G I J)))
  rw [← sum_fiberwise_of_maps_to' hmaps g]
  apply sum_congr rfl
  intro m _
  rw [sum_const, smul_eq_mul, mul_comm]
  congr 1
  unfold Zhang.tCount indepSubsets
  congr 1
  ext J
  simp only [mem_filter, mem_powersetCard, mem_powerset]
  tauto

/-- **`R_h` in the inventory**: `R_h = Σ_{m ≤ a} (a - m - h) N[h, m]` (`A = I`, `C = s \ I`). -/
theorem blockerCharge_eq_sum_tCount (s I : Finset V) (h : ℕ) :
    blockerCharge G I (s \ I) h =
      ∑ m ∈ range (I.card + 1), (I.card - m - h) * Zhang.tCount G s I h m := by
  rw [sum_mul_tCount s I h (fun m => I.card - m - h)]
  unfold blockerCharge
  apply sum_congr rfl
  intro J _
  rw [card_nbhdIn]

/-- `N_A({v}) = N(v) ∩ A`. -/
theorem nbhdIn_singleton (I : Finset V) (v : V) : nbhdIn G I {v} = I.filter (G.Adj v) := by
  ext b
  rw [mem_nbhdIn, mem_filter]
  simp only [mem_singleton, exists_eq_left]

omit [DecidableEq V] in
/-- Every singleton is independent: sums over the independent 1-subsets of `Y` are sums over `Y`. -/
theorem sum_indepSubsets_one (Y : Finset V) (f : Finset V → ℕ) :
    ∑ J ∈ indepSubsets G Y 1, f J = ∑ v ∈ Y, f {v} := by
  have h1 : indepSubsets G Y 1 = Y.powersetCard 1 := by
    unfold indepSubsets
    apply filter_true_of_mem
    intro J hJ
    obtain ⟨v, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hJ).2
    intro x hx y hy hxy
    rw [mem_singleton] at hx hy
    rw [hx, hy] at hxy
    exact G.irrefl hxy
  rw [h1, powersetCard_one, sum_map]
  rfl

/-- **`D` in the inventory**: `D = Σ_{m ≤ a} (a - m) N[1, m]` (`A = I`, `C = s \ I`). -/
theorem card_crossEdges_eq_sum_tCount (s I : Finset V) :
    (crossEdges G I (s \ I)).card =
      ∑ m ∈ range (I.card + 1), (I.card - m) * Zhang.tCount G s I 1 m := by
  rw [sum_mul_tCount s I 1 (fun m => I.card - m), sum_indepSubsets_one, card_crossEdges]
  apply sum_congr rfl
  intro v _
  rw [← nbhdIn_singleton, card_nbhdIn]

/-- **Theorem 3.1 as a row on the inventory `N[y, m] = t_{y,m}`**.  Let `μ` match `C = s \ I`
into `A = I` (injective on `C`, `μ v ∈ I`, `v ~ μ v`) with `U ≤ a - c`.  Then for `2 ≤ h ≤ c`,
`Σ_m (a - m - h) N[h, m] ≤ (Σ_m (a - m) N[1, m] - c) C(c-2, h-1) + (a - c) C(c-2, h-2)`. -/
theorem blockerCharge_le_inventory {s I : Finset V} {μ : V → V} (hμA : ∀ v ∈ s \ I, μ v ∈ I)
    (hμadj : ∀ v ∈ s \ I, G.Adj v (μ v)) (hμinj : Set.InjOn μ ↑(s \ I))
    (hU : unmatchedExcess G I (s \ I) μ ≤ I.card - (s \ I).card) {h : ℕ} (h2 : 2 ≤ h)
    (hhc : h ≤ (s \ I).card) :
    ∑ m ∈ range (I.card + 1), (I.card - m - h) * Zhang.tCount G s I h m ≤
      (∑ m ∈ range (I.card + 1), (I.card - m) * Zhang.tCount G s I 1 m - (s \ I).card) *
          ((s \ I).card - 2).choose (h - 1) +
        (I.card - (s \ I).card) * ((s \ I).card - 2).choose (h - 2) := by
  rw [← blockerCharge_eq_sum_tCount, ← card_crossEdges_eq_sum_tCount]
  exact blockerCharge_le hμA hμadj hμinj hU h2 hhc

/-- **(9) as an inventory row**: `S^-_h = Σ_m N[h, m] - C(c, h) + (C(c, 2) - Σ_m N[2, m])
C(c-2, h-2) ≥ 0` for `2 ≤ h` (`c = |s \ I|`). -/
theorem edgeUnion_nonneg_inventory (s I : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    0 ≤ ((∑ m ∈ range (I.card + 1), Zhang.tCount G s I h m : ℕ) : ℤ) - ((s \ I).card.choose h : ℕ) +
      (((s \ I).card.choose 2 : ℕ) - ((∑ m ∈ range (I.card + 1), Zhang.tCount G s I 2 m : ℕ) : ℤ)) *
        (((s \ I).card - 2).choose (h - 2) : ℕ) := by
  rw [Zhang.sum_tCount, Zhang.sum_tCount]
  exact edgeUnion_nonneg (s \ I) h2

/-- **(10) as an inventory row**: `S^+_h = C(c-2, h-2) Σ_m N[2, m] - C(h, 2) Σ_m N[h, m] ≥ 0`
for `2 ≤ h` (`c = |s \ I|`). -/
theorem pairExtension_nonneg_inventory (s I : Finset V) {h : ℕ} (h2 : 2 ≤ h) :
    0 ≤ (((s \ I).card - 2).choose (h - 2) : ℕ) *
        ((∑ m ∈ range (I.card + 1), Zhang.tCount G s I 2 m : ℕ) : ℤ) -
      (h.choose 2 : ℕ) * ((∑ m ∈ range (I.card + 1), Zhang.tCount G s I h m : ℕ) : ℤ) := by
  rw [Zhang.sum_tCount, Zhang.sum_tCount]
  exact pairExtension_nonneg (s \ I) h2

end Fiber
end Erdos993Lean
