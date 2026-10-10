module

public import Erdos993Lean.Analytic.V213.SmallForestMatching
public import Erdos993Lean.Analytic.V213.MatchingMode
public import Erdos993Lean.Analytic.V213.Foundation

/-!
# Current small-forest window: exact parameter-domain connector

Source: Section 7 of version 2.13 of the manuscript, equation (115), using the sharp first-mode bound of
Section 2. This file establishes the domain of every
relevant window rank; it does not use finite classification, a positive
variation table, or an old small-forest theorem. It does not yet assert
unimodality. The conjunction is stated literally to avoid importing the
current-domain classification module.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

theorem card_add_complement (A : Finset (Fin F.n)) : A.card + (Aᶜ).card = F.n := by
  have ha : A.card ≤ F.n := by simpa only [Fintype.card_fin] using Finset.card_le_univ A
  rw [Finset.card_compl, Fintype.card_fin]
  omega

/-- Natural-coordinate form of the literal strict window and equation (115).
The mode numerator's subtraction is justified through the matching/complement
identity; the returned domain has no silently truncated negative term. -/
theorem natural_window_domain (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hedge : ∃ x y, F.graph.Adj x y) (hn : F.n ≤ 24) {k : ℕ}
    (hlow : (F.n + 3) / 4 < k) (hhigh : k < hB F) :
    (Aᶜ).card ≤ A.card ∧ 1 ≤ (Aᶜ).card ∧
      A.card + (Aᶜ).card ≤ min 24 (4 * k - 4) ∧
      6 * k + 3 ≤ 3 * A.card + (Aᶜ).card := by
  have hca := complement_card_le F A hA hmax
  have hc := complement_card_pos_of_edge F A hA hedge
  have hcard := card_add_complement F A
  have hnu := matchingNumber_eq_complement_card F A hA hmax
  have hmode := forest_firstMode_sharp F
  rw [hnu] at hmode
  have hquarter : F.n + 4 ≤ 4 * k := by omega
  have hsixth : 6 * k + 3 ≤ 3 * A.card + (Aᶜ).card := by omega
  refine ⟨hca, by omega, ?_, hsixth⟩
  apply le_min
  · omega
  · omega

/-- The integer `WindowRank` definition is transported without weakening its
strict endpoints. The resulting natural rank is exactly k.toNat. -/
theorem integer_window_domain (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hedge : ∃ x y, F.graph.Adj x y) (hn : F.n ≤ 24) {k : ℤ}
    (hw : WindowRank F k) :
    0 ≤ k ∧ (Aᶜ).card ≤ A.card ∧ 1 ≤ (Aᶜ).card ∧
      A.card + (Aᶜ).card ≤ min 24 (4 * k.toNat - 4) ∧
      6 * k.toNat + 3 ≤ 3 * A.card + (Aᶜ).card := by
  have hk : 0 ≤ k := by have := hw.1; omega
  have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  have hlow : (F.n + 3) / 4 < k.toNat := by have := hw.1; omega
  have hhigh : k.toNat < hB F := by have := hw.2; omega
  exact ⟨hk, natural_window_domain F A hA hmax hedge hn hlow hhigh⟩

/-- The short algebraic range consequence after (115); no catalogue is used. -/
theorem window_rank_bounds (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hedge : ∃ x y, F.graph.Adj x y) (hn : F.n ≤ 24) {k : ℕ}
    (hlow : (F.n + 3) / 4 < k) (hhigh : k < hB F) :
    3 ≤ k ∧ k ≤ 11 := by
  obtain ⟨hca, hc, hsize, hmode⟩ := natural_window_domain F A hA hmax hedge hn hlow hhigh
  have h24 := le_trans hsize (min_le_left _ _)
  have hk := le_trans hsize (min_le_right _ _)
  omega

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.card_add_complement
#print axioms Erdos993Lean.Analytic.V213.SmallForest.card_add_complement
#check Erdos993Lean.Analytic.V213.SmallForest.natural_window_domain
#print axioms Erdos993Lean.Analytic.V213.SmallForest.natural_window_domain
#check Erdos993Lean.Analytic.V213.SmallForest.integer_window_domain
#print axioms Erdos993Lean.Analytic.V213.SmallForest.integer_window_domain
#check Erdos993Lean.Analytic.V213.SmallForest.window_rank_bounds
#print axioms Erdos993Lean.Analytic.V213.SmallForest.window_rank_bounds
