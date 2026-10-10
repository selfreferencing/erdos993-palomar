module

public import Erdos993Lean.Fiber.Matching
public import Erdos993Lean.Fiber.Counts
public import Erdos993Lean.Zhang.Rows.Basic

/-!
# Current Section 7: matching and the first three counting rows

The opening part of Lemma 7.2 (`r12:lem25`).
All hypotheses and conclusions are graph statements; no finite table is used.
The existing exposed-leaf matching theorem has exactly the printed conclusion,
but uses augmented Hall/forest expansion rather than alternating-path flips.

The later E_1, support and all-index payment bounds are proved separately.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

/-- The paper's N_h: independent h-subsets of the complement of A. -/
def N (A : Finset (Fin F.n)) (h : ℕ) : ℕ := indepCount F.graph Aᶜ h

/-- The paper's e: the number of edges in the subgraph induced by C=Aᶜ. -/
def internalEdges (A : Finset (Fin F.n)) : ℕ := Zhang.Rows.eIn F.graph Aᶜ

/-- Maximum means maximum cardinality, not merely inclusion-maximal. -/
theorem exists_maximum_independent :
    ∃ A : Finset (Fin F.n), F.graph.IsIndepSet (A : Set (Fin F.n)) ∧
      ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card :=
  Fiber.exists_maxIndep F

/-- Lemma 7.2: the matching saturates C and exposes only leaves or isolated vertices. -/
theorem exists_exposed_matching (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) →
      S.card ≤ A.card) :
    ∃ σ : Fin F.n → Fin F.n, Set.InjOn σ (Aᶜ : Finset (Fin F.n)) ∧
      (∀ v ∈ Aᶜ, σ v ∈ A ∧ F.graph.Adj v (σ v)) ∧
      ∀ v ∈ A \ (Aᶜ).image σ, F.graph.degree v ≤ 1 :=
  Fiber.exists_saturating_matching_exposedLeaves F A hA hmax

theorem complement_card_le (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) →
      S.card ≤ A.card) :
    (Aᶜ).card ≤ A.card :=
  Fiber.card_compl_le_card F A hA hmax

theorem matchingNumber_eq_complement_card (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) →
      S.card ≤ A.card) :
    matchingNumber F.graph = (Aᶜ).card := by
  simpa only [Finset.card_compl, Fintype.card_fin] using
    Fiber.matchingNumber_eq_of_maxIndep F A hA hmax

/-- This supplies the literal finite-set interpretation of every N_h. -/
theorem N_eq_card_independent_subsets (A : Finset (Fin F.n)) (h : ℕ) :
    N F A h = (Zhang.Rows.indepSets F.graph Aᶜ h).card :=
  Zhang.Rows.indepCount_eq_card_indepSets Aᶜ h

/-- The two existing edge-count interfaces have exactly the same definition. -/
theorem internalEdges_eq_fiberEdgeCount (A : Finset (Fin F.n)) :
    internalEdges F A = Fiber.edgeCount F.graph Aᶜ := rfl

theorem N_zero (A : Finset (Fin F.n)) : N F A 0 = 1 :=
  indepCount_zero F.graph Aᶜ

theorem N_one (A : Finset (Fin F.n)) : N F A 1 = (Aᶜ).card :=
  Zhang.indepCount_one Aᶜ

/-- The additive identity is exact even when C is empty. -/
theorem N_two_add_internalEdges (A : Finset (Fin F.n)) :
    N F A 2 + internalEdges F A = (Aᶜ).card.choose 2 :=
  Zhang.Rows.indepCount_two_add_eIn Aᶜ

theorem N_two (A : Finset (Fin F.n)) :
    N F A 2 = (Aᶜ).card.choose 2 - internalEdges F A := by
  have h := N_two_add_internalEdges F A
  omega

/-- The printed subtraction also holds in the integers, without truncated subtraction. -/
theorem N_two_int (A : Finset (Fin F.n)) :
    (N F A 2 : ℤ) = ((Aᶜ).card.choose 2 : ℤ) - (internalEdges F A : ℤ) := by
  have h : (N F A 2 : ℤ) + (internalEdges F A : ℤ) = ((Aᶜ).card.choose 2 : ℤ) := by
    exact_mod_cast N_two_add_internalEdges F A
  omega

/-- The natural-valued forest edge bound also covers the empty induced subgraph. -/
theorem internalEdges_le (A : Finset (Fin F.n)) :
    internalEdges F A ≤ (Aᶜ).card - 1 :=
  Zhang.Rows.eIn_le_card_sub_one F.isForest Aᶜ

/-- An edge prevents the complement of an independent set from being empty. -/
theorem complement_card_pos_of_edge (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hedge : ∃ x y, F.graph.Adj x y) : 0 < (Aᶜ).card := by
  obtain ⟨x, y, hxy⟩ := hedge
  apply Finset.card_pos.mpr
  by_cases hx : x ∈ A
  · refine ⟨y, Finset.mem_compl.mpr ?_⟩
    intro hy
    exact hA (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) (F.graph.ne_of_adj hxy) hxy
  · exact ⟨x, Finset.mem_compl.mpr hx⟩

/-- The displayed 0 ≤ e ≤ c-1 on its printed non-edgeless domain. -/
theorem internalEdges_bounds (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hedge : ∃ x y, F.graph.Adj x y) :
    0 ≤ (internalEdges F A : ℤ) ∧ (internalEdges F A : ℤ) ≤ ((Aᶜ).card : ℤ) - 1 := by
  have hc := complement_card_pos_of_edge F A hA hedge
  have he := internalEdges_le F A
  omega

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.exists_maximum_independent
#print axioms Erdos993Lean.Analytic.V213.SmallForest.exists_maximum_independent
#check Erdos993Lean.Analytic.V213.SmallForest.exists_exposed_matching
#print axioms Erdos993Lean.Analytic.V213.SmallForest.exists_exposed_matching
#check Erdos993Lean.Analytic.V213.SmallForest.complement_card_le
#print axioms Erdos993Lean.Analytic.V213.SmallForest.complement_card_le
#check Erdos993Lean.Analytic.V213.SmallForest.matchingNumber_eq_complement_card
#print axioms Erdos993Lean.Analytic.V213.SmallForest.matchingNumber_eq_complement_card
#check Erdos993Lean.Analytic.V213.SmallForest.N_eq_card_independent_subsets
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_eq_card_independent_subsets
#check Erdos993Lean.Analytic.V213.SmallForest.internalEdges_eq_fiberEdgeCount
#print axioms Erdos993Lean.Analytic.V213.SmallForest.internalEdges_eq_fiberEdgeCount
#check Erdos993Lean.Analytic.V213.SmallForest.N_zero
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_zero
#check Erdos993Lean.Analytic.V213.SmallForest.N_one
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_one
#check Erdos993Lean.Analytic.V213.SmallForest.N_two_add_internalEdges
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_two_add_internalEdges
#check Erdos993Lean.Analytic.V213.SmallForest.N_two
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_two
#check Erdos993Lean.Analytic.V213.SmallForest.N_two_int
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_two_int
#check Erdos993Lean.Analytic.V213.SmallForest.internalEdges_le
#print axioms Erdos993Lean.Analytic.V213.SmallForest.internalEdges_le
#check Erdos993Lean.Analytic.V213.SmallForest.complement_card_pos_of_edge
#print axioms Erdos993Lean.Analytic.V213.SmallForest.complement_card_pos_of_edge
#check Erdos993Lean.Analytic.V213.SmallForest.internalEdges_bounds
#print axioms Erdos993Lean.Analytic.V213.SmallForest.internalEdges_bounds
