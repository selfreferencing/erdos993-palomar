module

public import Erdos993Lean.Analytic.V213.Foundation
public import Erdos993Lean.Analytic.V213.MatchingMode

/-!
# Edgeless forests in the current Section 7 window assembly

The edgeless branch. Every subset is independent, so the exact
coefficient sequence is the binomial row. Its unimodality follows from the
new Bernoulli proof at a=0, b=n. No small-order theorem, enumeration,
finite table, or occupation/moment hypothesis is used.
The empty forest and every natural rank are included.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset Polynomial

/-- With no edge, the counting filter retains every k-subset. -/
theorem count_eq_choose_of_no_edge (F : FiniteForest)
    (hedge : ¬ ∃ x y, F.graph.Adj x y) (k : ℕ) :
    independenceCount F k = F.n.choose k := by
  classical
  have hfilter :
      (univ : Finset (Fin F.n)).powerset.filter (IsIndepFinset F.graph) =
        univ.powerset := by
    apply Finset.filter_eq_self.mpr
    intro S _
    intro x _ y _ hxy
    exact hedge ⟨x, y, hxy⟩
  rw [count_eq_indepCount, indepCount, hfilter,
    ← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- The binomial row is the a=0 specialization of the two-weight row. -/
theorem count_eq_twoWeight_of_no_edge (F : FiniteForest)
    (hedge : ¬ ∃ x y, F.graph.Adj x y) :
    independenceCount F = fun k => (twoWeightPoly 0 F.n).coeff k := by
  funext k
  rw [count_eq_choose_of_no_edge F hedge]
  simp only [twoWeightPoly, pow_zero, one_mul, Polynomial.coeff_one_add_X_pow,
    Nat.cast_id]

/-- The full zero-extended natural sequence is unimodal at every order. -/
theorem unimodal_of_no_edge (F : FiniteForest)
    (hedge : ¬ ∃ x y, F.graph.Adj x y) :
    Unimodal (independenceCount F) := by
  rw [count_eq_twoWeight_of_no_edge F hedge]
  obtain ⟨hlc, hpos⟩ := twoWeight_logConcave_positive 0 F.n
  exact unimodal_of_logConcave hlc hpos.noInternalZeros hpos.finitelySupported

/-- The exact statement-level edgeless case, including the empty forest. -/
theorem independenceSequenceUnimodal_of_no_edge (F : FiniteForest)
    (hedge : ¬ ∃ x y, F.graph.Adj x y) :
    independenceSequenceUnimodal F := by
  exact unimodalUpTo_of_unimodal (unimodal_of_no_edge F hedge)

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.count_eq_choose_of_no_edge
#print axioms Erdos993Lean.Analytic.V213.SmallForest.count_eq_choose_of_no_edge
#check Erdos993Lean.Analytic.V213.SmallForest.count_eq_twoWeight_of_no_edge
#print axioms Erdos993Lean.Analytic.V213.SmallForest.count_eq_twoWeight_of_no_edge
#check Erdos993Lean.Analytic.V213.SmallForest.unimodal_of_no_edge
#print axioms Erdos993Lean.Analytic.V213.SmallForest.unimodal_of_no_edge
#check Erdos993Lean.Analytic.V213.SmallForest.independenceSequenceUnimodal_of_no_edge
#print axioms Erdos993Lean.Analytic.V213.SmallForest.independenceSequenceUnimodal_of_no_edge
