module

public import Erdos993Lean.Analytic.V213.SmallForestCurrentForest
public import Erdos993Lean.Analytic.V213.SmallForestWindow
public import Erdos993Lean.Analytic.V213.SmallForestEdgeless
public import Erdos993Lean.Analytic.V213.WindowReduction

/-!
Final current Section 7 assembly. This uses the new
current-table graph proofs and the printed window reduction. It imports no
inherited small-forest theorem, moment estimate, or old tangent table.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

/-- The current small-forest theorem for the entire zero-extended sequence. -/
theorem small_forest_unimodal (F : FiniteForest) (hn : F.n ≤ 24) :
    Unimodal (independenceCount F) := by
  classical
  by_cases hedge : ∃ x y, F.graph.Adj x y
  · obtain ⟨A, hA, hmax⟩ := exists_maximum_independent F
    apply window_reduction_unimodal F
    intro k hw
    obtain ⟨hk0, hd⟩ := integer_window_domain F A hA hmax hedge hn hw
    have hd' : SmallForestPrinted.CurrentDomain A.card (Aᶜ).card k.toNat := hd
    have hno := currentDomain_no_valley F A hA hmax k.toNat hd'
    have he : (k.toNat : ℤ) = k := by omega
    simpa only [he] using hno
  · exact unimodal_of_no_edge F hedge

/-- Literal Theorem 7.1, including empty and edgeless forests. -/
theorem small_forest_independenceSequenceUnimodal (F : FiniteForest) (hn : F.n ≤ 24) :
    independenceSequenceUnimodal F := by
  exact unimodalUpTo_of_unimodal (small_forest_unimodal F hn)

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.small_forest_unimodal
#print axioms Erdos993Lean.Analytic.V213.SmallForest.small_forest_unimodal
#check Erdos993Lean.Analytic.V213.SmallForest.small_forest_independenceSequenceUnimodal
#print axioms Erdos993Lean.Analytic.V213.SmallForest.small_forest_independenceSequenceUnimodal
