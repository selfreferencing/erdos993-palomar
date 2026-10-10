module

public import Erdos993Lean.Analytic.V213.Final

/-! Four explicit consumers of the unconditional final theorem, including
the small forests that bypass the large-order lower-edge lemma. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FinalChecks

def emptyForest : FiniteForest :=
  ⟨0, ⊥, SimpleGraph.isAcyclic_bot⟩

def singletonForest : FiniteForest :=
  ⟨1, ⊥, SimpleGraph.isAcyclic_bot⟩

def edgeForest : FiniteForest :=
  ⟨2, SimpleGraph.starGraph 0, SimpleGraph.isAcyclic_starGraph (0 : Fin 2)⟩

def pathThreeForest : FiniteForest :=
  ⟨3, SimpleGraph.starGraph 1, SimpleGraph.isAcyclic_starGraph (1 : Fin 3)⟩

theorem pathThree_graph : pathThreeForest.graph = SimpleGraph.pathGraph 3 := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [pathThreeForest, SimpleGraph.starGraph_adj, SimpleGraph.pathGraph_adj]

theorem empty_unimodal : independenceSequenceUnimodal emptyForest :=
  erdos993_v213_final emptyForest

theorem singleton_unimodal : independenceSequenceUnimodal singletonForest :=
  erdos993_v213_final singletonForest

theorem edge_unimodal : independenceSequenceUnimodal edgeForest :=
  erdos993_v213_final edgeForest

theorem pathThree_unimodal : independenceSequenceUnimodal pathThreeForest :=
  erdos993_v213_final pathThreeForest

end Erdos993Lean.Analytic.V213.FinalChecks

#print axioms Erdos993Lean.Analytic.V213.FinalChecks.empty_unimodal
#print axioms Erdos993Lean.Analytic.V213.FinalChecks.singleton_unimodal
#print axioms Erdos993Lean.Analytic.V213.FinalChecks.edge_unimodal
#print axioms Erdos993Lean.Analytic.V213.FinalChecks.pathThree_unimodal
