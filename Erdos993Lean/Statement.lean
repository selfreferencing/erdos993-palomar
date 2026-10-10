module

public import Mathlib
public import Erdos993Lean.Sequences

/-!
# The Erdős #993 statement

The definitions `FiniteForest`, `UnimodalUpTo`, `independenceCount`, `independenceNumber`,
`independenceSequenceUnimodal` and `Erdos993Statement` state the project's own form of the
problem for forests:
forests are simple graphs on `Fin n` satisfying Mathlib's
`SimpleGraph.IsAcyclic`, independent sets are counted with Mathlib's `indepSetFinset`, and
unimodality is weak unimodality up to the independence number.

Erdős Problem #993 asks whether `Erdos993Statement` holds.



This file also records the bridge from the package's own sequence predicates
(`Erdos993Lean.Unimodal`) to `UnimodalUpTo`.
-/

@[expose] public section

namespace Erdos993Lean

open SimpleGraph

/-- A finite forest encoded as a simple graph on the vertex type `Fin n`. -/
structure FiniteForest where
  n : Nat
  graph : SimpleGraph (Fin n)
  isForest : graph.IsAcyclic

/--
`UnimodalUpTo N a` says that the finite sequence `a 0, a 1, ..., a N` has a peak: it is
nondecreasing before the peak and nonincreasing after it.
-/
def UnimodalUpTo (N : Nat) (a : Nat → Nat) : Prop :=
  ∃ peak : Nat,
    peak ≤ N ∧
      (∀ k : Nat, k < peak → a k ≤ a (k + 1)) ∧
      (∀ k : Nat, peak ≤ k → k < N → a (k + 1) ≤ a k)

/-- The number of independent sets of cardinality `k` in a finite forest (Mathlib's
`indepSetFinset`, classical decidability). -/
noncomputable def independenceCount (F : FiniteForest) (k : Nat) : Nat := by
  classical
  exact (F.graph.indepSetFinset k).card

/-- The maximum size of an independent set in the finite forest. -/
noncomputable def independenceNumber (F : FiniteForest) : Nat :=
  F.graph.indepNum

/-- The independence sequence of `F` is unimodal through its independence number. -/
noncomputable def independenceSequenceUnimodal (F : FiniteForest) : Prop :=
  UnimodalUpTo (independenceNumber F) (independenceCount F)

/-- **Erdős Problem #993** (open): every finite forest has a unimodal independence sequence. -/
noncomputable def Erdos993Statement : Prop :=
  ∀ forest : FiniteForest, independenceSequenceUnimodal forest

/-- A unimodal sequence is unimodal up to any `N`. -/
theorem unimodalUpTo_of_unimodal {N : ℕ} {a : ℕ → ℕ} (h : Unimodal a) : UnimodalUpTo N a := by
  obtain ⟨m, hup, hdown⟩ := h
  by_cases hmN : m ≤ N
  · refine ⟨m, hmN, ?_, ?_⟩
    · intro k hk
      exact hup k (k + 1) (by omega) (by omega)
    · intro k hk _
      exact hdown k (k + 1) hk (by omega)
  · -- The peak lies beyond `N`, so the sequence is nondecreasing on `[0, N]`.
    refine ⟨N, le_rfl, ?_, ?_⟩
    · intro k hk
      exact hup k (k + 1) (by omega) (by omega)
    · intro k hk hk'
      omega

end Erdos993Lean
