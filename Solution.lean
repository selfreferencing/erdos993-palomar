module

public import Mathlib
public import Erdos993Lean.PalomarBridge
public import Erdos993Lean.Analytic.V213.Final
public import Erdos993Lean.Analytic.V213.FinalChecks

/-!
# Proved solution

Comparator checks that each declaration below has exactly the same statement as its counterpart in
`Challenge.lean`, that the two definitions agree, and that only propext, Classical.choice and Quot.sound are used.
The proof formalizes the argument of W. Li, K. Vallier and T. Zhang, "Unimodality of Forest Independence Polynomials"
(see `README.md`), through `Erdos993Lean.Analytic.V213.erdos993_v213_final` and the bridge `Erdos993Lean.PalomarBridge`.
-/

@[expose] public section

namespace Erdos993

/-- `indepSeq G k` is the number of `k`-element independent sets of `G`, i.e. the `k`-th term
`i_k(G)` of the independence sequence. -/
noncomputable def indepSeq {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {s : Finset V // s.card = k ∧ G.IsIndepSet (s : Set V)}

/-- A sequence `a : ℕ → ℕ` is *unimodal* if it is nondecreasing up to some index `m` and
nonincreasing thereafter. -/
def UnimodalSeq (a : ℕ → ℕ) : Prop :=
  ∃ m, (∀ i, i < m → a i ≤ a (i + 1)) ∧ (∀ i, m ≤ i → a (i + 1) ≤ a i)

/-- **Erdős Problem 993, for forests.** The independence sequence of every finite forest is unimodal. -/
theorem erdos_993_forest : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsAcyclic → UnimodalSeq (indepSeq G) := by
  intro V _ G hG
  exact Erdos993Lean.PalomarBridge.unimodal_nat_card_of_acyclic
    Erdos993Lean.Analytic.V213.erdos993_v213_final G hG

/-- **Erdős Problem 993.** The independence sequence `i_k(T)` of every finite tree `T` is
unimodal. (The question is attributed to Alavi, Malde, Schwenk and Erdős, 1987.) -/
theorem erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsTree → UnimodalSeq (indepSeq G) := by
  intro V _ G hT
  exact erdos_993_forest V G hT.isAcyclic

end Erdos993

#print axioms Erdos993.erdos_993_forest
#print axioms Erdos993.erdos_993
