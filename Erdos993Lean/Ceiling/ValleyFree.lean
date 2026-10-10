module

public import Erdos993Lean.Ceiling.Statement

/-!
# The valley-free window lemma

Sources: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*, v1.1,
§5.3 (stitching the prefix, the window and the tail).



The ceiling's assembly `unimodal_of_prefix_window_tail` (`Ceiling/Statement.lean`) needs
log-concavity with positive entries across the window.  The analytic route for forests with at
least 61 vertices delivers less at each window rank `k`: **no weak valley**, i.e. never
`a k ≤ a (k − 1)` together with `a k ≤ a (k + 1)`.  This is enough:

* `no_descent_then_ascent`: under the three hypotheses below, a strict descent at `i` is never
  followed by a strict ascent at some `j > i`;
* `unimodal_of_prefix_valleyFree_tail`: a sequence that is nondecreasing up to `L`, has no weak
  valley at any rank `k` with `L < k < U`, and is nonincreasing from `U` on is unimodal.

Proof.  Given a strict descent at `i` and a strict ascent at `j > i`, the prefix forces `L ≤ i`
and the tail forces `j < U`; the first `k > i` with `a k ≤ a (k + 1)` satisfies `k ≤ j` and
`a k < a (k − 1)`, a weak valley with `L < k < U`.  Hence the sequence is nondecreasing before its
first strict descent (or before `U`, if that comes first) and nonincreasing from there on.
-/

@[expose] public section

namespace Erdos993Lean

/-- Under a nondecreasing prefix up to `L`, no weak valley strictly between `L` and `U`, and a
nonincreasing tail from `U`, a strict descent at `i` is never followed by a strict ascent at a
later index `j`. -/
theorem no_descent_then_ascent {a : ℕ → ℕ} {L U : ℕ}
    (hpre : ∀ k, k < L → a k ≤ a (k + 1))
    (hvf : ∀ k, L < k → k < U → a k ≤ a (k - 1) → a k ≤ a (k + 1) → False)
    (htail : ∀ k, U ≤ k → a (k + 1) ≤ a k) {i j : ℕ} (hij : i < j)
    (hi : a (i + 1) < a i) (hj : a j < a (j + 1)) : False := by
  classical
  have hLi : L ≤ i := by
    by_contra h
    push_neg at h
    exact absurd (hpre i h) (not_le.mpr hi)
  have hjU : j < U := by
    by_contra h
    push_neg at h
    exact absurd (htail j h) (not_le.mpr hj)
  -- the first weak ascent after `i`
  have hex : ∃ k, i < k ∧ a k ≤ a (k + 1) := ⟨j, hij, hj.le⟩
  obtain ⟨hik, hkup⟩ := Nat.find_spec hex
  have hkj : Nat.find hex ≤ j := Nat.find_min' hex ⟨hij, hj.le⟩
  have hkdown : a (Nat.find hex) < a (Nat.find hex - 1) := by
    rcases Nat.lt_or_ge (i + 1) (Nat.find hex) with h | h
    · -- `Nat.find hex - 1` lies strictly between `i` and `Nat.find hex`: a strict descent there
      have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at hmin
      have h1 := hmin (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at h1
    · -- `Nat.find hex = i + 1`
      have hk1 : Nat.find hex = i + 1 := by omega
      rw [hk1, Nat.add_sub_cancel]
      exact hi
  exact hvf (Nat.find hex) (by omega) (by omega) hkdown.le hkup

/-- **The valley-free window lemma** (Zhang §5.3 stitching; the Zhang proof map's §5,
consequence 4).  A sequence that is nondecreasing up to `L`, has no weak valley
(`a k ≤ a (k − 1)` and `a k ≤ a (k + 1)`) at any rank `k` with `L < k < U`, and is nonincreasing
from `U` on is unimodal. -/
theorem unimodal_of_prefix_valleyFree_tail {a : ℕ → ℕ} {L U : ℕ}
    (hpre : ∀ k, k < L → a k ≤ a (k + 1))
    (hvf : ∀ k, L < k → k < U → a k ≤ a (k - 1) → a k ≤ a (k + 1) → False)
    (htail : ∀ k, U ≤ k → a (k + 1) ≤ a k) : Unimodal a := by
  classical
  -- the peak: the first strict descent, or `U` if that comes first
  have hex : ∃ k, a (k + 1) < a k ∨ U ≤ k := ⟨U, Or.inr le_rfl⟩
  have hbefore : ∀ k, k < Nat.find hex → a k ≤ a (k + 1) := by
    intro k hk
    have h := Nat.find_min hex hk
    push_neg at h
    exact h.1
  have hafter : ∀ k, Nat.find hex ≤ k → a (k + 1) ≤ a k := by
    intro k hk
    by_cases hUk : U ≤ k
    · exact htail k hUk
    · by_contra hasc
      push_neg at hasc
      rcases Nat.find_spec hex with hdesc | hUm
      · rcases Nat.lt_or_ge (Nat.find hex) k with hlt | hge
        · exact no_descent_then_ascent hpre hvf htail hlt hdesc hasc
        · have hmk : Nat.find hex = k := le_antisymm hk hge
          rw [hmk] at hdesc
          exact absurd hasc (not_lt.mpr hdesc.le)
      · exact hUk (le_trans hUm hk)
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro i j hij hjm
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans (ih (by omega)) (hbefore j (by omega))
  · intro i j hmi hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans (hafter j (by omega)) ih

end Erdos993Lean
