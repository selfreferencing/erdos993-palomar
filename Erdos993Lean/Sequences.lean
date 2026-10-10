module

public import Mathlib

/-!
# Sequence predicates

Unimodality, log-concavity and "no internal zeros" for sequences `ℕ → ℕ`, and the classical
implication: a finitely supported log-concave sequence with no internal zeros is unimodal.

These are the predicates used by every headline theorem of the package.  They are stated for
`ℕ`-valued sequences because the headline objects are counts of independent sets.
-/

@[expose] public section

namespace Erdos993Lean

/-- Weak unimodality: there is an index `m` such that the sequence is nondecreasing on
`[0, m]` and nonincreasing on `[m, ∞)`. -/
def Unimodal (a : ℕ → ℕ) : Prop :=
  ∃ m, (∀ i j, i ≤ j → j ≤ m → a i ≤ a j) ∧ (∀ i j, m ≤ i → i ≤ j → a j ≤ a i)

/-- Log-concavity: `a k * a (k + 2) ≤ a (k + 1) ^ 2` for every `k`. -/
def LogConcave (a : ℕ → ℕ) : Prop :=
  ∀ k, a k * a (k + 2) ≤ a (k + 1) * a (k + 1)

/-- No internal zeros: every entry between two nonzero entries is nonzero. -/
def NoInternalZeros (a : ℕ → ℕ) : Prop :=
  ∀ i j k, i ≤ j → j ≤ k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0

/-- The sequence vanishes from some index on. -/
def FinitelySupported (a : ℕ → ℕ) : Prop :=
  ∃ N, ∀ k, N ≤ k → a k = 0

/-- A finitely supported log-concave sequence of natural numbers with no internal zeros is
unimodal.  (Classical: after a strict decrease at a positive entry, log-concavity forces
another strict decrease.) -/
theorem unimodal_of_logConcave {a : ℕ → ℕ} (hlc : LogConcave a) (hnz : NoInternalZeros a)
    (hfin : FinitelySupported a) : Unimodal a := by
  classical
  by_cases hex : ∃ k, a (k + 1) < a k
  · -- `m` is the first strict descent.
    set m := Nat.find hex with hmdef
    have hm : a (m + 1) < a m := Nat.find_spec hex
    have hbefore : ∀ k, k < m → a k ≤ a (k + 1) := by
      intro k hk
      have := Nat.find_min hex hk
      omega
    -- After the first strict descent the sequence never rises again.
    have hafter : ∀ k, m ≤ k → a (k + 1) ≤ a k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hm.le
      | succ k hmk ih =>
        rcases Nat.eq_zero_or_pos (a (k + 1)) with h0 | hpos
        · by_contra hcon
          have hne : a (k + 1 + 1) ≠ 0 := by omega
          exact hnz m (k + 1) (k + 1 + 1) (by omega) (by omega) (by omega) hne h0
        · have hk0 : 0 < a k := lt_of_lt_of_le hpos ih
          have h1 : a k * a (k + 1 + 1) ≤ a (k + 1) * a (k + 1) := hlc k
          have h2 : a (k + 1) * a (k + 1) ≤ a k * a (k + 1) := Nat.mul_le_mul_right _ ih
          exact Nat.le_of_mul_le_mul_left (le_trans h1 h2) hk0
    refine ⟨m, ?_, ?_⟩
    · intro i j hij hjm
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j hij ih => exact le_trans (ih (by omega)) (hbefore j (by omega))
    · intro i j hmi hij
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j hij ih => exact le_trans (hafter j (by omega)) ih
  · -- No strict descent at all: nondecreasing, hence identically zero past the support.
    push_neg at hex
    obtain ⟨N, hN⟩ := hfin
    refine ⟨N, ?_, ?_⟩
    · intro i j hij _
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j hij ih => exact le_trans (ih (by omega)) (hex j)
    · intro i j hNi hij
      rw [hN j (le_trans hNi hij)]
      exact Nat.zero_le _

end Erdos993Lean
