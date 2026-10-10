module

public import Erdos993Lean.Analytic.V213.LowMeanCertificateFacts

/-! Closed consecutive interval coverage and the left-selected activity seams. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- Consecutive closed intervals cover their full span, including every seam. -/
theorem lowMean_consecutive_closed_cover (lo hi : ℕ → ℝ) (x : ℝ)
    (start n : ℕ) (hlo : lo start ≤ x) (hhi : x ≤ hi (start + n))
    (hseam : ∀ k, start ≤ k → k < start + n → hi k = lo (k + 1)) :
    ∃ k, start ≤ k ∧ k ≤ start + n ∧ x ∈ Set.Icc (lo k) (hi k) := by
  induction n generalizing start with
  | zero => exact ⟨start, le_rfl, by omega, hlo, by simpa using hhi⟩
  | succ n ih =>
    by_cases hfirst : x ≤ hi start
    · exact ⟨start, le_rfl, by omega, hlo, hfirst⟩
    · have hs := hseam start le_rfl (by omega)
      have hl : lo (start + 1) ≤ x := by rw [← hs]; exact (lt_of_not_ge hfirst).le
      have hh : x ≤ hi (start + 1 + n) := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhi
      have hm : ∀ k, start + 1 ≤ k → k < start + 1 + n → hi k = lo (k + 1) := by
        intro k hk hk'; exact hseam k (by omega) (by omega)
      obtain ⟨k, hk, hk', hx⟩ := ih (start + 1) hl hh hm
      exact ⟨k, by omega, by omega, hx⟩

def lowMeanLeftSelected (lo hi : ℕ → ℝ) (k : ℕ) (x : ℝ) : Prop :=
  ((k = 0 ∧ lo k ≤ x) ∨ lo k < x) ∧ x ≤ hi k

/-- The first interval includes its left endpoint; all subsequent left endpoints
are open. The shared endpoint is consequently assigned to the left interval. -/
theorem lowMean_consecutive_left_cover (lo hi : ℕ → ℝ) (x : ℝ)
    (start n : ℕ) (hlo : (start = 0 ∧ lo start ≤ x) ∨ lo start < x)
    (hhi : x ≤ hi (start + n))
    (hseam : ∀ k, start ≤ k → k < start + n → hi k = lo (k + 1)) :
    ∃ k, start ≤ k ∧ k ≤ start + n ∧ lowMeanLeftSelected lo hi k x := by
  induction n generalizing start with
  | zero => exact ⟨start, le_rfl, by omega, hlo, by simpa using hhi⟩
  | succ n ih =>
    by_cases hfirst : x ≤ hi start
    · exact ⟨start, le_rfl, by omega, hlo, hfirst⟩
    · have hs := hseam start le_rfl (by omega)
      have hl : (start + 1 = 0 ∧ lo (start + 1) ≤ x) ∨ lo (start + 1) < x := by
        right; rw [← hs]; exact lt_of_not_ge hfirst
      have hh : x ≤ hi (start + 1 + n) := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhi
      have hm : ∀ k, start + 1 ≤ k → k < start + 1 + n → hi k = lo (k + 1) := by
        intro k hk hk'; exact hseam k (by omega) (by omega)
      obtain ⟨k, hk, hk', hx⟩ := ih (start + 1) hl hh hm
      exact ⟨k, by omega, by omega, hx⟩

theorem lowMean_leftSelected_closed {lo hi : ℕ → ℝ} {k : ℕ} {x : ℝ}
    (hx : lowMeanLeftSelected lo hi k x) : x ∈ Set.Icc (lo k) (hi k) := by
  exact ⟨hx.1.elim And.right (fun h => h.le), hx.2⟩

end Erdos993Lean.Analytic.V213
