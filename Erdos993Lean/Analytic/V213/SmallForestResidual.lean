module

public import Erdos993Lean.Analytic.V213.SmallForestSignIntervals

/-!
Supporting-line infrastructure. These finite interval arguments are
generic real sequence proofs, with actual adjacent changes, not hypotheses
standing in for a graph inequality. The G consumer discharges the interval
premise using the sign-interval module. No finite tables are used in this module.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestResidual

open Erdos993Lean.Analytic.V213.SmallForest

/-- The three possible residual minima in the printed supporting-line proof. -/
theorem supporting_residual_nonneg (R f : ℕ → ℝ) (q : ℝ) (t M : ℕ)
    (ht : 2 ≤ t) (hM : t ≤ M) (_hq : 0 < q)
    (hlevel : ∀ a b c : ℕ, a ≤ b → b ≤ c → q ≤ f a → q ≤ f c → q ≤ f b)
    (hfirst : f (t - 1) = q) (hprevious : f (t - 2) < q)
    (hstep : ∀ n : ℕ, R (n + 1) - R n = f n - q)
    (hleft : R (t - 1) = 0) (hright : R t = 0) (hend : 0 ≤ R M) :
    ∀ m : ℕ, m ≤ M → 0 ≤ R m := by
  intro m hm
  by_contra hn
  have hnegative : R m < 0 := lt_of_not_ge hn
  by_cases hl : m ≤ t - 1
  · have hr : R m < R (t - 1) := by rw [hleft]; exact hnegative
    obtain ⟨r, _, hrt, hinc⟩ := exists_positive_step R hl hr
    have hfr : q ≤ f r := by have := hstep r; linarith
    have hmid := hlevel r (t - 2) (t - 1) (by omega) (by omega) hfr (by rw [hfirst])
    linarith only [hprevious, hmid]
  · have htm : t ≤ m := by omega
    have hr : R m < R t := by rw [hright]; exact hnegative
    obtain ⟨r, htr, hrm, hdec⟩ := exists_negative_step R htm hr
    have hrM : R m < R M := hnegative.trans_le hend
    obtain ⟨s, hms, _, hinc⟩ := exists_positive_step R hm hrM
    have hfr : f r < q := by have := hstep r; linarith
    have hfs : q ≤ f s := by have := hstep s; linarith
    have hmid := hlevel (t - 1) r s (by omega) (by omega) (by rw [hfirst]) hfs
    linarith only [hfr, hmid]

/-- After a positive increment, an interval of positive increments has no new valley. -/
theorem endpoint_min_after_positive_step (f : ℕ → ℝ) (b : ℕ) (floor : ℝ)
    (hinterval : ∀ a r c : ℕ, a ≤ r → r ≤ c →
      f a < f (a + 1) → f c < f (c + 1) → f r < f (r + 1))
    (hstart : f b < f (b + 1)) (hprefix : ∀ n : ℕ, n ≤ b → floor ≤ f n) :
    ∀ M m : ℕ, m ≤ M → min floor (f M) ≤ f m := by
  intro M m hm
  by_cases hmb : m ≤ b
  · exact (min_le_left _ _).trans (hprefix m hmb)
  · by_contra hn
    have hbad : f m < min floor (f M) := lt_of_not_ge hn
    have hleft : f m < f b := (hbad.trans_le (min_le_left _ _)).trans_le (hprefix b le_rfl)
    obtain ⟨r, hbr, hrm, hdec⟩ := exists_negative_step f (by omega : b ≤ m) hleft
    have hright : f m < f M := hbad.trans_le (min_le_right _ _)
    obtain ⟨s, hms, _, hinc⟩ := exists_positive_step f hm hright
    have hpos := hinterval b r s hbr (by omega) hstart hinc
    exact (not_lt_of_ge (le_of_lt hpos)) hdec

end Erdos993Lean.Analytic.V213.SmallForestResidual

#check Erdos993Lean.Analytic.V213.SmallForestResidual.supporting_residual_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestResidual.supporting_residual_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestResidual.endpoint_min_after_positive_step
#print axioms Erdos993Lean.Analytic.V213.SmallForestResidual.endpoint_min_after_positive_step
