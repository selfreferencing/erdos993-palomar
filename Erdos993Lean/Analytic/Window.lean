module

public import Erdos993Lean.Analytic.Defs
public import Erdos993Lean.Ceiling.Join
public import Erdos993Lean.Ceiling.Occupation.Main

/-!
# Exact activity selection at the interior window ranks (open object O6, option (b))

Interface: `Analytic/Defs.lean`.
Sources: the ceiling's join lemmas B2 and B7 (`Ceiling/Join.lean`; ceiling proof, Appendix R) and
the occupation bound B5 (`occupationAt73`, `Ceiling/Occupation/Main.lean`), which fixes the top
activity of the route at `7/3`.

The analytic route excludes a weak valley at a window rank `k` by looking at the hard-core model
at an activity `t` whose mean is exactly `k`.  For every interior window rank
`⌈n/4⌉ < k < h_B` such an activity exists, strictly inside `(1/3, 7/3)`:

* `exists_activity_eq`: `μ_F(1/3) ≤ n/4 < k` (B2); `k + 1 ≤ h_B ≤ ⌈(3n − 2ν)/6⌉` (B7, with
  `2ν ≤ n`) gives `6k + 1 ≤ 3n − 2ν`, so `k < W = n/2 − ν/3 ≤ W + cc/7 ≤ μ_F(7/3)` (B5); the
  intermediate value theorem on `[1/3, 7/3]` (continuity of `μ_F`) gives `t` with `μ_F(t) = k`,
  and `t` lies in the open interval because both end inequalities are strict.
* `exists_activity_inRange`: the same activity satisfies `InRange t`, `0 < t` and
  `AtInteriorRank F t`, the form consumed by the inputs O1–O5 of `Defs.lean`.

Compare `Join.exists_activity_near` (the ceiling's B8), which covers the closed window
`⌈n/4⌉ ≤ k ≤ h_B` but only places `k` within distance one of a mean.
-/

@[expose] public section

namespace Erdos993Lean.Analytic

/-- **Exact activity selection** (open object O6, option (b), via B5).  Every interior window
rank `⌈n/4⌉ < k < h_B` of a forest is the hard-core mean `μ_F(t)` at some activity
`t ∈ (1/3, 7/3)`. -/
theorem exists_activity_eq (F : FiniteForest) (k : ℕ)
    (hk1 : (F.n + 3) / 4 < k) (hk2 : k < hB F) :
    ∃ t : ℝ, 1 / 3 < t ∧ t < 7 / 3 ∧ hardCoreMean F t = k := by
  -- the left end (B2): `μ_F(1/3) ≤ n/4 < k`
  have hlow : hardCoreMean F (1 / 3) < k := by
    have h1 := Join.hardCoreMean_one_third_le F
    have hn4 : F.n + 4 ≤ 4 * k := by omega
    have h2 : (F.n : ℝ) + 4 ≤ 4 * (k : ℝ) := by exact_mod_cast hn4
    linarith
  -- the right end (B7 and B5): `k < W ≤ W + cc/7 ≤ μ_F(7/3)`
  have hhigh : (k : ℝ) < hardCoreMean F (7 / 3) := by
    have hB7 := Join.hB_le F
    have h2 := Join.two_mul_matchingNumber_le F.graph
    have hk6 : 6 * k + 1 + 2 * matchingNumber F.graph ≤ 3 * F.n := by omega
    have hk6R : 6 * (k : ℝ) + 1 + 2 * (matchingNumber F.graph : ℝ) ≤ 3 * (F.n : ℝ) := by
      exact_mod_cast hk6
    have hocc := occupationAt73 F
    have hcc : (0 : ℝ) ≤ (numComponents F : ℝ) / 7 := by positivity
    unfold matchingEnvelopeMean at hocc
    linarith
  have hcont : ContinuousOn (hardCoreMean F) (Set.Icc (1 / 3) (7 / 3)) :=
    (Join.continuousOn_hardCoreMean F).mono fun t ht => le_trans (by norm_num) ht.1
  obtain ⟨t, ⟨ht1, ht2⟩, hteq⟩ :=
    intermediate_value_Ioo (by norm_num : (1 / 3 : ℝ) ≤ 7 / 3) hcont ⟨hlow, hhigh⟩
  exact ⟨t, ht1, ht2, hteq⟩

/-- The activity of `exists_activity_eq` in the form used by the analytic inputs: it is in range,
positive, and puts the mean at the interior rank `k` (`AtInteriorRank`). -/
theorem exists_activity_inRange (F : FiniteForest) (k : ℕ)
    (hk1 : (F.n + 3) / 4 < k) (hk2 : k < hB F) :
    ∃ t : ℝ, InRange t ∧ 0 < t ∧ AtInteriorRank F t ∧ hardCoreMean F t = k := by
  obtain ⟨t, ht1, ht2, hμ⟩ := exists_activity_eq F k hk1 hk2
  exact ⟨t, ⟨ht1.le, ht2.le⟩, by linarith, ⟨k, hk1, hk2, hμ⟩, hμ⟩

end Erdos993Lean.Analytic
