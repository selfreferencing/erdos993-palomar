module

public import Erdos993Lean.Analytic.V213.LowMeanKernelMaximum
public import Erdos993Lean.Analytic.V213.LowMeanRoot

/-!
The full closed negative-kernel maximum, Lemma 6.5 of version 2.13 of the manuscript
(`r12:lem12`), equation `r12:eq52`. The index is the smaller quadratic
root rounded upward, clipped at zero and floor(M/2). Ties are included.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMeanG_pos {M n : ℕ} (hn : 2 * n ≤ M) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) : 0 < lowMeanG M n q := by
  have hnR : 2 * (n : ℝ) ≤ M := by exact_mod_cast hn
  unfold lowMeanG
  exact mul_pos (div_pos (by linarith) (by linarith))
    (lowMean_binom_pos (by omega) hq0 hq1)

/-- The successive-ratio comparison is exactly the sign of the printed quadratic. -/
theorem lowMeanG_step_iff {M n : ℕ} (hn : 2 * (n + 1) ≤ M) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    (lowMeanG M n q ≤ lowMeanG M (n + 1) q ↔ 0 ≤ lowMeanRootP M q n) ∧
      (lowMeanG M (n + 1) q ≤ lowMeanG M n q ↔ lowMeanRootP M q n ≤ 0) := by
  have hnR : 2 * ((n : ℝ) + 1) ≤ M := by exact_mod_cast hn
  let D := ((M : ℝ) + 1 - 2 * n) * ((n : ℝ) + 1) * (1 - q)
  let N := ((M : ℝ) - 1 - 2 * n) * ((M : ℝ) + 1 - n) * q
  have hD : 0 < D := mul_pos (mul_pos (by linarith) (by positivity)) (sub_pos.mpr hq1)
  have hG := lowMeanG_pos (by omega : 2 * n ≤ M) hq0 hq1
  have he : N - D = lowMeanRootP M q n := by
    dsimp [N, D, lowMeanRootP, lowMeanRootB, lowMeanRootC]
    ring
  have ha := lowMeanG_adjacent (by omega : n < M) q
  change D * lowMeanG M (n + 1) q = N * lowMeanG M n q at ha
  constructor
  · calc
      lowMeanG M n q ≤ lowMeanG M (n + 1) q ↔
          D * lowMeanG M n q ≤ D * lowMeanG M (n + 1) q := (mul_le_mul_iff_right₀ hD).symm
      _ ↔ D * lowMeanG M n q ≤ N * lowMeanG M n q := by rw [ha]
      _ ↔ D ≤ N := mul_le_mul_iff_left₀ hG
      _ ↔ 0 ≤ lowMeanRootP M q n := by rw [← he]; exact sub_nonneg.symm
  · calc
      lowMeanG M (n + 1) q ≤ lowMeanG M n q ↔
          D * lowMeanG M (n + 1) q ≤ D * lowMeanG M n q := (mul_le_mul_iff_right₀ hD).symm
      _ ↔ N * lowMeanG M n q ≤ D * lowMeanG M n q := by rw [ha]
      _ ↔ N ≤ D := mul_le_mul_iff_left₀ hG
      _ ↔ lowMeanRootP M q n ≤ 0 := by rw [← he]; exact sub_nonpos.symm

/-- At a fixed probability, the clipped ceiling of the smaller root maximizes g_J. -/
theorem lowMeanG_le_at_maxIndex (M : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) (hn : n ≤ M / 2) : lowMeanG M n q ≤ lowMeanG M (lowMeanMaxIndex M q) q := by
  let J := lowMeanMaxIndex M q
  have hJ : J ≤ M / 2 := lowMeanMaxIndex_le M q
  have hleft : MonotoneOn (fun n : ℕ => lowMeanG M n q) (Set.Iic J) := by
    apply monotoneOn_of_le_succ Set.ordConnected_Iic
    intro k _ _ hk
    have hkJ : k < J := by exact Nat.lt_of_succ_le hk
    have hkM : 2 * (k + 1) ≤ M := by omega
    have hx : (k : ℝ) ≤ ((M : ℝ) - 1) / 2 := by
      have hc : 2 * (k : ℝ) + 1 ≤ M := by exact_mod_cast (show 2 * k + 1 ≤ M by omega)
      linarith
    exact (lowMeanG_step_iff hkM hq0 hq1).1.mpr
      (lowMeanRootP_nonneg hq1 hx (lowMeanMaxIndex_left hkJ).le)
  have hright : AntitoneOn (fun n : ℕ => lowMeanG M n q) (Set.Icc J (M / 2)) := by
    apply antitoneOn_of_succ_le Set.ordConnected_Icc
    intro k _ hk hk1
    have hkM : 2 * (k + 1) ≤ M := by
      have hkk : k + 1 ≤ M / 2 := hk1.2
      omega
    have hx : (k : ℝ) ≤ ((M : ℝ) - 1) / 2 := by
      have hc : 2 * (k : ℝ) + 1 ≤ M := by exact_mod_cast (show 2 * k + 1 ≤ M by omega)
      linarith
    exact (lowMeanG_step_iff hkM hq0 hq1).2.mpr
      (lowMeanRootP_nonpos hq1 hx (lowMeanMaxIndex_right hk.1 (by omega)))
  rcases le_total n J with hnJ | hJn
  · exact hleft hnJ (by change J ≤ J; exact le_rfl) hnJ
  · exact hright ⟨le_rfl, hJ⟩ ⟨hJn, hn⟩ hJn

/-- Natural ceiling gives exactly the printed integer clipping at zero. -/
theorem lowMeanMaxIndex_eq_printed (M : ℕ) (q : ℝ) :
    (lowMeanMaxIndex M q : ℤ) =
      max 0 (min ((M / 2 : ℕ) : ℤ) (Int.ceil (lowMeanRoot M q))) := by
  unfold lowMeanMaxIndex
  rw [← Int.ceil_toNat]
  omega

/-- The printed G_M, including its separately specified M=0 value. -/
noncomputable def lowMeanClosedMaximum (M : ℕ) (q : ℝ) : ℝ :=
  if M = 0 then 1 else lowMeanG M (lowMeanMaxIndex M q) q

theorem lowMeanClosedMaximum_eq (M : ℕ) (q : ℝ) :
    lowMeanClosedMaximum M q = lowMeanG M (lowMeanMaxIndex M q) q := by
  by_cases hM : M = 0
  · subst M
    simp [lowMeanClosedMaximum, lowMeanMaxIndex, lowMeanG_zero]
  · simp [lowMeanClosedMaximum, hM]

/-- Lemma 6.5: on the closed probability interval, every admissible g_J is
bounded by the closed formula evaluated at its left endpoint. -/
theorem lowMean_closedMaximum (M : ℕ) {l h : ℝ} (hl : 0 < l) (hh : h < 1)
    {q : ℝ} (hq : q ∈ Set.Icc l h) (n : ℕ) (hn : n ≤ M / 2) :
    lowMeanG M n q ≤ lowMeanClosedMaximum M l := by
  rw [lowMeanClosedMaximum_eq]
  exact lowMeanG_uniform_bound hl hq.1 (lt_of_le_of_lt hq.2 hh)
    (fun k hk => lowMeanG_le_at_maxIndex M hl (lt_of_le_of_lt (le_trans hq.1 hq.2) hh)
      k (by omega)) n (by omega)

/-- The bound is attained at q=l and the printed maximizing index, so the
previous theorem is an exact maximum rather than just an upper bound. -/
theorem lowMean_closedMaximum_attained (M : ℕ) {l h : ℝ} (hlh : l ≤ h) :
    ∃ q ∈ Set.Icc l h, ∃ n : ℕ, n ≤ M / 2 ∧ lowMeanG M n q = lowMeanClosedMaximum M l := by
  exact ⟨l, ⟨le_rfl, hlh⟩, lowMeanMaxIndex M l, lowMeanMaxIndex_le M l,
    (lowMeanClosedMaximum_eq M l).symm⟩

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanG_le_at_maxIndex
#print axioms Erdos993Lean.Analytic.V213.lowMeanMaxIndex_eq_printed
#print axioms Erdos993Lean.Analytic.V213.lowMean_closedMaximum
#print axioms Erdos993Lean.Analytic.V213.lowMean_closedMaximum_attained
