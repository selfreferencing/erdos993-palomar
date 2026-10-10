module

public import Erdos993Lean.Analytic.V22.Analysis.MonotoneBounds

/-!
# Section 4: the exact lower-error comparison in nu

Source: frozen note Lemma 4.9(a). Both quartic branches, their positive
part, and the source's exact rational coefficient `1/12` are retained.
Consumer: the lower-range linearized coefficient in Lemma 4.10(a).
All denominators are proved positive on the original source domain.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def monotonePhi (r N : ℝ) : ℝ := 1 + 2 * activityNu r N / N

noncomputable def monotonePsiL (r N : ℝ) : ℝ :=
  (monotonePhi r N) ^ 4 * (1 - (V22.Z0 N) ^ 2) /
    ((1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2) * (1 - activityNu r N ^ 2 / N))

noncomputable def monotonePsiR (r N : ℝ) : ℝ :=
  (1 + r * (r + 2 * V22.Z0 N) / (1 - (r + V22.Z0 N) ^ 2)) /
    (1 - activityNu r N ^ 2 / N)

theorem monotone_Z0_phi_eq {r N : ℝ} (hN : 0 < N) :
    V22.Z0 N * monotonePhi r N = (Real.sqrt N + 2 * r) / (N + 1) := by
  have hn1 : N + 1 ≠ 0 := ne_of_gt (by linarith)
  unfold V22.Z0 monotonePhi activityNu
  field_simp [hN.ne', hn1]
  linear_combination (2 * r) * (Real.sq_sqrt hN.le)

theorem monotone_quartic_domains {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    0 < V22.Z0 N ∧ V22.Z0 N < 1 ∧ 0 < monotonePhi r N ∧
      0 < V22.Z0 N * monotonePhi r N ∧ V22.Z0 N * monotonePhi r N < 1 ∧
      0 ≤ r + V22.Z0 N ∧ r + V22.Z0 N < 1 := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hsr := Real.sq_sqrt hn.le
  have hs0 := Real.sqrt_pos.2 hn
  have hsN : Real.sqrt N < N := by nlinarith
  have hsHalf : 2 * Real.sqrt N < N + 1 := by nlinarith
  have hZ0 : 0 < V22.Z0 N := div_pos hs0 hn1
  have hZ1 : V22.Z0 N < 1 := (div_lt_one hn1).2 (by exact hsN.trans (by linarith))
  have hphi : 0 < monotonePhi r N := by
    unfold monotonePhi
    have hnu := activityNu_nonneg (N := N) hr0
    positivity
  have hZphi : V22.Z0 N * monotonePhi r N < 1 := by
    rw [monotone_Z0_phi_eq hn]
    apply (div_lt_one hn1).2
    linarith
  have hZhalf : V22.Z0 N < 1 / 2 := (div_lt_iff₀ hn1).2 (by linarith)
  exact ⟨hZ0, hZ1, hphi, mul_pos hZ0 hphi, hZphi, by linarith, by linarith⟩

theorem monotone_ZL_upper {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    V22.ZL r N 1 ≤ V22.Z0 N * monotonePhi r N := by
  have hn : 0 < N := by linarith
  have hs := shared_sN_le_half_sqrt hr0 (by linarith : r < 1) hn
  rw [monotone_Z0_phi_eq hn]
  unfold V22.ZL
  norm_num only [Real.sqrt_one, one_mul]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith : 0 ≤ N + 1)

theorem monotone_ZR_upper {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) : V22.ZR r N 1 ≤ V22.Z0 N := by
  have hn : 0 < N := by linarith
  have hs := shared_sN_le_half_sqrt hr0 (by linarith : r < 1) hn
  unfold V22.ZR V22.Z0
  norm_num only [Real.sqrt_one, one_mul]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith : 0 ≤ N + 1)

private theorem quartic_left_ratio_mono {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) :
    s ^ 4 / (1 - s ^ 2) ≤ t ^ 4 / (1 - t ^ 2) := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hdt := shared_one_sub_sq_pos (by linarith : -1 < t) ht1
  have hds := shared_one_sub_sq_pos (by linarith : -1 < s) (hst.trans_lt ht1)
  calc
    _ ≤ t ^ 4 / (1 - s ^ 2) := div_le_div_of_nonneg_right (pow_le_pow_left₀ hs0 hst 4) hds.le
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg ht0 4) hdt (by nlinarith)

private theorem quartic_right_ratio_mono {r s t : ℝ}
    (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) (hst : s ≤ t) (hrt1 : r + t < 1) :
    s ^ 4 / (1 - (r + s) ^ 2) ≤ t ^ 4 / (1 - (r + t) ^ 2) := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hdt := shared_one_sub_sq_pos (by linarith : -1 < r + t) hrt1
  have hds := shared_one_sub_sq_pos (by linarith : -1 < r + s) (by linarith : r + s < 1)
  calc
    _ ≤ t ^ 4 / (1 - (r + s) ^ 2) := div_le_div_of_nonneg_right (pow_le_pow_left₀ hs0 hst 4) hds.le
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg ht0 4) hdt (by nlinarith)

theorem monotone_quarticErrorZero_identity {N : ℝ} (hN : 10 ≤ N) :
    V22.quarticErrorZero N = (N + 1) * (V22.Z0 N) ^ 4 / (12 * (1 - (V22.Z0 N) ^ 2)) := by
  have hn : 0 < N := by linarith
  have hn1 : N + 1 ≠ 0 := ne_of_gt (by linarith)
  have hp : N ^ 2 + N + 1 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg N])
  have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hn.le
  have hs4 : Real.sqrt N ^ 4 = N ^ 2 := by
    calc
      Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 := by ring
      _ = N ^ 2 := by rw [hs2]
  unfold V22.quarticErrorZero V22.Z0
  rw [div_pow, div_pow, hs2, hs4]
  have hd : 1 - N / (N + 1) ^ 2 ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    apply (div_lt_one (sq_pos_of_pos (by linarith : 0 < N + 1))).2
    nlinarith
  have hp' : 1 + N + N ^ 2 ≠ 0 := by positivity
  field_simp [hn1, hp, hd] <;> ring_nf <;> field_simp [hp'] <;> ring

theorem monotone_PsiR_ratio {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    monotonePsiR r N = (1 - (V22.Z0 N) ^ 2) /
      ((1 - (r + V22.Z0 N) ^ 2) * (1 - r ^ 2)) := by
  have hn : 0 < N := by linarith
  obtain ⟨_, _, _, _, _, hrt0, hrt1⟩ := monotone_quartic_domains hr0 hrh hN
  have hdr := (shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)).ne'
  have hdt := (shared_one_sub_sq_pos (by linarith : -1 < r + V22.Z0 N) hrt1).ne'
  unfold monotonePsiR
  rw [activityNu_quotient hn]
  field_simp [hdr, hdt] <;> ring

theorem monotone_PsiR_ge_one {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) : 1 ≤ monotonePsiR r N := by
  obtain ⟨hZ0, _, _, _, _, hrt0, hrt1⟩ := monotone_quartic_domains hr0 hrh hN
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hdt := shared_one_sub_sq_pos (by linarith : -1 < r + V22.Z0 N) hrt1
  rw [monotone_PsiR_ratio hr0 hrh hN]
  apply (le_div_iff₀ (mul_pos hdt hdr)).2
  have h1 : (1 - (r + V22.Z0 N) ^ 2) * (1 - r ^ 2) ≤ 1 - (r + V22.Z0 N) ^ 2 := by
    nlinarith [mul_nonneg hdt.le (sq_nonneg r)]
  have h2 : 1 - (r + V22.Z0 N) ^ 2 ≤ 1 - (V22.Z0 N) ^ 2 := by nlinarith
  simpa only [one_mul] using h1.trans h2

theorem monotone_quartic_error_bound {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    V22.quarticError r N 1 ≤ V22.quarticErrorZero N * max (monotonePsiL r N) (monotonePsiR r N) := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  obtain ⟨hZ0, hZ1, _, hZphi0, hZphi1, hrt0, hrt1⟩ := monotone_quartic_domains hr0 hrh hN
  obtain ⟨hZL0, _, hZR0, _⟩ := shared_gaussian_window_domains hr0 hrh hN
  have hdz := shared_one_sub_sq_pos (by linarith : -1 < V22.Z0 N) hZ1
  have hdp := shared_one_sub_sq_pos (by linarith : -1 < V22.Z0 N * monotonePhi r N) hZphi1
  have hdt := shared_one_sub_sq_pos (by linarith : -1 < r + V22.Z0 N) hrt1
  have he0 : 0 ≤ V22.quarticErrorZero N := by unfold V22.quarticErrorZero; positivity
  have hEL := mul_le_mul_of_nonneg_left
    (quartic_left_ratio_mono hZL0.le (monotone_ZL_upper hr0 hrh hN) hZphi1)
    (div_pos hn1 (mul_pos (by norm_num : (0 : ℝ) < 12) hdr)).le
  have hER := mul_le_mul_of_nonneg_left
    (quartic_right_ratio_mono hr0 hZR0.le (monotone_ZR_upper hr0 hrh hN) hrt1)
    (div_pos hn1 (mul_pos (by norm_num : (0 : ℝ) < 12) hdr)).le
  have hLEq : (N + 1) / (12 * (1 - r ^ 2)) *
      ((V22.Z0 N * monotonePhi r N) ^ 4 / (1 - (V22.Z0 N * monotonePhi r N) ^ 2)) =
      V22.quarticErrorZero N * monotonePsiL r N := by
    rw [monotone_quarticErrorZero_identity hN]
    unfold monotonePsiL
    rw [activityNu_quotient hn]
    have he : 1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2 ≠ 0 := by
      rw [← mul_pow]
      exact hdp.ne'
    field_simp [hdr.ne', hdz.ne', hdp.ne', he] <;> ring
  have hREq : (N + 1) / (12 * (1 - r ^ 2)) *
      ((V22.Z0 N) ^ 4 / (1 - (r + V22.Z0 N) ^ 2)) =
      V22.quarticErrorZero N * monotonePsiR r N := by
    rw [monotone_quarticErrorZero_identity hN, monotone_PsiR_ratio hr0 hrh hN]
    field_simp [hdr.ne', hdz.ne', hdt.ne'] <;> ring
  rw [hLEq] at hEL
  rw [hREq] at hER
  unfold V22.quarticError
  apply max_le
  · apply le_trans _ (mul_le_mul_of_nonneg_left (le_max_left _ _) he0)
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hEL
  · apply le_trans _ (mul_le_mul_of_nonneg_left (le_max_right _ _) he0)
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hER

theorem monotone_scaled_quartic_positivePart {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    (N + 1) * V22.positivePart (V22.quarticError r N 1 - V22.quarticErrorZero N) ≤
      (1 / 12 : ℝ) * (max (monotonePsiL r N) (monotonePsiR r N) - 1) := by
  have hn1 : 0 < N + 1 := by linarith
  have he0 : 0 ≤ V22.quarticErrorZero N := by unfold V22.quarticErrorZero; positivity
  have hp : 0 ≤ max (monotonePsiL r N) (monotonePsiR r N) - 1 := by
    linarith [le_max_right (monotonePsiL r N) (monotonePsiR r N), monotone_PsiR_ge_one hr0 hrh hN]
  have hq := monotone_quartic_error_bound hr0 hrh hN
  have hpp : V22.positivePart (V22.quarticError r N 1 - V22.quarticErrorZero N) ≤
      V22.quarticErrorZero N * (max (monotonePsiL r N) (monotonePsiR r N) - 1) := by
    unfold V22.positivePart
    apply max_le
    · nlinarith
    · exact mul_nonneg he0 hp
  have he0s : (N + 1) * V22.quarticErrorZero N ≤ (1 / 12 : ℝ) := by
    unfold V22.quarticErrorZero
    have hpoly : 0 < N ^ 2 + N + 1 := by nlinarith [sq_nonneg N]
    have heq : (N + 1) * (N ^ 2 / (12 * (N + 1) * (N ^ 2 + N + 1))) =
        N ^ 2 / (12 * (N ^ 2 + N + 1)) := by
      field_simp [hn1.ne', hpoly.ne'] <;> ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 12) hpoly)).2
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hpp hn1.le
  have hsecond := mul_le_mul_of_nonneg_right he0s hp
  nlinarith

theorem monotone_scaled_c0 {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    (N + 1) * V22.c0 r N = 2 * activityNu r N ^ 2 / (N - activityNu r N ^ 2) := by
  have hn : 0 < N := by linarith
  have hn1 : N + 1 ≠ 0 := ne_of_gt (by linarith)
  have hdr := (shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)).ne'
  rw [activityNu_gap hn, activityNu_sq hn.le]
  unfold V22.c0 V22.varianceR
  field_simp [hn.ne', hn1, hdr] <;> ring

theorem monotone_scaled_epsilon {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    (N + 1) * V22.epsilon r N = 2 * activityNu r N / Real.sqrt (1 - activityNu r N ^ 2 / N) := by
  have hn : 0 < N := by linarith
  have hn1 : N + 1 ≠ 0 := ne_of_gt (by linarith)
  have hv := shared_varianceR_pos hr0 (by linarith : r < 1)
  have hs : 0 < Real.sqrt (V22.varianceR r) := Real.sqrt_pos.2 hv
  have he : Real.sqrt (1 - r ^ 2) = 2 * Real.sqrt (V22.varianceR r) := by
    have hvr : 1 - r ^ 2 = 4 * V22.varianceR r := by unfold V22.varianceR; ring
    rw [hvr, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [activityNu_quotient hn, he]
  unfold V22.epsilon activityNu
  field_simp [hn1, hs.ne'] <;> ring

/-- Exact source Lemma 4.9(a), including the two quartic branches. -/
theorem monotone_eL_upper {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    (N + 1) * V22.eL r N ≤ 2 * activityNu r N ^ 2 / (N - activityNu r N ^ 2) +
      2 * activityNu r N / Real.sqrt (1 - activityNu r N ^ 2 / N) +
      (1 / 12 : ℝ) * (max (monotonePsiL r N) (monotonePsiR r N) - 1) := by
  have hq := monotone_scaled_quartic_positivePart hr0 hrh hN
  have hc := monotone_scaled_c0 hr0 hrh hN
  have he := monotone_scaled_epsilon hr0 hrh hN
  unfold V22.eL
  nlinarith

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.monotonePhi
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotonePhi
#check Erdos993Lean.Analytic.V22.Analysis.monotonePsiL
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotonePsiL
#check Erdos993Lean.Analytic.V22.Analysis.monotonePsiR
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotonePsiR
#check Erdos993Lean.Analytic.V22.Analysis.monotone_Z0_phi_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_Z0_phi_eq
#check Erdos993Lean.Analytic.V22.Analysis.monotone_quartic_domains
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_quartic_domains
#check Erdos993Lean.Analytic.V22.Analysis.monotone_ZL_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_ZL_upper
#check Erdos993Lean.Analytic.V22.Analysis.monotone_ZR_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_ZR_upper
#check Erdos993Lean.Analytic.V22.Analysis.quartic_left_ratio_mono
#print axioms Erdos993Lean.Analytic.V22.Analysis.quartic_left_ratio_mono
#check Erdos993Lean.Analytic.V22.Analysis.quartic_right_ratio_mono
#print axioms Erdos993Lean.Analytic.V22.Analysis.quartic_right_ratio_mono
#check Erdos993Lean.Analytic.V22.Analysis.monotone_quarticErrorZero_identity
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_quarticErrorZero_identity
#check Erdos993Lean.Analytic.V22.Analysis.monotone_PsiR_ratio
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_PsiR_ratio
#check Erdos993Lean.Analytic.V22.Analysis.monotone_PsiR_ge_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_PsiR_ge_one
#check Erdos993Lean.Analytic.V22.Analysis.monotone_quartic_error_bound
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_quartic_error_bound
#check Erdos993Lean.Analytic.V22.Analysis.monotone_scaled_quartic_positivePart
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_scaled_quartic_positivePart
#check Erdos993Lean.Analytic.V22.Analysis.monotone_scaled_c0
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_scaled_c0
#check Erdos993Lean.Analytic.V22.Analysis.monotone_scaled_epsilon
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_scaled_epsilon
#check Erdos993Lean.Analytic.V22.Analysis.monotone_eL_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.monotone_eL_upper
