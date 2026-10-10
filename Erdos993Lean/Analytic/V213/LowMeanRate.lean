module

public import Erdos993Lean.Analytic.V213.LowMeanMeanMargin

/-!
The explicit rate r12:eq61 and the rate-ratio derivative estimate
used at the three curved lower boundaries. Both sides of the upward jump
are treated separately. No finite group or endpoint record is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanRateBase (q : ℝ) : ℝ :=
  2 * q * (1 + 2 * q) * (1 - q) / ((1 + q) * (2 - q))
noncomputable def lowMeanRate (q : ℝ) : ℝ :=
  lowMeanRateBase q + if q < 3 / 7 then -1 / 125 else 3 / 1250
noncomputable def lowMeanRateBaseD (q : ℝ) : ℝ :=
  4 * (q ^ 2 - 3 * q - 1) * (q ^ 2 + q - 1) / ((1 + q) ^ 2 * (2 - q) ^ 2)
noncomputable def lowMeanRateBaseDD (q : ℝ) : ℝ :=
  8 * (1 - 9 * q - 3 * q ^ 2 - 2 * q ^ 3) / ((1 + q) ^ 3 * (2 - q) ^ 3)

theorem lowMean_rateBase_deriv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt lowMeanRateBase (lowMeanRateBaseD q) q := by
  have h1 : 1 + q ≠ 0 := by linarith
  have h2 : 2 - q ≠ 0 := by linarith
  have hd := (((((hasDerivAt_id q).const_mul 2).mul
    (((hasDerivAt_id q).const_mul 2).const_add 1)).mul
    ((hasDerivAt_id q).const_sub 1)).div
    (((hasDerivAt_id q).const_add 1).mul ((hasDerivAt_id q).const_sub 2))
    (mul_ne_zero h1 h2))
  convert hd using 1
  · rfl
  · dsimp
    unfold lowMeanRateBaseD
    field_simp
    ring

theorem lowMean_rateBase_second_deriv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt lowMeanRateBaseD (lowMeanRateBaseDD q) q := by
  have h1 : 1 + q ≠ 0 := by linarith
  have h2 : 2 - q ≠ 0 := by linarith
  have hd1 := (((hasDerivAt_id q).pow 2).sub ((hasDerivAt_id q).const_mul 3)).sub_const 1
  have hd2 := (((hasDerivAt_id q).pow 2).add (hasDerivAt_id q)).sub_const 1
  have hd3 := (((hasDerivAt_id q).const_add 1).pow 2).mul
    (((hasDerivAt_id q).const_sub 2).pow 2)
  have hd := ((hd1.const_mul 4).mul hd2).div hd3 (mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 h2))
  convert hd using 1
  · rfl
  · dsimp
    unfold lowMeanRateBaseDD
    field_simp
    ring

/-- The smooth part is concave throughout all eleven probability groups. -/
theorem lowMean_rateBase_concave : ConcaveOn ℝ (Set.Icc (1 / 4 : ℝ) (7 / 10)) lowMeanRateBase := by
  have hd q (hq : q ∈ Set.Icc (1 / 4 : ℝ) (7 / 10)) :=
    lowMean_rateBase_deriv (q := q) (by linarith [hq.1]) (by linarith [hq.2])
  have hdd q (hq : q ∈ Set.Icc (1 / 4 : ℝ) (7 / 10)) :=
    lowMean_rateBase_second_deriv (q := q) (by linarith [hq.1]) (by linarith [hq.2])
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (interior_subset hq)).hasDerivWithinAt)
    (fun q hq => (hdd q (interior_subset hq)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc (1 / 4 : ℝ) (7 / 10) := interior_subset hq
  unfold lowMeanRateBaseDD
  apply div_nonpos_of_nonpos_of_nonneg
  · have hq0 : 0 ≤ q := by linarith [hq'.1]
    have hq3 := pow_nonneg hq0 3
    nlinarith [sq_nonneg q, hq'.1]
  · have h1 : 0 ≤ 1 + q := by linarith [hq'.1]
    have h2 : 0 ≤ 2 - q := by linarith [hq'.2]
    exact mul_nonneg (pow_nonneg h1 3) (pow_nonneg h2 3)

theorem lowMean_rateBase_monotone_low :
    MonotoneOn lowMeanRateBase (Set.Icc (1 / 4 : ℝ) (3 / 7)) := by
  have hd q (hq : q ∈ Set.Icc (1 / 4 : ℝ) (3 / 7)) :=
    lowMean_rateBase_deriv (q := q) (by linarith [hq.1]) (by linarith [hq.2])
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (interior_subset hq)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc (1 / 4 : ℝ) (3 / 7) := interior_subset hq
  have hq0 : 0 ≤ q := by linarith [hq'.1]
  have hqsmall : q ^ 2 + q - 1 ≤ 0 := by nlinarith [hq'.2]
  have hqother : q ^ 2 - 3 * q - 1 ≤ 0 := by nlinarith [hq'.2]
  unfold lowMeanRateBaseD
  exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by nlinarith) hqsmall)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem lowMean_concave_endpoint_min {f : ℝ → ℝ} {l h q : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc l h) f) (hq : q ∈ Set.Icc l h) : min (f l) (f h) ≤ f q := by
  by_cases hlh : l < h
  · have hd : 0 < h - l := sub_pos.mpr hlh
    have hs := lowMean_concave_chord hlh hf hq
    have ha : 0 ≤ (h - q) / (h - l) := div_nonneg (sub_nonneg.mpr hq.2) hd.le
    have hb : 0 ≤ (q - l) / (h - l) := div_nonneg (sub_nonneg.mpr hq.1) hd.le
    have hab : (h - q) / (h - l) + (q - l) / (h - l) = 1 := by field_simp; ring
    have h1 := mul_le_mul_of_nonneg_left (min_le_left (f l) (f h)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_right (f l) (f h)) hb
    have he : (h - q) / (h - l) * min (f l) (f h) +
        (q - l) / (h - l) * min (f l) (f h) = min (f l) (f h) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · have he : q = l := by linarith [hq.1, hq.2]
    rw [he]
    exact min_le_left _ _

/-- The exact endpoint floor used in all eleven mean budgets, including a
group crossing the jump. The jump occurs before the smooth maximum. -/
theorem lowMean_rate_endpoint_min {l h q : ℝ} (hl : (1 / 4 : ℝ) ≤ l)
    (hh : h ≤ (7 / 10 : ℝ)) (hq : q ∈ Set.Icc l h) :
    min (lowMeanRate l) (lowMeanRate h) ≤ lowMeanRate q := by
  have hlh := le_trans hq.1 hq.2
  have hbase := lowMean_concave_endpoint_min
    (lowMean_rateBase_concave.subset (by intro x hx; exact ⟨le_trans hl hx.1, le_trans hx.2 hh⟩)
      (convex_Icc l h)) hq
  by_cases hqlo : q < 3 / 7
  · have hllo : l < 3 / 7 := lt_of_le_of_lt hq.1 hqlo
    by_cases hhlo : h < 3 / 7
    · simpa [lowMeanRate, hqlo, hllo, hhlo, min_sub_sub_right] using
        (add_le_add_right hbase (-1 / 125))
    · have hm := lowMean_rateBase_monotone_low ⟨hl, hllo.le⟩
        ⟨le_trans hl hq.1, hqlo.le⟩ hq.1
      apply le_trans (min_le_left _ _)
      simpa [lowMeanRate, hqlo, hllo] using add_le_add_right hm (-1 / 125)
  · have hhhi : ¬ h < 3 / 7 := by linarith [hq.2]
    have hleft : lowMeanRate l ≤ lowMeanRateBase l + 3 / 1250 := by
      unfold lowMeanRate
      split_ifs <;> linarith
    have hright : lowMeanRate h = lowMeanRateBase h + 3 / 1250 := by simp [lowMeanRate, hhhi]
    change _ ≤ lowMeanRateBase q + if q < 3 / 7 then -1 / 125 else 3 / 1250
    rw [ite_eq_right hqlo]
    calc
      min (lowMeanRate l) (lowMeanRate h) ≤ min (lowMeanRateBase l + 3 / 1250)
          (lowMeanRateBase h + 3 / 1250) := min_le_min hleft hright.le
      _ = min (lowMeanRateBase l) (lowMeanRateBase h) + 3 / 1250 := min_add_add_right _ _ _
      _ ≤ lowMeanRateBase q + 3 / 1250 := by linarith

noncomputable def lowMeanRateRatioBase (q : ℝ) : ℝ :=
  2 * (1 + 2 * q) * (1 - q) / ((1 + q) * (2 - q))
noncomputable def lowMeanRateRatioBaseD (q : ℝ) : ℝ :=
  -2 * (q ^ 2 + 6 * q - 1) / ((2 - q) ^ 2 * (1 + q) ^ 2)

theorem lowMean_rateRatioBase_deriv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt lowMeanRateRatioBase (lowMeanRateRatioBaseD q) q := by
  have h1 : 1 + q ≠ 0 := by linarith
  have h2 : 2 - q ≠ 0 := by linarith
  have hd := (((((hasDerivAt_id q).const_mul 2).const_add 1).const_mul 2).mul
    ((hasDerivAt_id q).const_sub 1)).div
    (((hasDerivAt_id q).const_add 1).mul ((hasDerivAt_id q).const_sub 2)) (mul_ne_zero h1 h2)
  convert hd using 1
  · rfl
  · dsimp
    unfold lowMeanRateRatioBaseD
    field_simp
    ring

/-- The printed uniform derivative bound -2/9 for r(q). -/
theorem lowMean_rateRatioBase_deriv_le {q : ℝ} (hq : (1 / 4 : ℝ) ≤ q) (hq1 : q < 1) :
    lowMeanRateRatioBaseD q ≤ -2 / 9 := by
  have hq0 : 0 < q := by linarith
  have hD0 : 0 < (2 - q) * (1 + q) := mul_pos (by linarith) (by linarith)
  have hD : (2 - q) * (1 + q) ≤ 9 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hN : 9 / 16 ≤ q ^ 2 + 6 * q - 1 := by nlinarith
  unfold lowMeanRateRatioBaseD
  rw [← mul_pow]
  apply (div_le_iff₀ (pow_pos hD0 2)).mpr
  nlinarith

theorem lowMean_rateRatio_branch_deriv {q c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x : ℝ => lowMeanRateRatioBase x + c / x)
      (lowMeanRateRatioBaseD q - c / q ^ 2) q := by
  have hd := (lowMean_rateRatioBase_deriv hq0 hq1).add
    ((hasDerivAt_const q c).div (hasDerivAt_id q) hq0.ne')
  convert hd using 1
  · rfl
  · dsimp
    ring

/-- Each branch of ell(q)/q decreases; the numerical estimates are exactly
-106/1125 on the low side and -2/9 on the high side. -/
theorem lowMean_rateRatio_branch_antitone {l h c : ℝ}
    (hl : (1 / 4 : ℝ) ≤ l) (hh : h < 1) (hc : c = -1 / 125 ∨ 0 ≤ c) :
    AntitoneOn (fun q : ℝ => lowMeanRateRatioBase q + c / q) (Set.Icc l h) := by
  have hd q (hq : q ∈ Set.Icc l h) := lowMean_rateRatio_branch_deriv
    (c := c) (q := q) (by linarith [hq.1]) (by linarith [hq.2])
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l h)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (interior_subset hq)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc l h := interior_subset hq
  have hqlo : (1 / 4 : ℝ) ≤ q := le_trans hl hq'.1
  have hqhi : q < 1 := lt_of_le_of_lt hq'.2 hh
  have hbound := lowMean_rateRatioBase_deriv_le hqlo hqhi
  rcases hc with hc | hc
  · rw [hc]
    have hq2 : (1 / 16 : ℝ) ≤ q ^ 2 := by nlinarith
    have hrecip : (1 / 125 : ℝ) / q ^ 2 ≤ 16 / 125 := by
      apply (div_le_iff₀ (by nlinarith : 0 < q ^ 2)).mpr
      nlinarith
    calc
      lowMeanRateRatioBaseD q - (-1 / 125) / q ^ 2 =
          lowMeanRateRatioBaseD q + (1 / 125) / q ^ 2 := by ring
      _ ≤ 0 := by linarith
  · have hh := div_nonneg hc (sq_nonneg q)
    linarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_rate_endpoint_min
#print axioms Erdos993Lean.Analytic.V213.lowMean_rateRatioBase_deriv_le
#print axioms Erdos993Lean.Analytic.V213.lowMean_rateRatio_branch_antitone
