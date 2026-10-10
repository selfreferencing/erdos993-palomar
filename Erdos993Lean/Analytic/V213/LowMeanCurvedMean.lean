module

public import Erdos993Lean.Analytic.V213.LowMeanRate

/-!
The three curved lower boundaries in r12:secA.5, equations
r12:eq62--63. The derivative, endpoint-sign implications, branch switch,
and exponential comparison are proved generically. Generated endpoint
values are not consumed in this module.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCurvedA (alpha beta gamma m0 eta theta D q : ℝ) : ℝ :=
  lowMeanPsi alpha beta gamma m0 (4 / q) - 4 * gamma * D / q - 4 * eta * theta * (1 - q)
def lowMeanCurvedB (beta gamma m0 D : ℝ) : ℝ := 4 * beta + 8 * gamma * m0 - 4 * gamma * D
def lowMeanCurvedH (beta gamma m0 eta theta D q : ℝ) : ℝ :=
  4 * eta * theta * q ^ 3 - lowMeanCurvedB beta gamma m0 D * q + 32 * gamma
def lowMeanCurvedHD (beta gamma m0 eta theta D q : ℝ) : ℝ :=
  12 * eta * theta * q ^ 2 - lowMeanCurvedB beta gamma m0 D

theorem lowMean_curvedA_deriv (alpha beta gamma m0 eta theta D : ℝ)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (lowMeanCurvedA alpha beta gamma m0 eta theta D)
      (lowMeanCurvedH beta gamma m0 eta theta D q / q ^ 3) q := by
  have hi := (hasDerivAt_const q (4 : ℝ)).div (hasDerivAt_id q) hq.ne'
  have hp := ((hi.sub_const m0).const_mul beta).const_add alpha
  have hs := ((hi.sub_const m0).pow 2).const_mul gamma
  have hd := (hasDerivAt_const q (4 * gamma * D)).div (hasDerivAt_id q) hq.ne'
  have he := ((hasDerivAt_id q).const_sub 1).const_mul (4 * eta * theta)
  convert ((hp.sub hs).sub hd).sub he using 1
  · rfl
  · dsimp
    unfold lowMeanCurvedH lowMeanCurvedB
    field_simp
    ring

theorem lowMean_curvedH_deriv (beta gamma m0 eta theta D q : ℝ) :
    HasDerivAt (lowMeanCurvedH beta gamma m0 eta theta D)
      (lowMeanCurvedHD beta gamma m0 eta theta D q) q := by
  convert ((((hasDerivAt_id q).pow 3).const_mul (4 * eta * theta)).sub
    ((hasDerivAt_id q).const_mul (lowMeanCurvedB beta gamma m0 D))).add_const (32 * gamma) using 1
  · rfl
  · dsimp [lowMeanCurvedHD]
    ring

theorem lowMean_curvedHD_deriv (beta gamma m0 eta theta D q : ℝ) :
    HasDerivAt (lowMeanCurvedHD beta gamma m0 eta theta D) (24 * eta * theta * q) q := by
  convert (((hasDerivAt_id q).pow 2).const_mul (12 * eta * theta)).sub_const
    (lowMeanCurvedB beta gamma m0 D) using 1
  · rfl
  · dsimp
    ring

/-- Nonpositive endpoint values of the convex H imply a decreasing A.
This is the printed argument for certificates 1 and 2. -/
theorem lowMean_curvedA_antitone
    {alpha beta gamma m0 eta theta D l h : ℝ} (hl : 0 < l)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hleft : lowMeanCurvedH beta gamma m0 eta theta D l ≤ 0)
    (hright : lowMeanCurvedH beta gamma m0 eta theta D h ≤ 0) :
    AntitoneOn (lowMeanCurvedA alpha beta gamma m0 eta theta D) (Set.Icc l h) := by
  have hneg : ConcaveOn ℝ (Set.Icc l h) (fun q => -lowMeanCurvedH beta gamma m0 eta theta D q) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l h)
      (fun q _ => ((lowMean_curvedH_deriv beta gamma m0 eta theta D q).neg).continuousAt.continuousWithinAt)
      (fun q _ => ((lowMean_curvedH_deriv beta gamma m0 eta theta D q).neg).hasDerivWithinAt)
      (fun q _ => ((lowMean_curvedHD_deriv beta gamma m0 eta theta D q).neg).hasDerivWithinAt)
    intro q hq
    have hq0 : 0 ≤ q := le_of_lt (lt_of_lt_of_le hl (interior_subset hq).1)
    have hh := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) heta) htheta) hq0
    linarith
  have hH q (hq : q ∈ Set.Icc l h) : lowMeanCurvedH beta gamma m0 eta theta D q ≤ 0 := by
    have hh := lowMean_concave_endpoint_min hneg hq
    have hm : 0 ≤ min (-lowMeanCurvedH beta gamma m0 eta theta D l)
        (-lowMeanCurvedH beta gamma m0 eta theta D h) := le_min (by linarith) (by linarith)
    linarith
  have hd q (hq : q ∈ Set.Icc l h) := lowMean_curvedA_deriv alpha beta gamma m0 eta theta D
    (q := q) (lt_of_lt_of_le hl hq.1)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l h)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (interior_subset hq)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc l h := interior_subset hq
  exact div_nonpos_of_nonpos_of_nonneg (hH q hq') (pow_nonneg (by linarith [hq'.1]) 3)

/-- Nonnegative H(l), H'(l) imply an increasing A. This is the printed
argument for certificate 24. -/
theorem lowMean_curvedA_monotone
    {alpha beta gamma m0 eta theta D l h : ℝ} (hl : 0 < l)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hleft : 0 ≤ lowMeanCurvedH beta gamma m0 eta theta D l)
    (hleftD : 0 ≤ lowMeanCurvedHD beta gamma m0 eta theta D l) :
    MonotoneOn (lowMeanCurvedA alpha beta gamma m0 eta theta D) (Set.Icc l h) := by
  have hHD q (hq : q ∈ Set.Icc l h) : 0 ≤ lowMeanCurvedHD beta gamma m0 eta theta D q := by
    have hq2 : l ^ 2 ≤ q ^ 2 := by nlinarith [hq.1]
    have hh := mul_le_mul_of_nonneg_left hq2 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) heta) htheta)
    unfold lowMeanCurvedHD at *
    linarith
  have hHmono : MonotoneOn (lowMeanCurvedH beta gamma m0 eta theta D) (Set.Icc l h) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l h)
      (fun q _ => (lowMean_curvedH_deriv beta gamma m0 eta theta D q).continuousAt.continuousWithinAt)
      (fun q _ => (lowMean_curvedH_deriv beta gamma m0 eta theta D q).hasDerivWithinAt)
    intro q hq
    exact hHD q (interior_subset hq)
  have hH q (hq : q ∈ Set.Icc l h) : 0 ≤ lowMeanCurvedH beta gamma m0 eta theta D q :=
    le_trans hleft (hHmono ⟨le_rfl, le_trans hq.1 hq.2⟩ hq hq.1)
  have hd q (hq : q ∈ Set.Icc l h) := lowMean_curvedA_deriv alpha beta gamma m0 eta theta D
    (q := q) (lt_of_lt_of_le hl hq.1)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l h)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (interior_subset hq)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc l h := interior_subset hq
  exact div_nonneg (hH q hq') (pow_nonneg (by linarith [hq'.1]) 3)

theorem lowMean_rateRatio_identity {q : ℝ} (hq : q ≠ 0) :
    lowMeanRate q / q = lowMeanRateRatioBase q +
      (if q < 3 / 7 then -1 / 125 else 3 / 1250) / q := by
  unfold lowMeanRate lowMeanRateBase lowMeanRateRatioBase
  field_simp

/-- Endpoint and low-limit tests prove the rate-ratio floor, including the
switch point's actual upper-branch value. -/
theorem lowMean_rateRatio_floor {l h q rho : ℝ} (hl : (1 / 4 : ℝ) ≤ l) (hh : h < 1)
    (hq : q ∈ Set.Icc l h) (hH : rho ≤ lowMeanRate h / h)
    (hSwitch : l < 3 / 7 → 3 / 7 ≤ h →
      rho ≤ lowMeanRateRatioBase (3 / 7) + (-1 / 125) / (3 / 7)) :
    rho ≤ lowMeanRate q / q := by
  have hq0 : 0 < q := by linarith [hq.1]
  have hh0 : 0 < h := by linarith [hq.2]
  rw [lowMean_rateRatio_identity hq0.ne']
  by_cases hqlo : q < 3 / 7
  · rw [ite_eq_left hqlo]
    by_cases hhlo : h < 3 / 7
    · have hm := lowMean_rateRatio_branch_antitone hl hh (Or.inl rfl : (-1 / 125 : ℝ) = -1 / 125 ∨ 0 ≤ (-1 / 125 : ℝ))
        hq ⟨le_trans hq.1 hq.2, le_rfl⟩ hq.2
      rw [lowMean_rateRatio_identity hh0.ne', ite_eq_left hhlo] at hH
      exact le_trans hH hm
    · have hllo : l < 3 / 7 := lt_of_le_of_lt hq.1 hqlo
      have hm := lowMean_rateRatio_branch_antitone (l := l) (h := 3 / 7) hl (by norm_num)
        (Or.inl rfl : (-1 / 125 : ℝ) = -1 / 125 ∨ 0 ≤ (-1 / 125 : ℝ))
        ⟨hq.1, hqlo.le⟩ ⟨hllo.le, le_rfl⟩ hqlo.le
      exact le_trans (hSwitch hllo (le_of_not_gt hhlo)) hm
  · rw [ite_eq_right hqlo]
    have hhhi : ¬ h < 3 / 7 := by linarith [hq.2]
    have hm := lowMean_rateRatio_branch_antitone hl hh
      (Or.inr (by norm_num) : (3 / 1250 : ℝ) = -1 / 125 ∨ 0 ≤ (3 / 1250 : ℝ))
      hq ⟨le_trans hq.1 hq.2, le_rfl⟩ hq.2
    rw [lowMean_rateRatio_identity hh0.ne', ite_eq_right hhhi] at hH
    exact le_trans hH hm

theorem lowMean_curved_margin_lower
    {alpha beta gamma m0 eta theta D z q qstar rho : ℝ}
    (hq : 0 < q) (hz : 0 ≤ z) (hrho : 0 ≤ rho)
    (hfloor : rho ≤ lowMeanRate q / q)
    (hA : lowMeanCurvedA alpha beta gamma m0 eta theta D qstar ≤
      lowMeanCurvedA alpha beta gamma m0 eta theta D q) :
    lowMeanCurvedA alpha beta gamma m0 eta theta D qstar - z / lowMeanE60 (4 * rho) ≤
      lowMeanMargin alpha beta gamma m0 eta theta D z (lowMeanRate q) q (4 / q) := by
  have he : lowMeanRate q * (4 / q) = 4 * (lowMeanRate q / q) := by ring
  have htail := lowMean_expTail_le hz (by positivity : 0 ≤ 4 * rho)
    (show 4 * rho ≤ lowMeanRate q * (4 / q) by rw [he]; nlinarith)
  unfold lowMeanMargin
  have ha : lowMeanPsi alpha beta gamma m0 (4 / q) - gamma * D * (4 / q) -
      eta * theta * q * (1 - q) * (4 / q) = lowMeanCurvedA alpha beta gamma m0 eta theta D q := by
    unfold lowMeanCurvedA
    field_simp
  rw [ha]
  simp only [neg_mul]
  linarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_curvedA_antitone
#print axioms Erdos993Lean.Analytic.V213.lowMean_curvedA_monotone
#print axioms Erdos993Lean.Analytic.V213.lowMean_rateRatio_floor
#print axioms Erdos993Lean.Analytic.V213.lowMean_curved_margin_lower
