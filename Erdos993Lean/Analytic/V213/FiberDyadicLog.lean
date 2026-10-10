module

public import Erdos993Lean.Analytic.V213.FreeCountRealLogEnvelopes

/-!
The exact Eq89 rational logarithm enclosure, including the
printed log2 slack. The exponent is a natural number and the actual
argument is retained. Reduced witness trees are interpreted by this
formula, not by an unrelated root value. No generated family is used.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real

noncomputable def fiberDyadicLog (n : ℕ) (y : ℝ) : ℝ :=
  1733 * (n : ℝ) / 2500 + FreeCountVariance.Envelopes.seriesT
    ((y / (2 : ℝ) ^ n - 1) / (y / (2 : ℝ) ^ n + 1))

theorem fiber_log_two_strict : Real.log 2 < 1733 / 2500 := by
  have h := (FreeCountVariance.Envelopes.artanh_brackets
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)).2
  norm_num [FreeCountVariance.Envelopes.seriesT,FreeCountVariance.Envelopes.seriesS] at h
  linarith only [h]

theorem fiber_log_two_printed_slack :
    (1733 / 2500 : ℝ) - FreeCountVariance.Envelopes.seriesT (1 / 3) = 52 / 1063125 := by
  norm_num [FreeCountVariance.Envelopes.seriesT,FreeCountVariance.Envelopes.seriesS]

theorem fiber_dyadic_log_bound (n : ℕ) {y : ℝ} (hy : (2 : ℝ) ^ n ≤ y) :
    Real.log y ≤ fiberDyadicLog n y := by
  have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hy0 : 0 < y := hp.trans_le hy
  have hw : 1 ≤ y / (2 : ℝ) ^ n := (one_le_div hp).2 hy
  have hw0 : 0 < y / (2 : ℝ) ^ n := div_pos hy0 hp
  have hd : 0 < y / (2 : ℝ) ^ n + 1 := by positivity
  have hz0 : 0 ≤ (y / (2 : ℝ) ^ n - 1) / (y / (2 : ℝ) ^ n + 1) :=
    div_nonneg (sub_nonneg.mpr hw) hd.le
  have hz1 : (y / (2 : ℝ) ^ n - 1) / (y / (2 : ℝ) ^ n + 1) < 1 :=
    (div_lt_one hd).2 (by linarith only [hw])
  have hlog := (FreeCountVariance.Envelopes.artanh_brackets hz0 hz1).2
  have hid :
      (1 + (y / (2 : ℝ) ^ n - 1) / (y / (2 : ℝ) ^ n + 1)) /
        (1 - (y / (2 : ℝ) ^ n - 1) / (y / (2 : ℝ) ^ n + 1)) = y / (2 : ℝ) ^ n := by
    field_simp [hd.ne',hp.ne']
    ring
  rw [hid] at hlog
  have hfactor : y = (2 : ℝ) ^ n * (y / (2 : ℝ) ^ n) := by field_simp [hp.ne']
  have hylog : Real.log y = (n : ℝ) * Real.log 2 + Real.log (y / (2 : ℝ) ^ n) := by
    conv_lhs => rw [hfactor,Real.log_mul hp.ne' hw0.ne',Real.log_pow]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have htwo := mul_le_mul_of_nonneg_left fiber_log_two_strict.le hn
  unfold fiberDyadicLog
  rw [hylog]
  linarith only [hlog,htwo]

end Erdos993Lean.Analytic.V213
