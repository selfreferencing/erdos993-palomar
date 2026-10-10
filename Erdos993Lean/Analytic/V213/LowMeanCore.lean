module

public import Erdos993Lean.Analytic.V213.LowMeanKernelFirst

/-!
The exact finite core r12:eq54 and the all-integer exclusion
inequality. The infinite tails are bounded explicitly; no search over a
finite interval is mistaken for coverage of the whole integer axis.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanKernelLInt (M : ℕ) (j : ℤ) (wL wR l h : ℝ) : ℝ :=
  if j = -1 then -wR * (1 - l) ^ M
  else if j = (M : ℤ) + 1 then -wL * h ^ M
  else if 0 ≤ j ∧ j ≤ M then
    lowMeanKernelL M j.toNat
      (wL * (((M : ℝ) + 1 - 2 * j.toNat) / ((M : ℝ) + 1 - j.toNat)))
      (wR * ((2 * (j.toNat : ℝ) + 1 - M) / ((j.toNat : ℝ) + 1))) l h
  else 0

theorem lowMean_kernel_second_lower_int (M : ℕ) (j : ℤ) {l h q wL wR : ℝ}
    (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hl : 0 < l) (hh : h < 1)
    (hq : q ∈ Set.Icc l h) : lowMeanKernelLInt M j wL wR l h ≤ kernel2 q wL wR M j := by
  have hq0 := lt_of_lt_of_le hl hq.1
  have hq1 := lt_of_le_of_lt hq.2 hh
  unfold lowMeanKernelLInt
  split_ifs with hjneg hjtop hj
  · rw [hjneg, lowMean_kernel_neg_one M hq1]
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (by linarith) (by linarith [hq.1]) M)
      (show -wR ≤ 0 by linarith)
  · rw [hjtop, lowMean_kernel_top M hq0]
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hq0.le hq.2 M)
      (show -wL ≤ 0 by linarith)
  · have hn : j.toNat ≤ M := by omega
    have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj.1
    rw [← he]
    simpa only [Int.toNat_natCast] using lowMean_kernel_second_lower hn hwL hwR hl hh hq
  · rw [lowMean_kernel_outside M q wL wR j (by omega)]

noncomputable def lowMeanCoreDistance (M : ℕ) (j : ℤ) (xi eta l h : ℝ) : ℝ :=
  max 0 (max (M * l - ((j : ℝ) + xi / (2 * eta)))
    (((j : ℝ) + xi / (2 * eta)) - M * h))

noncomputable def lowMeanCoreH (M : ℕ) (xi eta alpha beta gamma m0 z zeta h : ℝ) : ℝ :=
  lowMeanPsi alpha beta gamma m0 M + xi ^ 2 / (4 * eta) - z * (1 - h) ^ M + zeta

noncomputable def lowMeanCore (M : ℕ) (wL wR xi eta alpha beta gamma m0 z zeta l h : ℝ) : Set ℤ :=
  {j | eta * lowMeanCoreDistance M j xi eta l h ^ 2 <
      lowMeanCoreH M xi eta alpha beta gamma m0 z zeta h + lowMeanKernelK M j wL wR l h ∧
    eta * lowMeanCoreDistance M j xi eta l h ^ 2 + lowMeanKernelLInt M j wL wR l h <
      lowMeanCoreH M xi eta alpha beta gamma m0 z zeta h}

/-- The explicit max formula is the distance to [Ml,Mh]. -/
theorem lowMean_core_distance_le (M : ℕ) (j : ℤ) (xi eta : ℝ) {l h q : ℝ}
    (hq : q ∈ Set.Icc l h) :
    lowMeanCoreDistance M j xi eta l h ≤ |(j : ℝ) - M * q + xi / (2 * eta)| := by
  have hMl := mul_le_mul_of_nonneg_left hq.1 (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hMh := mul_le_mul_of_nonneg_left hq.2 (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  unfold lowMeanCoreDistance
  apply max_le (abs_nonneg _)
  apply max_le
  · linarith [neg_le_abs ((j : ℝ) - M * q + xi / (2 * eta))]
  · linarith [le_abs_self ((j : ℝ) - M * q + xi / (2 * eta))]

theorem lowMean_core_distance_nonneg (M : ℕ) (j : ℤ) (xi eta l h : ℝ) :
    0 ≤ lowMeanCoreDistance M j xi eta l h := le_max_left _ _

theorem lowMean_complete_square {eta : ℝ} (heta : eta ≠ 0) (xi x : ℝ) :
    eta * x ^ 2 + xi * x = eta * (x + xi / (2 * eta)) ^ 2 - xi ^ 2 / (4 * eta) := by
  field_simp
  ring

/-- The geometric slack bound before either kernel lower bound is applied. -/
theorem lowMean_core_slack (M : ℕ) (j : ℤ)
    {wL wR xi eta alpha beta gamma m0 z zeta l h q : ℝ}
    (heta : 0 < eta) (hz : 0 ≤ z) (hh : h < 1) (hq : q ∈ Set.Icc l h) :
    zeta + eta * lowMeanCoreDistance M j xi eta l h ^ 2 -
        lowMeanCoreH M xi eta alpha beta gamma m0 z zeta h + kernel2 q wL wR M j ≤
      lowMeanH q wL wR xi eta M j - lowMeanPsi alpha beta gamma m0 M + z * (1 - q) ^ M := by
  have hd := lowMean_core_distance_le M j xi eta hq
  have hs := (sq_le_sq₀ (lowMean_core_distance_nonneg M j xi eta l h)
    (abs_nonneg ((j : ℝ) - M * q + xi / (2 * eta)))).mpr hd
  rw [sq_abs] at hs
  have hds := mul_le_mul_of_nonneg_left hs heta.le
  have hp0 : (1 - h) ^ M ≤ (1 - q) ^ M :=
    pow_le_pow_left₀ (sub_pos.mpr hh).le (by linarith [hq.2]) M
  have hp := mul_le_mul_of_nonneg_left hp0 hz
  unfold lowMeanH lowMeanCoreH
  have he := lowMean_complete_square heta.ne' xi ((j : ℝ) - M * q)
  linarith

/-- Equation r12:eq54 excludes every rank failing either strict core test. -/
theorem lowMean_outside_core (M : ℕ) (j : ℤ)
    {wL wR xi eta alpha beta gamma m0 z zeta l h q : ℝ}
    (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (heta : 0 < eta) (hz : 0 ≤ z)
    (hl : 0 < l) (hh : h < 1) (hq : q ∈ Set.Icc l h)
    (hj : j ∉ lowMeanCore M wL wR xi eta alpha beta gamma m0 z zeta l h) :
    zeta ≤ lowMeanH q wL wR xi eta M j - lowMeanPsi alpha beta gamma m0 M + z * (1 - q) ^ M := by
  have hs := lowMean_core_slack M j (wL := wL) (wR := wR) (xi := xi)
    (alpha := alpha) (beta := beta) (gamma := gamma) (m0 := m0) (zeta := zeta) heta hz hh hq
  have hK := lowMean_kernel_first_lower M j hwL hwR hl hh hq
  have hL := lowMean_kernel_second_lower_int M j hwL hwR hl hh hq
  change ¬ (_ ∧ _) at hj
  rcases not_and_or.mp hj with hj | hj
  · have hb := le_of_not_gt hj
    linarith
  · have hb := le_of_not_gt hj
    linarith

/-- Explicit tail boundary tests suffice to cover the full core by a finite
integer range. These arithmetic boundary tests will be checked per fiber. -/
theorem lowMean_core_in_range (M : ℕ) (lo hi : ℤ)
    {wL wR xi eta alpha beta gamma m0 z zeta l h : ℝ}
    (heta : 0 < eta) (hlo : lo < -1) (hhi : (M : ℤ) + 1 < hi)
    (hloSide : (lo : ℝ) + xi / (2 * eta) ≤ M * l)
    (hhiSide : M * h ≤ (hi : ℝ) + xi / (2 * eta))
    (hloBound : lowMeanCoreH M xi eta alpha beta gamma m0 z zeta h ≤
      eta * (M * l - ((lo : ℝ) + xi / (2 * eta))) ^ 2)
    (hhiBound : lowMeanCoreH M xi eta alpha beta gamma m0 z zeta h ≤
      eta * (((hi : ℝ) + xi / (2 * eta)) - M * h) ^ 2)
    {j : ℤ} (hj : j ∈ lowMeanCore M wL wR xi eta alpha beta gamma m0 z zeta l h) :
    lo < j ∧ j < hi := by
  have hd0 := lowMean_core_distance_nonneg M j xi eta l h
  have hjFirst := hj.1
  constructor
  · by_contra hjlo
    have hjlo' : j ≤ lo := le_of_not_gt hjlo
    have hjloR : (j : ℝ) ≤ lo := by exact_mod_cast hjlo'
    have hK0 : lowMeanKernelK M j wL wR l h = 0 := by
      unfold lowMeanKernelK
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [hK0, add_zero] at hjFirst
    have hd : M * l - ((lo : ℝ) + xi / (2 * eta)) ≤ lowMeanCoreDistance M j xi eta l h := by
      exact le_trans (by linarith) (le_trans (le_max_left _ _) (le_max_right _ _))
    have hsq := (sq_le_sq₀ (by linarith : 0 ≤ M * l - ((lo : ℝ) + xi / (2 * eta))) hd0).mpr hd
    have hh := mul_le_mul_of_nonneg_left hsq heta.le
    linarith
  · by_contra hjhi
    have hjhi' : hi ≤ j := le_of_not_gt hjhi
    have hjhiR : (hi : ℝ) ≤ j := by exact_mod_cast hjhi'
    have hK0 : lowMeanKernelK M j wL wR l h = 0 := by
      unfold lowMeanKernelK
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [hK0, add_zero] at hjFirst
    have hd : ((hi : ℝ) + xi / (2 * eta)) - M * h ≤ lowMeanCoreDistance M j xi eta l h := by
      exact le_trans (by linarith) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hsq := (sq_le_sq₀ (by linarith : 0 ≤ ((hi : ℝ) + xi / (2 * eta)) - M * h) hd0).mpr hd
    have hh := mul_le_mul_of_nonneg_left hsq heta.le
    linarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_kernel_second_lower_int
#print axioms Erdos993Lean.Analytic.V213.lowMean_outside_core
#print axioms Erdos993Lean.Analytic.V213.lowMean_core_in_range
