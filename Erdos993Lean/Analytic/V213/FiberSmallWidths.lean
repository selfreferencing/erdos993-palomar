module

public import Erdos993Lean.Analytic.V213.FiberSmallCheck
public import Erdos993Lean.Analytic.V213.FiberSmallKernel
public import Erdos993Lean.Analytic.V213.LowMeanKernelIdentities

/-!
Literal Lemma6.20. All integer ranks,
including the two spikes, both zero tails and width zero, are covered.
The accepted finite values bind actual U; arbitrary larger widths follow
from the exact accepted Pascal recurrence with nonnegative convex weights.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberSmallK : ℕ → ℝ
  | 0 => 51 / 200 | 1 => 17 / 125 | 2 => 159 / 2000 | 3 => 61 / 1250
  | 4 => 161 / 5000 | 5 => 129 / 5000 | 6 => 101 / 5000 | _ => 81 / 5000

theorem fiber_small_named_cap (id : FiberSmallIdentity) :
    lowMeanFractionReal (fiberSmallById id).cap = fiberSmallK (fiberSmallWidth id) := by
  cases id <;> norm_num [fiberSmallById, fiberSmallWidth, fiberSmallK, lowMeanFractionReal]

noncomputable def fiberSmallMaximum : ℕ → ℝ
  | 0 => 1 / 4 | 1 => 2187 / 16384 | 2 => 243 / 3125 | 3 => 3125 / 65536
  | 4 => 1 / 32 | 5 => 4 * (17 / 32 : ℝ) ^ (8 : ℕ)
  | 6 => 4 * (5 / 9 : ℝ) ^ (9 : ℕ) | _ => 4 * (23 / 40 : ℝ) ^ (10 : ℕ)

theorem fiber_small_named_maximum (id : FiberSmallIdentity) :
    lowMeanFractionReal (fiberSmallById id).maximum =
      fiberSmallMaximum (fiberSmallWidth id) := by
  have h := fiber_small_named_checked id
  simp only [fiberSmallWidthCheck, Bool.and_eq_true] at h
  have hw := of_decide_eq_true h.1
  rcases hw with ⟨_,_,_,_,_,hm,_,_,hp,_,_,he,_,_,_,_,_⟩
  rw [(lowMean_fraction_eq_iff hm hp).mp he]
  cases id <;> simp only [fiberSmallExpectedMaximum, fiberSmallWidth, fiberSmallMaximum,
    lowMean_fraction_mul, lowMean_fraction_pow] <;>
    norm_num only [lowMeanFractionReal, Int.cast_ofNat, Nat.cast_ofNat, div_one]

theorem fiber_small_identity_covers {M : ℕ} (hM : M ≤ 7) :
    fiberSmallWidth (fiberSmallIdentityAt M) = M := by
  interval_cases M <;> rfl

theorem fiber_small_named_kernel (id : FiberSmallIdentity) {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 4) (3 / 4)) (j : ℤ) :
    -lowMeanFractionReal (fiberSmallById id).cap ≤
      kernel2 q (fiberWeightL q) (fiberWeightR q) (fiberSmallWidth id) j := by
  let M := fiberSmallWidth id
  have hc := fiber_small_cap_nonneg id
  by_cases hout : j < -1 ∨ (M : ℤ) + 1 < j
  · rw [lowMean_kernel_outside M q (fiberWeightL q) (fiberWeightR q) j hout]
    linarith
  · have hj0 : 0 ≤ j + 1 := by omega
    obtain ⟨J,hJ⟩ := Int.eq_ofNat_of_zero_le hj0
    have hj : j = (J : ℤ) - 1 := by omega
    have hJN : J ≤ M + 2 := by omega
    have hk := fiber_small_supported_kernel M hJN
      (q := q) (by linarith [hq.1]) (by linarith [hq.2])
    have hu := fiber_small_U_le_maximum id hJN
    have hcap := fiber_small_maximum_lt_cap id
    rw [← hj] at hk
    linarith

theorem fiber_small_all_printed_maxima (id : FiberSmallIdentity) :
    (∀ J ≤ fiberSmallWidth id + 2,
      fiberSmallU (fiberSmallWidth id + 2) J ≤ fiberSmallMaximum (fiberSmallWidth id)) ∧
    (fiberSmallById id).witnessJ ≤ fiberSmallWidth id + 2 ∧
    fiberSmallU (fiberSmallWidth id + 2) (fiberSmallById id).witnessJ =
      fiberSmallMaximum (fiberSmallWidth id) := by
  constructor
  · intro J hJ
    rw [← fiber_small_named_maximum]
    exact fiber_small_U_le_maximum id hJ
  · rw [← fiber_small_named_maximum]
    exact fiber_small_maximum_attained id

/-- Literal first clause of Lemma6.20, all eight printed widths. -/
theorem fiber_small_width_kernel {M : ℕ} (hM : M ≤ 7) {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 4) (3 / 4)) (j : ℤ) :
    -fiberSmallK M ≤ kernel2 q (fiberWeightL q) (fiberWeightR q) M j := by
  have h := fiber_small_named_kernel (fiberSmallIdentityAt M) hq j
  rw [fiber_small_named_cap, fiber_small_identity_covers hM] at h
  exact h

/-- Literal geometric clause, including equality at width zero. -/
theorem fiber_small_width_geometric {M : ℕ} (hM : M ≤ 7) :
    fiberSmallK M ≤ (51 / 200 : ℝ) * (27 / 40 : ℝ) ^ M := by
  have h := fiber_small_geometric_cap (fiberSmallIdentityAt M)
  rw [fiber_small_named_cap, fiber_small_identity_covers hM] at h
  exact h

theorem fiber_small_zero_geometric :
    fiberSmallK 0 = (51 / 200 : ℝ) * (27 / 40 : ℝ) ^ (0 : ℕ) := by
  norm_num [fiberSmallK]

theorem fiber_weighted_kernel_pascal (q : ℝ) (M : ℕ) (j : ℤ) :
    kernel2 q (fiberWeightL q) (fiberWeightR q) (M + 1) j =
      (1 - q) * kernel2 q (fiberWeightL q) (fiberWeightR q) M j +
        q * kernel2 q (fiberWeightL q) (fiberWeightR q) M (j - 1) := by
  rw [kernel2_heat]
  ring

/-- Literal final clause of Lemma6.20, on the full infinite width/rank domain. -/
theorem fiber_large_width_kernel {M : ℕ} (hM : 7 ≤ M) {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 4) (3 / 4)) (j : ℤ) :
    -(81 / 5000 : ℝ) ≤ kernel2 q (fiberWeightL q) (fiberWeightR q) M j := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hq1 : 0 ≤ 1 - q := by linarith [hq.2]
  have h : ∀ n : ℕ, ∀ j : ℤ,
      -(81 / 5000 : ℝ) ≤ kernel2 q (fiberWeightL q) (fiberWeightR q) (7 + n) j := by
    intro n
    induction n with
    | zero =>
      intro j
      simpa [fiberSmallK] using fiber_small_width_kernel (M := 7) (by decide +kernel) hq j
    | succ n ih =>
      intro j
      rw [show 7 + (n + 1) = (7 + n) + 1 by omega, fiber_weighted_kernel_pascal]
      have h1 := mul_le_mul_of_nonneg_left (ih j) hq1
      have h2 := mul_le_mul_of_nonneg_left (ih (j - 1)) hq0
      linarith
  simpa [Nat.add_sub_of_le hM] using h (M - 7) j

end Erdos993Lean.Analytic.V213
