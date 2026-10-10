module

public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Tactic

/-!
# Version 2.2 of the manuscript, Lemma 3.7: the central-binomial upper bound

Source: the fiber theorem note, Lemma 3.7. The paper's `W_m`
is `centralMass m`; Mathlib's `Real.Wallis.W m` is the Wallis product,
which is a different sequence. The increasing sequence
`centralMass m ^ 2 * (m + 1/4)` converges to `1/pi` by the proved
Wallis product limit. Consumer: the paper's even/odd bounds `U_N`.
This scalar analytic calculation creates no forest or process data.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Filter
open scoped Topology

/-- Source: note Lemma 3.7, `W_m = choose (2m) m * 4^(-m)`. -/
noncomputable def centralMass (m : ℕ) : ℝ :=
  (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m

theorem centralMass_pos (m : ℕ) : 0 < centralMass m := by
  unfold centralMass
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos m) (by positivity)

/-- The central binomial recurrence, with all natural indices retained. -/
theorem centralMass_succ (m : ℕ) :
    centralMass (m + 1) = centralMass m * (2 * (m : ℝ) + 1) / (2 * m + 2) := by
  have hrec : ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ) =
      2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ m
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
  have hpow : (4 : ℝ) ^ m ≠ 0 := by positivity
  have hc : (Nat.centralBinom (m + 1) : ℝ) =
      2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) / ((m : ℝ) + 1) := by
    apply (eq_div_iff hm1).2
    rw [mul_comm]
    exact hrec
  unfold centralMass
  rw [hc, pow_succ]
  field_simp [hm1, hm2, hpow]
  <;> ring

/-- The exact relation between the paper's mass and Mathlib's Wallis product. -/
theorem centralMass_wallis_mul (m : ℕ) :
    (2 * (m : ℝ) + 1) * centralMass m ^ 2 * Real.Wallis.W m = 1 := by
  induction m with
  | zero => norm_num [centralMass, Real.Wallis.W]
  | succ m ih =>
    have hm1 : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    have hm2 : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
    have hm3 : 2 * (m : ℝ) + 3 ≠ 0 := by positivity
    calc
      (2 * ((m + 1 : ℕ) : ℝ) + 1) * centralMass (m + 1) ^ 2 *
          Real.Wallis.W (m + 1) =
          (2 * (m : ℝ) + 1) * centralMass m ^ 2 * Real.Wallis.W m := by
        rw [centralMass_succ, Real.Wallis.W_succ]
        simp only [Nat.cast_add, Nat.cast_one]
        field_simp [hm1, hm2, hm3]
        <;> ring
      _ = 1 := ih

/-- Source: note Lemma 3.7, the auxiliary increasing sequence `x_m`. -/
noncomputable def centralMassSqShift (m : ℕ) : ℝ :=
  centralMass m ^ 2 * ((m : ℝ) + 1 / 4)

theorem centralMassSqShift_eq_wallis (m : ℕ) :
    centralMassSqShift m =
      (((m : ℝ) + 1 / 4) / (2 * m + 1)) / Real.Wallis.W m := by
  have hw : Real.Wallis.W m ≠ 0 := (Real.Wallis.W_pos m).ne'
  have hm : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  have hc : centralMass m ^ 2 = 1 / ((2 * (m : ℝ) + 1) * Real.Wallis.W m) := by
    apply (eq_div_iff (mul_ne_zero hm hw)).2
    nlinarith [centralMass_wallis_mul m]
  unfold centralMassSqShift
  rw [hc]
  field_simp [hm, hw]
  <;> ring

/-- Exact successor difference; it is positive, including at `m = 0`. -/
theorem centralMassSqShift_succ_sub (m : ℕ) :
    centralMassSqShift (m + 1) - centralMassSqShift m =
      centralMass m ^ 2 / (16 * ((m : ℝ) + 1) ^ 2) := by
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
  unfold centralMassSqShift
  rw [centralMass_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hm1, hm2]
  <;> ring

theorem centralMassSqShift_monotone : Monotone centralMassSqShift := by
  apply monotone_nat_of_le_succ
  intro m
  have h : 0 ≤ centralMass m ^ 2 / (16 * ((m : ℝ) + 1) ^ 2) := by positivity
  rw [← centralMassSqShift_succ_sub m] at h
  linarith

/-- Wallis' product gives the exact limiting constant `1/pi`. -/
theorem centralMassSqShift_tendsto :
    Tendsto centralMassSqShift atTop (𝓝 (1 / Real.pi)) := by
  have hcast : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun m : ℕ => 4 * (2 * (m : ℝ) + 1)) atTop atTop :=
    ((hcast.const_mul_atTop (by norm_num)).atTop_add tendsto_const_nhds).const_mul_atTop
      (by norm_num)
  have hsmall : Tendsto (fun m : ℕ => 1 / (4 * (2 * (m : ℝ) + 1))) atTop (𝓝 0) :=
    hden.const_div_atTop 1
  have hfactor : Tendsto (fun m : ℕ => ((m : ℝ) + 1 / 4) / (2 * m + 1))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := hsmall.const_sub (1 / 2 : ℝ)
    simp only [sub_zero] at h
    convert h using 1
    funext m
    have hm : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hm]
    <;> ring
  have h := hfactor.div Real.Wallis.tendsto_W_nhds_pi_div_two
    (div_ne_zero Real.pi_ne_zero (by norm_num))
  convert h using 1
  · funext m
    exact centralMassSqShift_eq_wallis m
  · field_simp

/-- Source: note Lemma 3.7, `x_m ≤ 1/pi`. -/
theorem centralMassSqShift_le (m : ℕ) : centralMassSqShift m ≤ 1 / Real.pi :=
  centralMassSqShift_monotone.ge_of_tendsto centralMassSqShift_tendsto m

/-- The paper's upper bound, expressed with an inverse square root. -/
theorem centralMass_upper_sqrt (m : ℕ) :
    centralMass m ≤ (Real.sqrt (Real.pi * ((m : ℝ) + 1 / 4)))⁻¹ := by
  have ht : 0 < (m : ℝ) + 1 / 4 := by positivity
  have hs : 0 < Real.sqrt (Real.pi * ((m : ℝ) + 1 / 4)) := by positivity
  have hsq : (centralMass m * Real.sqrt (Real.pi * ((m : ℝ) + 1 / 4))) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc
      centralMass m ^ 2 * (Real.pi * ((m : ℝ) + 1 / 4)) =
          Real.pi * centralMassSqShift m := by unfold centralMassSqShift; ring
      _ ≤ Real.pi * (1 / Real.pi) :=
        mul_le_mul_of_nonneg_left (centralMassSqShift_le m) Real.pi_pos.le
      _ = 1 := by field_simp
  have hmul : centralMass m * Real.sqrt (Real.pi * ((m : ℝ) + 1 / 4)) ≤ 1 :=
    le_of_sq_le_sq (by simpa only [one_pow] using hsq) (by norm_num)
  simpa only [one_div] using (le_div_iff₀ hs).2 hmul

/-- Source: note Lemma 3.7, the exact upper bound for every `m ≥ 1`. -/
theorem centralMass_upper {m : ℕ} (_hm : 1 ≤ m) :
    centralMass m ≤ (Real.pi * ((m : ℝ) + 1 / 4)) ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  exact centralMass_upper_sqrt m

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.centralMass
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_pos
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_succ
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_succ
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_wallis_mul
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_wallis_mul
#check Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift
#check Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_eq_wallis
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_eq_wallis
#check Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_succ_sub
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_succ_sub
#check Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_monotone
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_monotone
#check Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_tendsto
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_tendsto
#check Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_le
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMassSqShift_le
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_upper_sqrt
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_upper_sqrt
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_upper
