module

public import Erdos993Lean.Analytic.V22.Analysis.InteriorKL
public import Erdos993Lean.Analytic.V22.Analysis.WallisLower
public import Erdos993Lean.Analytic.V22.Analysis.Amplitudes

/-!
# Version 2.2 of the manuscript, Lemma 4.4: the exact central amplitude lower bound

Source: the frozen version 5 of the note,
SHA256 `c08dbf5837e1fce232f4871dffbade9fa8197bd01e9d8c77fbd8c921e35e4415`.
The final statement covers every natural N>=2 and the
shared source `V22.centralAmplitude`, without a finite-check assumption.
Consumer: the lower three-range minorant and window amplitudes.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real

/-- Exact identification of the shared source's central binomial atom. -/
theorem shared_wallisW_eq (m : ℕ) :
    Erdos993Lean.Analytic.V22.wallisW m = centralMass m := by
  rfl

/-- Shared definitions retain exactly the local lower prefactor, including
the odd-row entropy correction. -/
theorem shared_centralAmplitude_eq (N : ℕ) :
    Erdos993Lean.Analytic.V22.centralAmplitude N = interiorCentralPrefactor N := by
  unfold Erdos993Lean.Analytic.V22.centralAmplitude interiorCentralPrefactor
  split_ifs
  · exact shared_wallisW_eq _
  · rw [shared_wallisW_eq]
    rfl

theorem shared_centralAmplitude_pos (N : ℕ) :
    0 < Erdos993Lean.Analytic.V22.centralAmplitude N := by
  rw [shared_centralAmplitude_eq]
  exact interiorCentralPrefactor_pos N

/-- Source Lemma 4.4, the exact even-row rational comparison. -/
theorem shared_quarticErrorZero_le_even {N : ℝ} (hN : 2 ≤ N) :
    Erdos993Lean.Analytic.V22.quarticErrorZero N ≤ 1 / (12 * (N - 1)) := by
  have hN0 : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  unfold Erdos993Lean.Analytic.V22.quarticErrorZero
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [sq_nonneg N]

/-- Source Lemma 4.4, the exact odd-row rational comparison. -/
theorem shared_quarticErrorZero_le_odd {N : ℝ} (hN : 2 ≤ N) :
    Erdos993Lean.Analytic.V22.quarticErrorZero N ≤ 1 / (12 * (N + 1)) := by
  have hN0 : 0 < N := by linarith
  unfold Erdos993Lean.Analytic.V22.quarticErrorZero
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [sq_nonneg N]

private theorem centralAmplitude_even_gain {m : ℕ} (hm : 1 ≤ m) :
    symmetricLowerPrefactor (2 * m) *
      Real.exp (1 / (12 * (((2 * m : ℕ) : ℝ) - 1))) =
      Real.exp (1 / (24 * (m : ℝ) + 1) - 1 / (6 * (m : ℝ))) *
        (Real.pi * (m : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmge : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hNm1 : 0 < ((2 * m : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hhalf : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
  unfold symmetricLowerPrefactor
  rw [if_pos (by omega : (2 * m) % 2 = 0), hhalf]
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_exp, Real.log_rpow]
  push_cast
  field_simp [hm0.ne', hNm1.ne']
  ring

private theorem centralAmplitude_odd_gain (m : ℕ) :
    symmetricLowerPrefactor (2 * m + 1) *
      Real.exp (1 / (12 * (((2 * m + 1 : ℕ) : ℝ) + 1))) =
      (Real.exp (1 / (24 * ((m + 1 : ℕ) : ℝ) + 1) - 1 / (6 * ((m + 1 : ℕ) : ℝ))) *
        (Real.pi * ((m + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (1 / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) := by
  have hm0 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hhalf : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = ((m + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  unfold symmetricLowerPrefactor
  rw [if_neg (by omega : (2 * m + 1) % 2 ≠ 0), hhalf]
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_exp, Real.log_rpow]
  push_cast
  field_simp
  ring

/-- Lemma 4.4 in the shared source definitions: every natural N>=2, exactly
c_N>=L_N*exp(E4^(0)), with no extra analytic or certificate assumption. -/
theorem shared_centralAmplitude_lower {N : ℕ} (hN : 2 ≤ N) :
    symmetricLowerPrefactor N *
      Real.exp (Erdos993Lean.Analytic.V22.quarticErrorZero (N : ℝ)) ≤
      Erdos993Lean.Analytic.V22.centralAmplitude N := by
  rw [shared_centralAmplitude_eq]
  by_cases heven : N % 2 = 0
  · obtain ⟨m, hform⟩ : ∃ m : ℕ, N = 2 * m := ⟨N / 2, by omega⟩
    subst N
    have hm : 1 ≤ m := by omega
    have hNr : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hN
    have he := shared_quarticErrorZero_le_even hNr
    have hL := (symmetricLowerPrefactor_pos hN).le
    calc
      symmetricLowerPrefactor (2 * m) *
          Real.exp (Erdos993Lean.Analytic.V22.quarticErrorZero ((2 * m : ℕ) : ℝ)) ≤
          symmetricLowerPrefactor (2 * m) *
            Real.exp (1 / (12 * (((2 * m : ℕ) : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hL
      _ = Real.exp (1 / (24 * (m : ℝ) + 1) - 1 / (6 * (m : ℝ))) *
          (Real.pi * (m : ℝ)) ^ (-(1 / 2 : ℝ)) := centralAmplitude_even_gain hm
      _ ≤ centralMass m := centralMass_lower hm
      _ = interiorCentralPrefactor (2 * m) := (interiorCentralPrefactor_even m).symm
  · obtain ⟨m, hform⟩ : ∃ m : ℕ, N = 2 * m + 1 := ⟨N / 2, by omega⟩
    subst N
    have hNr : (2 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast hN
    have hden : 0 < ((2 * m + 1 : ℕ) : ℝ) + 1 := by positivity
    have hx0 : 0 ≤ 1 / (((2 * m + 1 : ℕ) : ℝ) + 1) := by positivity
    have hx1 : 1 / (((2 * m + 1 : ℕ) : ℝ) + 1) < 1 := by
      apply (div_lt_one hden).2
      linarith
    have hi := mul_le_mul_of_nonneg_left (sharedKLI_quadratic_lower hx0 hx1) hden.le
    have hgain : (((2 * m + 1 : ℕ) : ℝ) + 1) *
        ((1 / (((2 * m + 1 : ℕ) : ℝ) + 1)) ^ 2 / 2) =
        1 / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
      field_simp [hden.ne'] <;> ring
    rw [hgain] at hi
    have he := shared_quarticErrorZero_le_odd hNr
    have hL := (symmetricLowerPrefactor_pos hN).le
    have hW := centralMass_lower (m := m + 1) (by omega)
    have hW0 : 0 ≤ Real.exp (1 / (24 * ((m + 1 : ℕ) : ℝ) + 1) -
        1 / (6 * ((m + 1 : ℕ) : ℝ))) *
        (Real.pi * ((m + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) := by positivity
    calc
      symmetricLowerPrefactor (2 * m + 1) *
          Real.exp (Erdos993Lean.Analytic.V22.quarticErrorZero ((2 * m + 1 : ℕ) : ℝ)) ≤
          symmetricLowerPrefactor (2 * m + 1) *
            Real.exp (1 / (12 * (((2 * m + 1 : ℕ) : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hL
      _ = (Real.exp (1 / (24 * ((m + 1 : ℕ) : ℝ) + 1) -
            1 / (6 * ((m + 1 : ℕ) : ℝ))) *
          (Real.pi * ((m + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
          Real.exp (1 / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) := centralAmplitude_odd_gain m
      _ ≤ (Real.exp (1 / (24 * ((m + 1 : ℕ) : ℝ) + 1) -
            1 / (6 * ((m + 1 : ℕ) : ℝ))) *
          (Real.pi * ((m + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
          Real.exp ((((2 * m + 1 : ℕ) : ℝ) + 1) *
            sharedKLI (1 / (((2 * m + 1 : ℕ) : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi) hW0
      _ ≤ centralMass (m + 1) *
          Real.exp ((((2 * m + 1 : ℕ) : ℝ) + 1) *
            sharedKLI (1 / (((2 * m + 1 : ℕ) : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hW (Real.exp_pos _).le
      _ = interiorCentralPrefactor (2 * m + 1) := (interiorCentralPrefactor_odd m).symm

/-- The same source bound in the local c_N definition consumed by minorants. -/
theorem interiorCentralPrefactor_lower {N : ℕ} (hN : 2 ≤ N) :
    symmetricLowerPrefactor N *
      Real.exp (Erdos993Lean.Analytic.V22.quarticErrorZero (N : ℝ)) ≤
      interiorCentralPrefactor N := by
  rw [← shared_centralAmplitude_eq]
  exact shared_centralAmplitude_lower hN

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.shared_wallisW_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_wallisW_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_centralAmplitude_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_centralAmplitude_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_centralAmplitude_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_centralAmplitude_pos
#check Erdos993Lean.Analytic.V22.Analysis.shared_quarticErrorZero_le_even
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_quarticErrorZero_le_even
#check Erdos993Lean.Analytic.V22.Analysis.shared_quarticErrorZero_le_odd
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_quarticErrorZero_le_odd
#check Erdos993Lean.Analytic.V22.Analysis.centralAmplitude_even_gain
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralAmplitude_even_gain
#check Erdos993Lean.Analytic.V22.Analysis.centralAmplitude_odd_gain
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralAmplitude_odd_gain
#check Erdos993Lean.Analytic.V22.Analysis.shared_centralAmplitude_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_centralAmplitude_lower
#check Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor_lower
