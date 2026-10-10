module

public import Erdos993Lean.Analytic.V22.Analysis.SymmetricUpper
public import Erdos993Lean.Analytic.V22.Analysis.LogShiftK
public import Erdos993Lean.Analytic.V22.Analysis.Kernel

/-!
# Version 2.2 of the manuscript: exact amplitudes and log-ratio shifts

Source: note Lemma 3.9(a,b,c) and the displayed definitions of `U_N,L_N`.
The upper prefactor is the same `symmetricUpperPrefactor` as Lemma 3.8.
The lower prefactor below retains the source's exact parity formulas.
Consumer: the activity-one fiber estimate, at the retained binomial index.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

/-- Source: the exact parity formula for `L_N` preceding note Lemma 3.8. -/
noncomputable def symmetricLowerPrefactor (N : ℕ) : ℝ :=
  if N % 2 = 0 then
    Real.exp (1 / (12 * (N : ℝ) + 1) - 1 / (3 * (N : ℝ)) -
      1 / (12 * ((N : ℝ) - 1))) *
      (Real.pi * ((N : ℝ) / 2)) ^ (-(1 / 2 : ℝ))
  else
    Real.exp (1 / (12 * (N : ℝ) + 13) + 1 / (12 * ((N : ℝ) + 1))) *
      (Real.pi * (((N : ℝ) + 1) / 2)) ^ (-(1 / 2 : ℝ))

/-- Source: note Lemma 3.9, `a_X(N)`, retaining `X_N`. -/
noncomputable def shapeAmplitude (N X : ℝ) : ℝ :=
  N ^ (3 / 2 : ℝ) * (Real.pi / 2) ^ (1 / 2 : ℝ) * X / (N - 1)

noncomputable def upperAmplitude (N : ℕ) : ℝ :=
  shapeAmplitude (N : ℝ) (symmetricUpperPrefactor N)

noncomputable def lowerAmplitude (N : ℕ) : ℝ :=
  shapeAmplitude (N : ℝ) (symmetricLowerPrefactor N)

theorem symmetricLowerPrefactor_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < symmetricLowerPrefactor N := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold symmetricLowerPrefactor
  split_ifs <;> positivity

theorem shapeAmplitude_pos {N X : ℝ} (hN : 1 < N) (hX : 0 < X) :
    0 < shapeAmplitude N X := by
  have hNm1 : 0 < N - 1 := by linarith
  unfold shapeAmplitude
  positivity

theorem upperAmplitude_pos {N : ℕ} (hN : 2 ≤ N) : 0 < upperAmplitude N := by
  apply shapeAmplitude_pos _ (symmetricUpperPrefactor_pos N)
  exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hN)

theorem lowerAmplitude_pos {N : ℕ} (hN : 2 ≤ N) : 0 < lowerAmplitude N := by
  apply shapeAmplitude_pos _ (symmetricLowerPrefactor_pos hN)
  exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hN)

/-- The exact logarithm of a modeled parity prefactor. -/
theorem shapeAmplitude_log_model {N d c : ℝ} (hN : 1 < N) (hd : 0 < 1 + d) :
    Real.log (shapeAmplitude N
      (Real.exp c * ((Real.pi / 2) * N * (1 + d)) ^ (-(1 / 2 : ℝ)))) =
        -Real.log (1 - 1 / N) + c - (1 / 2 : ℝ) * Real.log (1 + d) := by
  have hN0 : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  have hx : 0 < 1 - 1 / N := by
    apply sub_pos.mpr
    apply (div_lt_one hN0).2
    exact hN
  have hlogN : Real.log (N - 1) = Real.log N + Real.log (1 - 1 / N) := by
    rw [← Real.log_mul hN0.ne' hx.ne']
    congr 1
    field_simp [hN0.ne']
  unfold shapeAmplitude
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow, Real.log_exp]
  rw [hlogN]
  ring

theorem symmetricUpperPrefactor_even_real {N : ℕ} (he : N % 2 = 0) :
    symmetricUpperPrefactor N =
      (Real.pi * ((N : ℝ) / 2 + 1 / 4)) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = 2 * m := ⟨N / 2, by omega⟩
  rw [symmetricUpperPrefactor_even]
  push_cast
  congr 1
  ring

theorem symmetricUpperPrefactor_odd_real {N : ℕ} (ho : N % 2 ≠ 0) :
    symmetricUpperPrefactor N = Real.exp (1 / (2 * ((N : ℝ) + 1))) *
      (Real.pi * (((N : ℝ) + 1) / 2 + 1 / 4)) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = 2 * m + 1 := ⟨N / 2, by omega⟩
  rw [symmetricUpperPrefactor_odd]
  push_cast
  congr 2 <;> ring

/-- Source: note Lemma 3.9(b), the actual even `a_U` logarithm. -/
theorem upperAmplitude_log_even {N : ℕ} (hN : 2 ≤ N) (he : N % 2 = 0) :
    Real.log (upperAmplitude N) = logShiftUpperEven (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hbase : Real.pi * ((N : ℝ) / 2 + 1 / 4) =
      (Real.pi / 2) * (N : ℝ) * (1 + 1 / (2 * (N : ℝ))) := by
    field_simp [hN0]
    ring
  unfold upperAmplitude
  rw [symmetricUpperPrefactor_even_real he, hbase]
  have h := shapeAmplitude_log_model (N := (N : ℝ)) (d := 1 / (2 * (N : ℝ)))
    (c := 0) hNr (by positivity)
  simpa [logShiftUpperEven] using h

/-- Source: note Lemma 3.9(b), the actual odd `a_U` logarithm. -/
theorem upperAmplitude_log_odd {N : ℕ} (hN : 2 ≤ N) (ho : N % 2 ≠ 0) :
    Real.log (upperAmplitude N) = logShiftUpperOdd (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hbase : Real.pi * (((N : ℝ) + 1) / 2 + 1 / 4) =
      (Real.pi / 2) * (N : ℝ) * (1 + 3 / (2 * (N : ℝ))) := by
    field_simp [hN0]
    ring
  unfold upperAmplitude
  rw [symmetricUpperPrefactor_odd_real ho, hbase]
  simpa [logShiftUpperOdd, sub_eq_add_neg, add_assoc] using
    shapeAmplitude_log_model (N := (N : ℝ)) (d := 3 / (2 * (N : ℝ)))
      (c := 1 / (2 * ((N : ℝ) + 1))) hNr (by positivity)

/-- Source: note Lemma 3.9(b), the actual even `a_L` logarithm. -/
theorem lowerAmplitude_log_even {N : ℕ} (hN : 2 ≤ N) (he : N % 2 = 0) :
    Real.log (lowerAmplitude N) = logShiftLowerEven (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  unfold lowerAmplitude symmetricLowerPrefactor
  rw [if_pos he]
  have hbase : Real.pi * ((N : ℝ) / 2) = (Real.pi / 2) * (N : ℝ) * (1 + 0) := by ring
  rw [hbase]
  have h := shapeAmplitude_log_model (N := (N : ℝ)) (d := 0)
    (c := 1 / (12 * (N : ℝ) + 1) - 1 / (3 * (N : ℝ)) -
      1 / (12 * ((N : ℝ) - 1))) hNr (by norm_num)
  simpa [logShiftLowerEven, sub_eq_add_neg, add_assoc] using h

/-- Source: note Lemma 3.9(b), the actual odd `a_L` logarithm. -/
theorem lowerAmplitude_log_odd {N : ℕ} (hN : 2 ≤ N) (ho : N % 2 ≠ 0) :
    Real.log (lowerAmplitude N) = logShiftLowerOdd (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hbase : Real.pi * (((N : ℝ) + 1) / 2) =
      (Real.pi / 2) * (N : ℝ) * (1 + 1 / (N : ℝ)) := by
    field_simp [hN0]
  unfold lowerAmplitude symmetricLowerPrefactor
  rw [if_neg ho, hbase]
  have h := shapeAmplitude_log_model (N := (N : ℝ)) (d := 1 / (N : ℝ))
    (c := 1 / (12 * (N : ℝ) + 13) + 1 / (12 * ((N : ℝ) + 1))) hNr (by positivity)
  unfold logShiftLowerOdd
  linarith

/-- Source: note Lemma 3.9(b), the actual `a_U,a_L` amplitudes. -/
theorem amplitude_log_bounds {N : ℕ} (hN : 10 ≤ N) :
    ((13 / 20 : ℝ) / (N : ℝ) ≤ Real.log (upperAmplitude N) ∧
      Real.log (upperAmplitude N) ≤ 3 / (4 * (N : ℝ)) + (11 / 10 : ℝ) / (N : ℝ) ^ 2) ∧
    ((13 / 20 : ℝ) / (N : ℝ) ≤ Real.log (lowerAmplitude N) ∧
      Real.log (lowerAmplitude N) ≤ 3 / (4 * (N : ℝ)) + (11 / 10 : ℝ) / (N : ℝ) ^ 2) := by
  have hN2 : 2 ≤ N := by omega
  have hb := logShift_four_formula_bounds (by exact_mod_cast hN : (10 : ℝ) ≤ N)
  by_cases he : N % 2 = 0
  · rw [upperAmplitude_log_even hN2 he, lowerAmplitude_log_even hN2 he]
    exact ⟨hb.1, hb.2.2.1⟩
  · rw [upperAmplitude_log_odd hN2 he, lowerAmplitude_log_odd hN2 he]
    exact ⟨hb.2.1, hb.2.2.2⟩

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.symmetricLowerPrefactor
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetricLowerPrefactor
#check Erdos993Lean.Analytic.V22.Analysis.shapeAmplitude
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeAmplitude
#check Erdos993Lean.Analytic.V22.Analysis.upperAmplitude
#print axioms Erdos993Lean.Analytic.V22.Analysis.upperAmplitude
#check Erdos993Lean.Analytic.V22.Analysis.lowerAmplitude
#print axioms Erdos993Lean.Analytic.V22.Analysis.lowerAmplitude
#check Erdos993Lean.Analytic.V22.Analysis.symmetricLowerPrefactor_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetricLowerPrefactor_pos
#check Erdos993Lean.Analytic.V22.Analysis.shapeAmplitude_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeAmplitude_pos
#check Erdos993Lean.Analytic.V22.Analysis.upperAmplitude_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.upperAmplitude_pos
#check Erdos993Lean.Analytic.V22.Analysis.lowerAmplitude_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.lowerAmplitude_pos
#check Erdos993Lean.Analytic.V22.Analysis.shapeAmplitude_log_model
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeAmplitude_log_model
#check Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_even_real
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_even_real
#check Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_odd_real
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_odd_real
#check Erdos993Lean.Analytic.V22.Analysis.upperAmplitude_log_even
#print axioms Erdos993Lean.Analytic.V22.Analysis.upperAmplitude_log_even
#check Erdos993Lean.Analytic.V22.Analysis.upperAmplitude_log_odd
#print axioms Erdos993Lean.Analytic.V22.Analysis.upperAmplitude_log_odd
#check Erdos993Lean.Analytic.V22.Analysis.lowerAmplitude_log_even
#print axioms Erdos993Lean.Analytic.V22.Analysis.lowerAmplitude_log_even
#check Erdos993Lean.Analytic.V22.Analysis.lowerAmplitude_log_odd
#print axioms Erdos993Lean.Analytic.V22.Analysis.lowerAmplitude_log_odd
#check Erdos993Lean.Analytic.V22.Analysis.amplitude_log_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.amplitude_log_bounds
