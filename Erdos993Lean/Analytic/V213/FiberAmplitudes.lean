module

public import Erdos993Lean.Analytic.V213.FiberEntropy
public import Erdos993Lean.Analytic.V22.Analysis.CentralAmplitude
public import Erdos993Lean.Analytic.V22.Analysis.AmplitudeShift

/-!
Actual upper and central binomial amplitudes
(`r12:eq68`--`r12:eq70`). The old lower prefactor is used through
a proved comparison to the actual central prefactor, never as its definition.
No generated finite family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberUpperPrefactor (N : ℕ) : ℝ := symmetricUpperPrefactor N

noncomputable def fiberCentralPrefactor (N : ℕ) : ℝ :=
  Erdos993Lean.Analytic.V22.centralAmplitude N

noncomputable def fiberAmplitude (N : ℕ) (X : ℝ) : ℝ := shapeAmplitude N X

noncomputable def fiberTemplateOmega (mu : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  shapeTemplateLambda mu N X

theorem fiber_central_prefactor_formula (N : ℕ) :
    fiberCentralPrefactor N =
      if N % 2 = 0 then centralMass (N / 2)
      else centralMass ((N + 1) / 2) *
        Real.exp (((N : ℝ) + 1) * sharedKLI (1 / ((N : ℝ) + 1))) := by
  exact shared_centralAmplitude_eq N

theorem fiber_central_prefactor_pos (N : ℕ) : 0 < fiberCentralPrefactor N :=
  shared_centralAmplitude_pos N

theorem fiber_amplitude_mono {N : ℝ} (hN : 1 < N) {X Y : ℝ} (hXY : X ≤ Y) :
    shapeAmplitude N X ≤ shapeAmplitude N Y := by
  unfold shapeAmplitude
  exact (div_le_div_iff_of_pos_right (by linarith : 0 < N - 1)).2
    (mul_le_mul_of_nonneg_left hXY (by positivity))

theorem fiber_actual_central_dominates_lower {N : ℕ} (hN : 2 ≤ N) :
    symmetricLowerPrefactor N ≤ fiberCentralPrefactor N := by
  have he : 0 ≤ Erdos993Lean.Analytic.V22.quarticErrorZero (N : ℝ) := by
    unfold Erdos993Lean.Analytic.V22.quarticErrorZero
    positivity
  have hx : 1 ≤ Real.exp (Erdos993Lean.Analytic.V22.quarticErrorZero (N : ℝ)) :=
    Real.one_le_exp_iff.mpr he
  calc
    symmetricLowerPrefactor N = symmetricLowerPrefactor N * 1 := (mul_one _).symm
    _ ≤ symmetricLowerPrefactor N *
        Real.exp (Erdos993Lean.Analytic.V22.quarticErrorZero (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hx (symmetricLowerPrefactor_pos hN).le
    _ ≤ fiberCentralPrefactor N := shared_centralAmplitude_lower hN

theorem fiber_central_log_amplitude_lower {N : ℕ} (hN : 10 ≤ N) :
    (13 / 20 : ℝ) / (N : ℝ) ≤ Real.log (fiberAmplitude N (fiberCentralPrefactor N)) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hm := fiber_amplitude_mono hNr (fiber_actual_central_dominates_lower hN2)
  exact (amplitude_log_bounds hN).2.1.trans
    (Real.log_le_log (lowerAmplitude_pos hN2) hm)

theorem fiber_upper_log_amplitude_bounds {N : ℕ} (hN : 10 ≤ N) :
    (13 / 20 : ℝ) / (N : ℝ) ≤ Real.log (fiberAmplitude N (fiberUpperPrefactor N)) ∧
      Real.log (fiberAmplitude N (fiberUpperPrefactor N)) ≤
        3 / (4 * (N : ℝ)) + (11 / 10 : ℝ) / (N : ℝ) ^ 2 :=
  (amplitude_log_bounds hN).1

theorem fiber_central_mass_basic_upper {k : ℕ} (hk : 1 ≤ k) :
    centralMass k ≤ (Real.pi * (k : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  exact (centralMass_upper hk).trans
    (Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith [Real.pi_pos] : Real.pi * (k : ℝ) ≤ Real.pi * ((k : ℝ) + 1 / 4))
      (by norm_num))

theorem fiber_central_prefactor_upper {N : ℕ} (hN : 2 ≤ N) :
    fiberCentralPrefactor N ≤
      (Real.pi * (N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (2 * (N : ℝ))) := by
  rw [fiber_central_prefactor_formula]
  by_cases he : N % 2 = 0
  · rw [if_pos he]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = 2 * k := ⟨N / 2, by omega⟩
    have hk : 1 ≤ k := by omega
    rw [show (2 * k) / 2 = k by omega]
    have hb : Real.pi * ((2 * k : ℕ) : ℝ) / 2 = Real.pi * (k : ℝ) := by
      push_cast
      ring
    rw [hb]
    exact (fiber_central_mass_basic_upper hk).trans
      (le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr (by positivity)))
  · rw [if_neg he]
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hk : 1 ≤ (N + 1) / 2 := by omega
    have hkcast : (((N + 1) / 2 : ℕ) : ℝ) = ((N : ℝ) + 1) / 2 := by
      have hhalf : 2 * ((N + 1) / 2) = N + 1 := by omega
      have h := congrArg (fun x : ℕ => (x : ℝ)) hhalf
      push_cast at h
      linarith
    have hw := fiber_central_mass_basic_upper hk
    rw [hkcast] at hw
    have hw' : centralMass ((N + 1) / 2) ≤ (Real.pi * (N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) :=
      hw.trans (Real.rpow_le_rpow_of_nonpos (by positivity)
        (by nlinarith [Real.pi_pos] : Real.pi * (N : ℝ) / 2 ≤
          Real.pi * (((N : ℝ) + 1) / 2)) (by norm_num))
    exact mul_le_mul hw' (Real.exp_le_exp.mpr (fiber_odd_entropy_correction hNr))
      (Real.exp_nonneg _) (by positivity)

theorem fiber_central_log_amplitude_upper {N : ℕ} (hN : 2 ≤ N) :
    Real.log (fiberAmplitude N (fiberCentralPrefactor N)) ≤
      -Real.log (1 - 1 / (N : ℝ)) + 1 / (2 * (N : ℝ)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hp := shapeAmplitude_pos hNr (fiber_central_prefactor_pos N)
  have hm := fiber_amplitude_mono hNr (fiber_central_prefactor_upper hN)
  have hmodel := shapeAmplitude_log_model (N := (N : ℝ)) (d := 0)
    (c := 1 / (2 * (N : ℝ))) hNr (by norm_num)
  have hb : (Real.pi / 2) * (N : ℝ) * (1 + (0 : ℝ)) = Real.pi * (N : ℝ) / 2 := by ring
  rw [hb] at hmodel
  simp only [zero_add, add_zero, Real.log_one, mul_zero, sub_zero] at hmodel
  have he : (Real.pi * (N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (2 * (N : ℝ))) =
      Real.exp (1 / (2 * (N : ℝ))) * (Real.pi * (N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := mul_comm _ _
  rw [he] at hm
  exact (Real.log_le_log hp hm).trans_eq hmodel

theorem fiber_template_omega_formula {mu : ℝ} (hmu : 0 < mu)
    {N : ℕ} (hN : 2 ≤ N) {X : ℝ} (hX : 0 < X) :
    fiberTemplateOmega mu N X = (5 / 2 : ℝ) * Real.log ((N : ℝ) / mu) -
      1 / (2 * ((N : ℝ) + 1)) - Real.log (fiberAmplitude N X) :=
  shapeTemplateLambda_eq hmu (by exact_mod_cast (by omega : 1 < N)) hX

theorem fiber_template_omega_shift {mu : ℝ} (hmu : 0 < mu)
    {M : ℕ} (hM : 0 < M) {X : ℝ} (hX : 0 < X) :
    fiberTemplateOmega mu (M + 2) X = (5 / 2 : ℝ) * Real.log ((M : ℝ) / mu) +
      logShiftKValue (M : ℝ) (Real.log (fiberAmplitude (M + 2) X)) / ((M : ℝ) + 3) := by
  simpa only [fiberTemplateOmega, fiberAmplitude, Nat.cast_add, Nat.cast_ofNat] using
    shapeTemplateLambda_shift hmu (by exact_mod_cast hM : (0 : ℝ) < M) hX

theorem fiber_upper_shift_bounds {M : ℕ} (hM : 8 ≤ M) :
    (71 / 20 : ℝ) ≤ logShiftKValue (M : ℝ)
        (Real.log (fiberAmplitude (M + 2) (fiberUpperPrefactor (M + 2)))) ∧
      logShiftKValue (M : ℝ)
        (Real.log (fiberAmplitude (M + 2) (fiberUpperPrefactor (M + 2)))) ≤
        (77 / 20 : ℝ) + 10 / (M : ℝ) := by
  have ha := fiber_upper_log_amplitude_bounds (by omega : 10 ≤ M + 2)
  push_cast at ha
  exact logShiftK_bounds (by exact_mod_cast hM) ha.1 ha.2

theorem fiber_central_log_amplitude_small_upper {N : ℕ} (hN : 10 ≤ N) :
    Real.log (fiberAmplitude N (fiberCentralPrefactor N)) ≤ 2 / (N : ℝ) := by
  have hn : (10 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hi0, hi⟩ := logShift_inv_small hn
  have hu := logShift_neg_log_one_sub_small_upper hi0.le hi
  have hb := fiber_central_log_amplitude_upper (by omega : 2 ≤ N)
  have hsq : (1 / (N : ℝ)) ^ 2 ≤ (1 / 10 : ℝ) * (1 / (N : ℝ)) :=
    by nlinarith
  have hr : 1 / (2 * (N : ℝ)) = (1 / 2 : ℝ) * (1 / (N : ℝ)) := by ring
  rw [hr] at hb
  have ht : 2 / (N : ℝ) = 2 * (1 / (N : ℝ)) := by ring
  rw [ht]
  nlinarith

theorem fiber_central_k_bounds {M : ℕ} (hM : 8 ≤ M) :
    0 ≤ logShiftKValue (M : ℝ)
        (Real.log (fiberAmplitude (M + 2) (fiberCentralPrefactor (M + 2)))) ∧
      logShiftKValue (M : ℝ)
        (Real.log (fiberAmplitude (M + 2) (fiberCentralPrefactor (M + 2)))) ≤
        (77 / 20 : ℝ) + 10 / (M : ℝ) := by
  have hm : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : 0 < (M : ℝ) := by linarith
  have hn0 : 0 < (M : ℝ) + 2 := by linarith
  have hm3 : 0 < (M : ℝ) + 3 := by linarith
  let A := Real.log (fiberAmplitude (M + 2) (fiberCentralPrefactor (M + 2)))
  have hAl : (13 / 20 : ℝ) / ((M : ℝ) + 2) ≤ A := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      fiber_central_log_amplitude_lower (by omega : 10 ≤ M + 2)
  have hAu : A ≤ 2 / ((M : ℝ) + 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      fiber_central_log_amplitude_small_upper (by omega : 10 ≤ M + 2)
  have hscaleL : (13 / 20 : ℝ) ≤ ((M : ℝ) + 3) * A := by
    have h := mul_le_mul_of_nonneg_left hAl hm3.le
    have hb : (13 / 20 : ℝ) ≤ ((M : ℝ) + 3) * ((13 / 20 : ℝ) / ((M : ℝ) + 2)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hn0).2
      linarith
    exact hb.trans (by simpa only [mul_div_assoc] using h)
  have hscaleU : ((M : ℝ) + 3) * A ≤ (11 / 5 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hAu hm3.le
    have hb : ((M : ℝ) + 3) * (2 / ((M : ℝ) + 2)) ≤ (11 / 5 : ℝ) := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hn0).2
      linarith
    exact h.trans hb
  have hw := logShift_weighted_log_bounds hm
  have hcor : 0 ≤ 10 / (M : ℝ) - 15 / (M : ℝ) ^ 2 := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0 < (M : ℝ) ^ 2) hm0).2
    nlinarith
  have heq : logShiftKValue (M : ℝ) A =
      (5 / 2 : ℝ) * ((M : ℝ) + 3) * Real.log (1 + 2 / (M : ℝ)) -
        1 / 2 - ((M : ℝ) + 3) * A := by
    unfold logShiftKValue
    field_simp [hm3.ne']
  change 0 ≤ logShiftKValue (M : ℝ) A ∧ _
  rw [heq]
  constructor <;> linarith [hw.1, hw.2]

theorem fiber_central_shift_bounds {mu : ℝ} (hmu : 0 < mu)
    {M : ℕ} (hM : 8 ≤ M) :
    0 ≤ fiberTemplateOmega mu (M + 2) (fiberCentralPrefactor (M + 2)) -
        (5 / 2 : ℝ) * Real.log ((M : ℝ) / mu) ∧
      fiberTemplateOmega mu (M + 2) (fiberCentralPrefactor (M + 2)) -
          (5 / 2 : ℝ) * Real.log ((M : ℝ) / mu) ≤
        ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) := by
  rw [fiber_template_omega_shift hmu (by omega : 0 < M)
    (fiber_central_prefactor_pos (M + 2)), add_sub_cancel_left]
  have h := fiber_central_k_bounds hM
  constructor
  · exact div_nonneg h.1 (by positivity)
  · exact div_le_div_of_nonneg_right h.2 (by positivity)

noncomputable def fiberUpperK (M : ℕ) : ℝ :=
  logShiftKValue (M : ℝ)
    (Real.log (fiberAmplitude (M + 2) (fiberUpperPrefactor (M + 2))))

/-- Literal Lemma 6.8, with the paper's `M = N - 2` and `t = M / mu`. -/
theorem fiber_direct_amplitude_bounds {N : ℕ} (hN : 10 ≤ N)
    {mu : ℝ} (hmu : 0 < mu) :
    ((13 / 20 : ℝ) / (N : ℝ) ≤
      Real.log (fiberAmplitude N (fiberUpperPrefactor N)) ∧
      Real.log (fiberAmplitude N (fiberUpperPrefactor N)) ≤
        3 / (4 * (N : ℝ)) + (11 / 10 : ℝ) / (N : ℝ) ^ 2) ∧
    fiberTemplateOmega mu N (fiberUpperPrefactor N) =
      (5 / 2 : ℝ) * Real.log (((N - 2 : ℕ) : ℝ) / mu) +
        fiberUpperK (N - 2) / ((N : ℝ) + 1) ∧
    ((71 / 20 : ℝ) ≤ fiberUpperK (N - 2) ∧
      fiberUpperK (N - 2) ≤ (77 / 20 : ℝ) + 10 / ((N - 2 : ℕ) : ℝ)) ∧
    (0 ≤ fiberTemplateOmega mu N (fiberCentralPrefactor N) -
        (5 / 2 : ℝ) * Real.log (((N - 2 : ℕ) : ℝ) / mu) ∧
      fiberTemplateOmega mu N (fiberCentralPrefactor N) -
          (5 / 2 : ℝ) * Real.log (((N - 2 : ℕ) : ℝ) / mu) ≤
        ((77 / 20 : ℝ) + 10 / ((N : ℝ) - 2)) / ((N : ℝ) + 1)) := by
  have hM : 8 ≤ N - 2 := by omega
  have hNid : N - 2 + 2 = N := by omega
  have hMcast : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ N)]
    norm_num
  have hm3 : ((N - 2 : ℕ) : ℝ) + 3 = (N : ℝ) + 1 := by
    rw [hMcast]
    ring
  refine ⟨fiber_upper_log_amplitude_bounds hN, ?_, ?_, ?_⟩
  · have h := fiber_template_omega_shift hmu (by omega : 0 < N - 2)
      (symmetricUpperPrefactor_pos (N - 2 + 2))
    simpa only [hNid, hm3, fiberUpperK, fiberUpperPrefactor] using h
  · exact fiber_upper_shift_bounds hM
  · have hreal : (N : ℝ) - 2 + 3 = (N : ℝ) + 1 := by ring
    simpa only [hNid, hMcast, hreal] using fiber_central_shift_bounds hmu hM

end Erdos993Lean.Analytic.V213
