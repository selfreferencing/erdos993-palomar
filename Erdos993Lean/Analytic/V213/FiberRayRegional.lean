module

public import Erdos993Lean.Analytic.V213.FiberRayDerivatives

/-!
The actual uniform Eq93 extension region R<=7/20,N>=10.
The printed d0<=1/5 and rho-star>=1/2 follow from explicit real
square-root and denominator comparisons. No finite record or endpoint
certificate is assumed. The original capped beta join is handled later.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_ray_regional_rho {N R : ℝ} (hN : 10 ≤ N)
    (hR : 0 ≤ R) (hRh : R ≤ 7 / 20) : (1 / 2 : ℝ) ≤ rhoStar N R := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrsq : R ^ 2 ≤ (49 / 400 : ℝ) := by nlinarith
  have ho : (351 / 400 : ℝ) ≤ 1 - R ^ 2 := by linarith
  have hs := linearized_sqrt_cCoef_lower hN
  have hs0 : 0 < Real.sqrt (cCoef N) := by linarith
  have hrho : (10 / 11 : ℝ) ≤ rho N := by
    unfold rho
    apply (le_div_iff₀ hn1).2
    linarith
  have hmain : (351 / 440 : ℝ) ≤ (1 - R ^ 2) * rho N := by
    have h := mul_le_mul ho hrho (by norm_num : (0 : ℝ) ≤ 10 / 11)
      (by linarith : 0 ≤ 1 - R ^ 2)
    norm_num at h
    exact h
  have hd1 : (99 / 10 : ℝ) ≤ (N + 1) * Real.sqrt (cCoef N) := by
    have h := mul_le_mul (show (11 : ℝ) ≤ N + 1 by linarith) hs
      (by norm_num : (0 : ℝ) ≤ 9 / 10) hn1.le
    norm_num at h
    exact h
  have ht1 : 2 / ((N + 1) * Real.sqrt (cCoef N)) ≤ (20 / 99 : ℝ) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 99 / 10) hd1
    norm_num at h
    exact h
  have hd2 : (9477 / 4000 : ℝ) ≤ 3 * (1 - R ^ 2) * Real.sqrt (cCoef N) := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left ho (by norm_num : (0 : ℝ) ≤ 3)) hs
      (by norm_num : (0 : ℝ) ≤ 9 / 10) (by linarith : 0 ≤ 3 * (1 - R ^ 2))
    norm_num at h
    exact h
  have ht2 : R ^ 2 / (3 * (1 - R ^ 2) * Real.sqrt (cCoef N)) ≤ (490 / 9477 : ℝ) := by
    calc
      _ ≤ (49 / 400 : ℝ) / (3 * (1 - R ^ 2) * Real.sqrt (cCoef N)) :=
        div_le_div_of_nonneg_right hrsq (by positivity)
      _ ≤ (49 / 400 : ℝ) / (9477 / 4000) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd2
      _ = _ := by norm_num
  unfold rhoStar
  linarith

theorem fiber_ray_regional_d0 {N R : ℝ} (hN : 10 ≤ N)
    (hR : 0 ≤ R) (hRh : R ≤ 7 / 20) : fiberRayD0 R N ≤ (1 / 5 : ℝ) := by
  have hrsq : R ^ 2 ≤ (49 / 400 : ℝ) := by nlinarith
  have ho : (351 / 400 : ℝ) ≤ 1 - R ^ 2 := by linarith
  have hop : 0 < 1 - R ^ 2 := by linarith
  have hs : (3 : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsp : 0 < Real.sqrt N := by linarith
  have hd1 : (3159 / 100 : ℝ) ≤ 12 * (1 - R ^ 2) * Real.sqrt N := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left ho (by norm_num : (0 : ℝ) ≤ 12)) hs
      (by norm_num : (0 : ℝ) ≤ 3) (by positivity : 0 ≤ 12 * (1 - R ^ 2))
    norm_num at h
    exact h
  have ht1 : 5 * R / (12 * (1 - R ^ 2) * Real.sqrt N) ≤ (175 / 3159 : ℝ) := by
    calc
      _ ≤ (7 / 4 : ℝ) / (12 * (1 - R ^ 2) * Real.sqrt N) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (7 / 4 : ℝ) / (3159 / 100) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd1
      _ = _ := by norm_num
  have hosq : (123201 / 160000 : ℝ) ≤ (1 - R ^ 2) ^ 2 := by
    have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 351 / 400) hop.le).2 ho
    norm_num at h
    exact h
  have hd2 : (369603 / 80000 : ℝ) ≤ 6 * (1 - R ^ 2) ^ 2 := by linarith
  have ht2 : 5 * R ^ 2 / (6 * (1 - R ^ 2) ^ 2) ≤ (49000 / 369603 : ℝ) := by
    calc
      _ ≤ (49 / 80 : ℝ) / (6 * (1 - R ^ 2) ^ 2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (49 / 80 : ℝ) / (369603 / 80000) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd2
      _ = _ := by norm_num
  unfold fiberRayD0
  linarith

theorem fiber_ray_pre_derivative_d0 {R N N0 : ℝ}
    (hR : 0 < R) (hRh : R ≤ 1 / 2) (hN0 : 0 < N0) (hN : N0 ≤ N)
    (hcap : N ≤ (6 / R) ^ 2) :
    fiberRayCalc_preCapE2Derivative R N ≤ fiberRayD0 R N0 := by
  have ho := fiberRayCalc_activity_denominator_pos hR.le hRh
  have he3 : 0 ≤ e3 R := by unfold e3; positivity
  have he5 : 0 ≤ e5 R := by unfold e5; positivity
  have hNu : R * Real.sqrt N ≤ 6 := by
    have h := Real.sqrt_le_iff.mpr ⟨(by positivity : 0 ≤ 6 / R),hcap⟩
    simpa only [mul_comm] using (le_div_iff₀ hR).mp h
  have hs0 : 0 < Real.sqrt N0 := Real.sqrt_pos.mpr hN0
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (hN0.trans_le hN)
  have hd1 := div_le_div_of_nonneg_left (by positivity : 0 ≤ e3 R * R)
    (mul_pos (by norm_num : (0 : ℝ) < 2) hs0)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hN) (by norm_num : (0 : ℝ) ≤ 2))
  have hd3 : (3 / 2 : ℝ) * e5 R * R ^ 3 * Real.sqrt N ≤ 9 * e5 R * R ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hNu (by positivity : 0 ≤ (3 / 2 : ℝ) * e5 R * R ^ 2)
    convert h using 1 <;> ring
  unfold fiberRayCalc_preCapE2Derivative fiberRayD0
  have hid : e3 R * R / (2 * Real.sqrt N0) + e5 R * R ^ 2 + 9 * e5 R * R ^ 2 =
      5 * R / (12 * (1 - R ^ 2) * Real.sqrt N0) + 5 * R ^ 2 / (6 * (1 - R ^ 2) ^ 2) := by
    unfold e3 e5
    field_simp
    ring
  rw [← hid]
  linarith only [hd1,hd3]

end Erdos993Lean.Analytic.V213
