module

public import Erdos993Lean.Analytic.V22.Analysis.GaussianUpper
public import Erdos993Lean.Analytic.V213.FiberLowerBranches
public import Erdos993Lean.Analytic.V213.FiberMassLinearization
public import Erdos993Lean.Analytic.V213.FiberUniformConsequences
public import Erdos993Lean.Analytic.V213.FiberRootMinimum

/-!
Literal Eq77: the actual full-integer F is bounded by the upper-offset
minorant with printed U_N, P_U, rho_U and gamma. Original probability q
remains explicit. The constrained Eq67 minimum is consumed only with
proved P_U,B,rho_U positivity. No finite family or paper theorem is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_upper_gamma_identity {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) :
    V22.gamma (fiberSkew q) ((M : ℝ) + 2) = fiberBonus q M := by
  have hv := fiber_variance_pos hq0 hq1
  have ha : 1 - fiberSkew q ^ 2 ≠ 0 := by rw [fiber_variance_skew]; positivity
  have hn : (M : ℝ) + 2 ≠ 0 := by positivity
  unfold V22.gamma V22.Delta fiberBonus
  field_simp [ha, hn]

theorem fiber_upper_standard_offset (q : ℝ) (M : ℕ) (j : ℤ) :
    sharedGaussianU (fiberSkew q) (M + 2) (j + 1) = fiberOffset q M j := by
  unfold sharedGaussianU fiberOffset fiberSkew
  push_cast
  ring

theorem fiber_upper_standard_square {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (M : ℕ) (j : ℤ) :
    (sharedGaussianX (fiberSkew q) (M + 2) (j + 1)) ^ 2 = fiberSquareOffset q M j := by
  have hv : 0 < V22.varianceR (fiberSkew q) * ((M : ℝ) + 2) := by
    unfold V22.varianceR
    rw [fiber_variance_skew]
    have := fiber_variance_pos hq0 hq1
    positivity
  unfold sharedGaussianX V22.sN
  rw [fiber_upper_standard_offset, div_pow]
  push_cast
  rw [Real.sq_sqrt hv.le]
  unfold fiberSquareOffset V22.varianceR
  rw [fiber_variance_skew]
  ring

theorem fiber_binomial_gaussian_upper_actual {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 1)
    (M : ℕ) (j : ℤ) :
    Real.sqrt (1 - fiberSkew q ^ 2) * binom (M + 2) q (j + 1) ≤
      fiberUpperPrefactor (M + 2) * Real.exp
        (((M : ℝ) + 3) * V22.cr (fiberSkew q) - V22.c0Prime (fiberSkew q) ((M : ℝ) + 2) -
          (1 - fiberSkew q ^ 2) * V22.rho ((M : ℝ) + 2) / 2 * fiberSquareOffset q M j +
          V22.epsilonPrime (fiberSkew q) ((M : ℝ) + 2) * Real.sqrt (fiberSquareOffset q M j)) := by
  have hq0' : 0 < q := by linarith
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hr1 : fiberSkew q < 1 := by unfold fiberSkew; linarith
  have hx := fiber_upper_standard_square hq0' hq1 M j
  have habs : |sharedGaussianX (fiberSkew q) (M + 2) (j + 1)| = Real.sqrt (fiberSquareOffset q M j) := by
    rw [← hx, Real.sqrt_sq_eq_abs]
  have hb := binomial_gaussian_upper_normalized (by omega : 2 ≤ M + 2) hr0 hr1 (j + 1)
  rw [show (1 + fiberSkew q) / 2 = q by unfold fiberSkew; ring, hx, habs] at hb
  have hc := interiorCentralPrefactor_pos (M + 2)
  have hh : (Real.sqrt (1 - fiberSkew q ^ 2) * binom (M + 2) q (j + 1)) /
      interiorCentralPrefactor (M + 2) ≤
      (fiberUpperPrefactor (M + 2) * Real.exp
        (((M : ℝ) + 3) * V22.cr (fiberSkew q) - V22.c0Prime (fiberSkew q) ((M : ℝ) + 2) -
          (1 - fiberSkew q ^ 2) * V22.rho ((M : ℝ) + 2) / 2 * fiberSquareOffset q M j +
          V22.epsilonPrime (fiberSkew q) ((M : ℝ) + 2) * Real.sqrt (fiberSquareOffset q M j))) /
      interiorCentralPrefactor (M + 2) := by
    push_cast at hb
    unfold fiberUpperPrefactor
    convert hb using 1 <;> congr 1 <;> ring
  exact (div_le_div_iff_of_pos_right hc).mp hh

theorem fiber_binomial_upper_linearized {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 1)
    (M : ℕ) (j : ℤ) :
    Real.sqrt (1 - fiberSkew q ^ 2) * binom (M + 2) q (j + 1) ≤
      fiberUpperPrefactor (M + 2) * Real.exp
        (((M : ℝ) + 3) * V22.cr (fiberSkew q) - V22.c0Prime (fiberSkew q) ((M : ℝ) + 2) +
          V22.epsilonPrime (fiberSkew q) ((M : ℝ) + 2) * Real.sqrt (fiberBonus q M) / 2 -
          V22.rhoU (fiberSkew q) ((M : ℝ) + 2) * fiberSquareOffset q M j / 2) := by
  have hq0' : 0 < q := by linarith
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hr1 : fiberSkew q < 1 := by unfold fiberSkew; linarith
  have hg : 0 < fiberBonus q M := by
    have hb := fiber_bonus_current_formula hq0' hq1 M
    rw [hb]
    have hh : 0 ≤ ((M : ℝ) + 2) - 1 + 1 / ((M : ℝ) + 2) := by
      have hi : 0 ≤ (1 : ℝ) / ((M : ℝ) + 2) := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) M]
    nlinarith [mul_nonneg hh (sq_nonneg (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)))]
  have he := shared_epsilonPrime_nonneg hr0 hr1 (by positivity : 0 < (M : ℝ) + 2)
  have hamgm := fiber_mass_amgm (fiber_square_offset_nonneg hq0' hq1 M j) hg
  have hsq := Real.sq_sqrt hg.le
  have hs := Real.sqrt_pos.2 hg
  have hlin : Real.sqrt (fiberSquareOffset q M j) ≤
      Real.sqrt (fiberBonus q M) / 2 + fiberSquareOffset q M j / (2 * Real.sqrt (fiberBonus q M)) := by
    have hamgm' := (le_div_iff₀ hs).mp hamgm
    have hi : Real.sqrt (fiberBonus q M) / 2 + fiberSquareOffset q M j / (2 * Real.sqrt (fiberBonus q M)) =
        (fiberBonus q M + fiberSquareOffset q M j) / (2 * Real.sqrt (fiberBonus q M)) := by
      field_simp [hs.ne']
      nlinarith [hsq]
    rw [hi]
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hs)).2
    nlinarith [hamgm']
  have hmul := mul_le_mul_of_nonneg_left hlin he
  apply (fiber_binomial_gaussian_upper_actual hq0 hq1 M j).trans
  apply mul_le_mul_of_nonneg_left _ (symmetricUpperPrefactor_pos (M + 2)).le
  apply Real.exp_le_exp.mpr
  unfold V22.rhoU
  rw [fiber_upper_gamma_identity hq0' hq1 M]
  convert add_le_add_left hmul (((M : ℝ) + 3) * V22.cr (fiberSkew q) -
    V22.c0Prime (fiberSkew q) ((M : ℝ) + 2) -
    (1 - fiberSkew q ^ 2) * V22.rho ((M : ℝ) + 2) / 2 * fiberSquareOffset q M j) using 1 <;> ring

theorem fiber_upper_minorant {q mu : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    fiberScalarH (fiberUpperP mu (fiberSkew q) (M + 2)) (((M : ℝ) + 2) / mu)
      (V22.rhoU (fiberSkew q) ((M : ℝ) + 2)) (fiberBonus q M) (fiberSquareOffset q M j) ≤
      fiberF q mu M j := by
  have hq0' : 0 < q := by linarith
  have hb := fiber_binomial_upper_linearized hq0 hq1 M j
  let C : ℝ := mu ^ (3 / 2 : ℝ) / (2 * fiberAG * ((M : ℝ) + 1))
  have hC : 0 ≤ C := by dsimp [C]; have := fiber_AG_pos; positivity
  have hc := mul_le_mul_of_nonneg_left hb hC
  have hd := mul_le_mul_of_nonpos_right hc (sub_nonpos.mpr hw)
  have he : fiberScalarH (fiberUpperP mu (fiberSkew q) (M + 2)) (((M : ℝ) + 2) / mu)
      (V22.rhoU (fiberSkew q) ((M : ℝ) + 2)) (fiberBonus q M) (fiberSquareOffset q M j) =
    C * (fiberUpperPrefactor (M + 2) * Real.exp
        (((M : ℝ) + 3) * V22.cr (fiberSkew q) - V22.c0Prime (fiberSkew q) ((M : ℝ) + 2) +
          V22.epsilonPrime (fiberSkew q) ((M : ℝ) + 2) * Real.sqrt (fiberBonus q M) / 2 -
          V22.rhoU (fiberSkew q) ((M : ℝ) + 2) * fiberSquareOffset q M j / 2)) *
      (fiberBonus q M - fiberSquareOffset q M j) + (((M : ℝ) + 2) / mu) * fiberSquareOffset q M j := by
    unfold fiberScalarH fiberUpperP shapeTemplatePrefactor
    rw [← fiber_AG_port_identity]
    push_cast
    rw [fiber_upper_gamma_identity hq0' hq1 M]
    rw [show (M : ℝ) + 2 - 1 = (M : ℝ) + 1 by ring]
    dsimp [C]
    rw [show -V22.rhoU (fiberSkew q) ((M : ℝ) + 2) * fiberSquareOffset q M j / 2 =
      -(V22.rhoU (fiberSkew q) ((M : ℝ) + 2) * fiberSquareOffset q M j / 2) by ring,
      Real.exp_neg, Real.exp_sub]
    rw [show (M : ℝ) + 2 + 1 = (M : ℝ) + 3 by ring]
    ring
  rw [he, fiber_F_normalized M j hq0' hq1 hmu]
  dsimp [C] at hd
  convert add_le_add_right hd ((((M : ℝ) + 2) / mu) * fiberSquareOffset q M j) using 1 <;> ring

theorem fiber_upper_constrained_gain {M : ℕ} (hM : 8 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ)
    (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    fiberBonus q M - 2 / V22.rhoU (fiberSkew q) ((M : ℝ) + 2) *
      V22.G (min 0 (fiberUpperOmega mu (fiberSkew q) (M + 2))) ≤
        fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hN : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 10 ≤ M + 2)
  have hR : 0 < V22.rhoU (fiberSkew q) ((M : ℝ) + 2) :=
    lt_trans (by norm_num) (fiber_uniform_upper_rate hN hr0 hrh)
  have hP := fiber_upper_P_pos (r := fiberSkew q) hmu (by omega : 2 ≤ M + 2)
  have hB : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hh := (fiber_H_constrained_minimum hP hB hR (fiberBonus q M)).2
    ⟨fiberSquareOffset q M j, hw, rfl⟩
  have hO : fiberScalarOmega (fiberUpperP mu (fiberSkew q) (M + 2)) (((M : ℝ) + 2) / mu)
      (V22.rhoU (fiberSkew q) ((M : ℝ) + 2)) (fiberBonus q M) =
        fiberUpperOmega mu (fiberSkew q) (M + 2) := by
    unfold fiberScalarOmega fiberUpperOmega
    push_cast
    rw [fiber_upper_gamma_identity hq0' hq1 M]
  rw [hO] at hh
  exact (le_div_iff₀ hB).2 (by
    convert hh.trans (fiber_upper_minorant hq0 hq1 hmu M j hw) using 1 <;> ring)

end Erdos993Lean.Analytic.V213
