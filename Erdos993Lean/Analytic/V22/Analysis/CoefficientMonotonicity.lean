module

public import Erdos993Lean.Analytic.V22.Functions
public import Mathlib.Tactic

/-!
# Version 2.2 of the manuscript, Lemma 4.10: coefficient guards and monotonicity

All functions here are the shared D1 definitions. Every denominator guard
is proved from `N>=10` and `0<=rm<=1/2`; no additional analytic guard is
assumed. The final scaled `N*alpha2` result retains the actual varying size
and does not assume that a capped `nu_m` stays constant. The parent owns
serialized Lean verification.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem coefficient_rm_sq_bounds {rm : ℝ} (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) :
    0 ≤ rm ^ 2 ∧ rm ^ 2 ≤ 1 / 4 ∧ 3 / 4 ≤ 1 - rm ^ 2 := by
  have hs := (sq_le_sq₀ hr0 (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hr1
  norm_num at hs
  exact ⟨sq_nonneg rm, hs, by linarith⟩

theorem coefficient_one_sub_rm_sq_pos {rm : ℝ} (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) :
    0 < 1 - rm ^ 2 := by
  linarith [(coefficient_rm_sq_bounds hr0 hr1).2.2]

theorem coefficient_cCoef_bounds {N : ℝ} (hN : 10 ≤ N) :
    (9 / 10 : ℝ) ≤ cCoef N ∧ cCoef N ≤ 1 := by
  have hn : 0 < N := by linarith
  have hi : (1 : ℝ) / N ≤ 1 / 10 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
  unfold cCoef
  constructor
  · linarith
  · exact sub_le_self _ (div_nonneg (by norm_num) hn.le)

theorem coefficient_sqrt_cCoef_bounds {N : ℝ} (hN : 10 ≤ N) :
    (9 / 10 : ℝ) ≤ Real.sqrt (cCoef N) ∧ 0 < Real.sqrt (cCoef N) := by
  have hc := (coefficient_cCoef_bounds hN).1
  have hs : (9 / 10 : ℝ) ≤ Real.sqrt (cCoef N) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  exact ⟨hs, by linarith⟩

theorem coefficient_Z0_pos {N : ℝ} (hN : 10 ≤ N) : 0 < Z0 N := by
  unfold Z0
  exact div_pos (Real.sqrt_pos.2 (by linarith)) (by linarith)

theorem coefficient_Z0_sq {N : ℝ} (hN : 10 ≤ N) :
    (Z0 N) ^ 2 = N / (N + 1) ^ 2 := by
  rw [Z0, div_pow, Real.sq_sqrt (by linarith : 0 ≤ N)]

theorem coefficient_Z0_le_third {N : ℝ} (hN : 10 ≤ N) : Z0 N ≤ 1 / 3 := by
  have hn : 0 ≤ N := by linarith
  have hpoly : (9 : ℝ) * N ≤ (N + 1) ^ 2 := by
    nlinarith [mul_nonneg hn (show 0 ≤ N - 10 by linarith)]
  have hs : (Z0 N) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    rw [coefficient_Z0_sq hN]
    apply (div_le_iff₀ (sq_pos_of_pos (show 0 < N + 1 by linarith))).2
    nlinarith
  exact (sq_le_sq₀ (coefficient_Z0_pos hN).le (by norm_num)).1 hs

theorem coefficient_Z0_antitone {N M : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M) :
    Z0 M ≤ Z0 N := by
  have hM : 10 ≤ M := hN.trans hNM
  have hpoly : M * (N + 1) ^ 2 ≤ N * (M + 1) ^ 2 := by
    have hprod : 0 ≤ (M - N) * (N * M - 1) := by
      apply mul_nonneg (sub_nonneg.mpr hNM)
      nlinarith [mul_nonneg (show 0 ≤ N - 10 by linarith) (show 0 ≤ M by linarith)]
    nlinarith
  have hs : (Z0 M) ^ 2 ≤ (Z0 N) ^ 2 := by
    rw [coefficient_Z0_sq hM, coefficient_Z0_sq hN]
    exact (div_le_div_iff₀ (sq_pos_of_pos (show 0 < M + 1 by linarith))
      (sq_pos_of_pos (show 0 < N + 1 by linarith))).2 hpoly
  exact (sq_le_sq₀ (coefficient_Z0_pos hM).le (coefficient_Z0_pos hN).le).1 hs

theorem coefficient_phiM_bounds {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) : 1 ≤ phiM N rm ∧ phiM N rm ≤ 4 / 3 := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hs3 : (3 : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
  have hquot : 2 * rm / Real.sqrt N ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ hs).2
    linarith
  unfold phiM
  exact ⟨le_add_of_nonneg_right (div_nonneg (by linarith) hs.le), by linarith⟩

theorem coefficient_phiM_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) : phiM M rm ≤ phiM N rm := by
  unfold phiM
  have hdiv : 2 * rm / Real.sqrt M ≤ 2 * rm / Real.sqrt N :=
    div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_le_sqrt hNM)
  linarith

theorem coefficient_KL_den_pos {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) : 0 < 1 - (Z0 N) ^ 2 * (phiM N rm) ^ 2 := by
  have hz := coefficient_Z0_le_third hN
  have hp := coefficient_phiM_bounds hN hr0 hr1
  have hprod : Z0 N * phiM N rm ≤ (4 / 9 : ℝ) := by
    have h := mul_le_mul hz hp.2 (by linarith : 0 ≤ phiM N rm) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    norm_num at h
    exact h
  have hsq := (sq_le_sq₀
    (mul_nonneg (coefficient_Z0_pos hN).le (by linarith : 0 ≤ phiM N rm))
    (by norm_num : (0 : ℝ) ≤ 4 / 9)).2 hprod
  nlinarith

theorem coefficient_KR_den_pos {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) : 0 < 1 - (rm + Z0 N) ^ 2 := by
  have hsum : rm + Z0 N ≤ (5 / 6 : ℝ) := by linarith [coefficient_Z0_le_third hN]
  have hsq := (sq_le_sq₀ (add_nonneg hr0 (coefficient_Z0_pos hN).le)
    (by norm_num : (0 : ℝ) ≤ 5 / 6)).2 hsum
  nlinarith

theorem coefficient_KL_nonneg {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) : 0 ≤ KL N rm := by
  unfold KL
  exact add_nonneg (by norm_num) (div_nonneg (sq_nonneg _) (coefficient_KL_den_pos hN hr0 hr1).le)

theorem coefficient_KR_nonneg {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) : 0 ≤ KR N rm := by
  unfold KR
  exact div_nonneg (by norm_num) (coefficient_KR_den_pos hN hr0 hr1).le

theorem coefficient_KL_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : KL M rm ≤ KL N rm := by
  have hM : 10 ≤ M := hN.trans hNM
  have hpN := coefficient_phiM_bounds hN hr0 hr1
  have hpM := coefficient_phiM_bounds hM hr0 hr1
  have hp := coefficient_phiM_antitone hN hNM hr0
  have hprod : Z0 M * phiM M rm ≤ Z0 N * phiM N rm :=
    mul_le_mul (coefficient_Z0_antitone hN hNM) hp (by linarith) (coefficient_Z0_pos hN).le
  have hprodSq := (sq_le_sq₀
    (mul_nonneg (coefficient_Z0_pos hM).le (by linarith))
    (mul_nonneg (coefficient_Z0_pos hN).le (by linarith))).2 hprod
  have hden : 1 - (Z0 N) ^ 2 * (phiM N rm) ^ 2 ≤
      1 - (Z0 M) ^ 2 * (phiM M rm) ^ 2 := by nlinarith
  have hnum := (sq_le_sq₀ (by linarith : 0 ≤ phiM M rm) (by linarith : 0 ≤ phiM N rm)).2 hp
  unfold KL
  have hdiv : (phiM M rm) ^ 2 / (1 - (Z0 M) ^ 2 * (phiM M rm) ^ 2) ≤
      (phiM N rm) ^ 2 / (1 - (Z0 N) ^ 2 * (phiM N rm) ^ 2) :=
    div_le_div₀ (sq_nonneg _) hnum (coefficient_KL_den_pos hN hr0 hr1) hden
  linarith

theorem coefficient_KR_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : KR M rm ≤ KR N rm := by
  have hM : 10 ≤ M := hN.trans hNM
  have hsum : rm + Z0 M ≤ rm + Z0 N := by
    linarith [coefficient_Z0_antitone hN hNM]
  have hsq := (sq_le_sq₀ (add_nonneg hr0 (coefficient_Z0_pos hM).le)
    (add_nonneg hr0 (coefficient_Z0_pos hN).le)).2 hsum
  unfold KR
  exact div_le_div_of_nonneg_left (by norm_num) (coefficient_KR_den_pos hN hr0 hr1)
    (by linarith)

theorem coefficient_cCoef_monotone {N M : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M) :
    cCoef N ≤ cCoef M := by
  have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (show 0 < N by linarith) hNM
  unfold cCoef
  linarith

theorem coefficient_rho_monotone {N M : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M) : rho N ≤ rho M := by
  unfold rho
  apply (div_le_div_iff₀ (show 0 < N + 1 by linarith) (show 0 < M + 1 by linarith)).2
  nlinarith

theorem coefficient_cL1_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : cL1 M rm ≤ cL1 N rm := by
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  unfold cL1
  exact div_le_div₀ (mul_nonneg (by norm_num) (coefficient_KL_nonneg hN hr0 hr1))
    (mul_le_mul_of_nonneg_left (coefficient_KL_antitone hN hNM hr0 hr1) (by norm_num))
    (mul_pos (by linarith) hd) (mul_le_mul_of_nonneg_right hNM hd.le)

theorem coefficient_cR1_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : cR1 M rm ≤ cR1 N rm := by
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  unfold cR1
  exact div_le_div₀ (mul_nonneg (by norm_num) (coefficient_KR_nonneg hN hr0 hr1))
    (mul_le_mul_of_nonneg_left (coefficient_KR_antitone hN hNM hr0 hr1) (by norm_num))
    (mul_pos (by linarith) hd) (mul_le_mul_of_nonneg_right (by linarith) hd.le)

theorem coefficient_cL2_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : cL2 M rm ≤ cL2 N rm := by
  have hn : 0 < N := by linarith
  have hm : 0 < M := hn.trans_le hNM
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hfirst : 4 * KL M rm / M ^ 2 ≤ 4 * KL N rm / N ^ 2 :=
    div_le_div₀ (mul_nonneg (by norm_num) (coefficient_KL_nonneg hN hr0 hr1))
    (mul_le_mul_of_nonneg_left (coefficient_KL_antitone hN hNM hr0 hr1) (by norm_num))
    (sq_pos_of_pos hn) ((sq_le_sq₀ hn.le hm.le).2 hNM)
  have hsecond := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hn hNM
  unfold cL2
  exact div_le_div_of_nonneg_right (add_le_add hfirst hsecond) hd.le

theorem coefficient_cR2_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : cR2 M rm ≤ cR2 N rm := by
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  unfold cR2
  exact div_le_div₀ (add_nonneg (coefficient_KR_nonneg hN hr0 hr1) (by norm_num))
    (add_le_add (coefficient_KR_antitone hN hNM hr0 hr1) (le_refl 1))
    (mul_pos (by linarith) hd) (mul_le_mul_of_nonneg_right hNM hd.le)

theorem coefficient_alpha1_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : alpha1 M rm ≤ alpha1 N rm := by
  unfold alpha1
  have hdiv : max (cL1 M rm) (cR1 M rm) / 12 ≤ max (cL1 N rm) (cR1 N rm) / 12 :=
    div_le_div_of_nonneg_right
      (max_le_max (coefficient_cL1_antitone hN hNM hr0 hr1)
        (coefficient_cR1_antitone hN hNM hr0 hr1)) (by norm_num)
  linarith

theorem coefficient_alpha2_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : alpha2 M rm ≤ alpha2 N rm := by
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hfirst := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (mul_pos (show 0 < N by linarith) hd) (mul_le_mul_of_nonneg_right hNM hd.le)
  unfold alpha2
  exact add_le_add hfirst (div_le_div_of_nonneg_right
    (max_le_max (coefficient_cL2_antitone hN hNM hr0 hr1)
      (coefficient_cR2_antitone hN hNM hr0 hr1)) (by norm_num))

theorem coefficient_alpha_nonneg {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) : 0 ≤ alpha1 N rm ∧ 0 ≤ alpha2 N rm := by
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hKL := coefficient_KL_nonneg hN hr0 hr1
  have hKR := coefficient_KR_nonneg hN hr0 hr1
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  unfold alpha1 alpha2 cL1 cR1 cL2 cR2
  constructor <;> positivity

theorem coefficient_kappaA_scaled {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) :
    kappaA N rm = 2 + (2 / (3 * (1 - rm ^ 2))) * ((1 + 1 / N) / Real.sqrt (cCoef N)) := by
  unfold kappaA
  field_simp [(show 0 < N by linarith).ne', (coefficient_one_sub_rm_sq_pos hr0 hr1).ne',
    (coefficient_sqrt_cCoef_bounds hN).2.ne'] <;> ring

theorem coefficient_kappaA_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : kappaA M rm ≤ kappaA N rm := by
  have hM : 10 ≤ M := hN.trans hNM
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hnum : 1 + 1 / M ≤ 1 + 1 / N := by
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (show 0 < N by linarith) hNM
    linarith
  have hdiv := div_le_div₀ (show 0 ≤ 1 + 1 / N by positivity) hnum
    (coefficient_sqrt_cCoef_bounds hN).2 (Real.sqrt_le_sqrt (coefficient_cCoef_monotone hN hNM))
  rw [coefficient_kappaA_scaled hM hr0 hr1, coefficient_kappaA_scaled hN hr0 hr1]
  have hmul := mul_le_mul_of_nonneg_left hdiv
    (by positivity : 0 ≤ 2 / (3 * (1 - rm ^ 2)))
  linarith

theorem coefficient_rhoStar_monotone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : rhoStar N rm ≤ rhoStar M rm := by
  have hM : 10 ≤ M := hN.trans hNM
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hroot := Real.sqrt_le_sqrt (coefficient_cCoef_monotone hN hNM)
  have hrootN := (coefficient_sqrt_cCoef_bounds hN).2
  have hprod : (N + 1) * Real.sqrt (cCoef N) ≤ (M + 1) * Real.sqrt (cCoef M) :=
    mul_le_mul (by linarith) hroot hrootN.le (by linarith)
  have hterm2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (mul_pos (by linarith) hrootN) hprod
  have hterm3 := div_le_div_of_nonneg_left (sq_nonneg rm)
    (mul_pos (mul_pos (by norm_num) hd) hrootN)
    (mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 3 * (1 - rm ^ 2)))
  have hmain := mul_le_mul_of_nonneg_left (coefficient_rho_monotone hN hNM) hd.le
  unfold rhoStar
  linarith

/-- A uniform positive lower guard for the all-offset shape coefficient. -/
theorem coefficient_rhoStar_pos {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) : 0 < rhoStar N rm := by
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hrsq := coefficient_rm_sq_bounds hr0 hr1
  have hs := coefficient_sqrt_cCoef_bounds hN
  have hrho : (10 / 11 : ℝ) ≤ rho N := by
    have h := coefficient_rho_monotone (N := 10) (M := N) (by norm_num) hN
    norm_num [rho] at h
    exact h
  have hmain : (15 / 22 : ℝ) ≤ (1 - rm ^ 2) * rho N := by
    have h := mul_le_mul hrsq.2.2 hrho (by norm_num : (0 : ℝ) ≤ 10 / 11) hd.le
    norm_num at h
    exact h
  have hden2 : (99 / 10 : ℝ) ≤ (N + 1) * Real.sqrt (cCoef N) := by
    have h := mul_le_mul (show (11 : ℝ) ≤ N + 1 by linarith) hs.1
      (by norm_num : (0 : ℝ) ≤ 9 / 10) (by linarith : 0 ≤ N + 1)
    norm_num at h
    exact h
  have hterm2 : 2 / ((N + 1) * Real.sqrt (cCoef N)) ≤ (20 / 99 : ℝ) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 99 / 10) hden2
    norm_num at h
    exact h
  have hden3 : (81 / 40 : ℝ) ≤ 3 * (1 - rm ^ 2) * Real.sqrt (cCoef N) := by
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left hrsq.2.2 (by norm_num : (0 : ℝ) ≤ 3)) hs.1
      (by norm_num : (0 : ℝ) ≤ 9 / 10) (by positivity : 0 ≤ 3 * (1 - rm ^ 2))
    norm_num at h
    exact h
  have hterm3 : rm ^ 2 / (3 * (1 - rm ^ 2) * Real.sqrt (cCoef N)) ≤ (10 / 81 : ℝ) := by
    have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hrsq.2.1
      (by norm_num : (0 : ℝ) < 81 / 40) hden3
    norm_num at h
    exact h
  unfold rhoStar
  linarith

theorem coefficient_remaining_nonneg {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) :
    0 ≤ kappaA N rm ∧ 0 ≤ e2 ∧ 0 ≤ e3 rm ∧ 0 ≤ e4 N rm ∧ 0 ≤ e5 rm := by
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hs := (coefficient_sqrt_cCoef_bounds hN).2
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  unfold kappaA e2 e3 e4 e5
  constructor
  · positivity
  constructor
  · norm_num
  constructor
  · positivity
  constructor <;> positivity

theorem coefficient_e4_scaled {N rm : ℝ} (hN : 10 ≤ N) :
    e4 N rm = (1 + 1 / N) / (12 * (1 - rm ^ 2) ^ 2) := by
  unfold e4
  by_cases hd : 1 - rm ^ 2 = 0
  · simp [hd]
  · field_simp [(show 0 < N by linarith).ne', hd] <;> ring

theorem coefficient_e4_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M) :
    e4 M rm ≤ e4 N rm := by
  rw [coefficient_e4_scaled (hN.trans hNM), coefficient_e4_scaled hN]
  have hnum : 1 + 1 / M ≤ 1 + 1 / N := by
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (show 0 < N by linarith) hNM
    linarith
  exact div_le_div_of_nonneg_right hnum
    (mul_nonneg (by norm_num) (sq_nonneg _))

theorem coefficient_E_antitone {N M rm nu : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M) :
    E M rm nu ≤ E N rm nu := by
  have h := mul_le_mul_of_nonneg_right (coefficient_e4_antitone (rm := rm) hN hNM)
    (pow_nonneg (sq_nonneg nu) 2)
  unfold E
  have h4 : e4 M rm * nu ^ 4 ≤ e4 N rm * nu ^ 4 := by
    simpa only [← pow_mul] using h
  linarith

/-- Exact identity exposing the scaled second coefficient's monotonic pieces. -/
theorem coefficient_N_alpha2_eq {N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hr1 : rm ≤ 1 / 2) :
    N * alpha2 N rm = 2 / (1 - rm ^ 2) +
      max ((4 * KL N rm / N + 1) / (1 - rm ^ 2))
        ((KR N rm + 1) / (1 - rm ^ 2)) / 12 := by
  have hn : N ≠ 0 := (show 0 < N by linarith).ne'
  have hd := (coefficient_one_sub_rm_sq_pos hr0 hr1).ne'
  have hbase : N * (2 / (N * (1 - rm ^ 2))) = 2 / (1 - rm ^ 2) := by
    field_simp [hn, hd] <;> ring
  have hL : N * cL2 N rm = (4 * KL N rm / N + 1) / (1 - rm ^ 2) := by
    unfold cL2
    field_simp [hn, hd] <;> ring
  have hR : N * cR2 N rm = (KR N rm + 1) / (1 - rm ^ 2) := by
    unfold cR2
    field_simp [hn, hd] <;> ring
  calc
    N * alpha2 N rm = N * (2 / (N * (1 - rm ^ 2))) +
        (N * max (cL2 N rm) (cR2 N rm)) / 12 := by unfold alpha2; ring
    _ = _ := by rw [hbase, mul_max_of_nonneg _ _ (show 0 ≤ N by linarith), hL, hR]

theorem coefficient_N_alpha2_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) : M * alpha2 M rm ≤ N * alpha2 N rm := by
  have hM : 10 ≤ M := hN.trans hNM
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hKLdiv : 4 * KL M rm / M ≤ 4 * KL N rm / N :=
    div_le_div₀ (mul_nonneg (by norm_num) (coefficient_KL_nonneg hN hr0 hr1))
    (mul_le_mul_of_nonneg_left (coefficient_KL_antitone hN hNM hr0 hr1) (by norm_num))
    (show 0 < N by linarith) hNM
  have hL := div_le_div_of_nonneg_right (add_le_add hKLdiv (le_refl 1)) hd.le
  have hR := div_le_div_of_nonneg_right
    (add_le_add (coefficient_KR_antitone hN hNM hr0 hr1) (le_refl 1)) hd.le
  rw [coefficient_N_alpha2_eq hM hr0 hr1, coefficient_N_alpha2_eq hN hr0 hr1]
  have hdiv : max ((4 * KL M rm / M + 1) / (1 - rm ^ 2))
      ((KR M rm + 1) / (1 - rm ^ 2)) / 12 ≤
      max ((4 * KL N rm / N + 1) / (1 - rm ^ 2))
      ((KR N rm + 1) / (1 - rm ^ 2)) / 12 :=
    div_le_div_of_nonneg_right (max_le_max hL hR) (by norm_num)
  linarith

theorem coefficient_N_alpha2_antitoneOn (rm : ℝ) (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) :
    AntitoneOn (fun N => N * alpha2 N rm) (Ici 10) := by
  intro N hN M _ hNM
  exact coefficient_N_alpha2_antitone hN hNM hr0 hr1

/-- Useful for the uncapped branch of `nu_m=min(6,rm*sqrt(N))`. -/
theorem coefficient_sqrt_alpha2_antitone {N M rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) :
    alpha2 M rm * Real.sqrt M ≤ alpha2 N rm * Real.sqrt N := by
  have hM : 10 ≤ M := hN.trans hNM
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 (by linarith)
  have heq : ∀ X : ℝ, 10 ≤ X →
      alpha2 X rm * Real.sqrt X = (X * alpha2 X rm) / Real.sqrt X := by
    intro X hX
    apply (eq_div_iff (Real.sqrt_pos.2 (by linarith : 0 < X)).ne').2
    rw [mul_assoc, ← pow_two, Real.sq_sqrt (by linarith : 0 ≤ X)]
    ring
  rw [heq M hM, heq N hN]
  exact div_le_div₀ (mul_nonneg (by linarith) (coefficient_alpha_nonneg hN hr0 hr1).2)
    (coefficient_N_alpha2_antitone hN hNM hr0 hr1) hsN (Real.sqrt_le_sqrt hNM)

/-- The source last sentence, as whole-domain order assertions. -/
theorem source_coefficient_monotonicity (rm : ℝ) (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) :
    AntitoneOn (fun N => alpha1 N rm) (Ici 10) ∧
    AntitoneOn (fun N => alpha2 N rm) (Ici 10) ∧
    AntitoneOn (fun N => kappaA N rm) (Ici 10) ∧
    AntitoneOn (fun N => e4 N rm) (Ici 10) ∧
    MonotoneOn (fun N => rhoStar N rm) (Ici 10) :=
  ⟨fun _ hN _ _ hNM => coefficient_alpha1_antitone hN hNM hr0 hr1,
    fun _ hN _ _ hNM => coefficient_alpha2_antitone hN hNM hr0 hr1,
    fun _ hN _ _ hNM => coefficient_kappaA_antitone hN hNM hr0 hr1,
    fun _ hN _ _ hNM => coefficient_e4_antitone hN hNM,
    fun _ hN _ _ hNM => coefficient_rhoStar_monotone hN hNM hr0 hr1⟩

theorem source_E_coefficient_monotonicity (rm : ℝ) :
    AntitoneOn (fun _ : ℝ => e2) (Ici 10) ∧
    AntitoneOn (fun _ : ℝ => e3 rm) (Ici 10) ∧
    AntitoneOn (fun N => e4 N rm) (Ici 10) ∧
    AntitoneOn (fun _ : ℝ => e5 rm) (Ici 10) :=
  ⟨fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => le_rfl,
    fun _ hN _ _ hNM => coefficient_e4_antitone hN hNM,
    fun _ _ _ _ _ => le_rfl⟩

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.coefficient_rm_sq_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_rm_sq_bounds
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_one_sub_rm_sq_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_one_sub_rm_sq_pos
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_cCoef_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_cCoef_bounds
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_sqrt_cCoef_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_sqrt_cCoef_bounds
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_Z0_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_Z0_pos
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_Z0_sq
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_Z0_sq
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_Z0_le_third
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_Z0_le_third
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_Z0_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_Z0_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_phiM_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_phiM_bounds
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_phiM_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_phiM_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_KL_den_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_KL_den_pos
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_KR_den_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_KR_den_pos
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_KL_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_KL_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_KR_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_KR_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_KL_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_KL_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_KR_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_KR_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_cCoef_monotone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_cCoef_monotone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_rho_monotone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_rho_monotone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_cL1_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_cL1_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_cR1_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_cR1_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_cL2_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_cL2_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_cR2_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_cR2_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_alpha1_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_alpha1_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_alpha2_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_alpha2_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_alpha_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_alpha_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_kappaA_scaled
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_kappaA_scaled
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_kappaA_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_kappaA_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_rhoStar_monotone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_rhoStar_monotone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_rhoStar_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_rhoStar_pos
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_remaining_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_remaining_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_e4_scaled
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_e4_scaled
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_e4_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_e4_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_E_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_E_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_N_alpha2_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_N_alpha2_eq
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_N_alpha2_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_N_alpha2_antitone
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_N_alpha2_antitoneOn
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_N_alpha2_antitoneOn
#check Erdos993Lean.Analytic.V22.Analysis.coefficient_sqrt_alpha2_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.coefficient_sqrt_alpha2_antitone
#check Erdos993Lean.Analytic.V22.Analysis.source_coefficient_monotonicity
#print axioms Erdos993Lean.Analytic.V22.Analysis.source_coefficient_monotonicity
#check Erdos993Lean.Analytic.V22.Analysis.source_E_coefficient_monotonicity
#print axioms Erdos993Lean.Analytic.V22.Analysis.source_E_coefficient_monotonicity
