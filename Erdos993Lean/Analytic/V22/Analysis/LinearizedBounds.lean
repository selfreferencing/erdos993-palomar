module

public import Erdos993Lean.Analytic.V22.Analysis.MonotoneLowerBounds

/-!
# Section 4: linearized coefficients and positive reciprocal denominators

Source: frozen note Lemma 4.10. This module owns the pointwise inequalities,
not the coefficient monotonicity in `N`. In particular `rhoStar>0` is proved
on the full source domain, rather than added to the reciprocal-loss theorem.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem linearized_cCoef_lower {N : ℝ} (hN : 10 ≤ N) : (9 / 10 : ℝ) ≤ V22.cCoef N := by
  have hn : 0 < N := by linarith
  have hi : 1 / N ≤ (1 / 10 : ℝ) := one_div_le_one_div_of_le (by norm_num) hN
  unfold V22.cCoef
  linarith

theorem linearized_sqrt_cCoef_lower {N : ℝ} (hN : 10 ≤ N) :
    (9 / 10 : ℝ) ≤ Real.sqrt (V22.cCoef N) := by
  have hc := linearized_cCoef_lower hN
  have hc0 : 0 ≤ V22.cCoef N := by linarith
  have hs := Real.sq_sqrt hc0
  have hs0 := Real.sqrt_nonneg (V22.cCoef N)
  nlinarith

/-- Automatic source-domain positivity; no extra `rhoStar>0` premise is needed. -/
theorem linearized_rhoStar_lower {N rm : ℝ} (hN : 10 ≤ N)
    (hrm0 : 0 ≤ rm) (hrmh : rm ≤ 1 / 2) : (1 / 3 : ℝ) ≤ V22.rhoStar N rm := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrmsq : rm ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hd : (3 / 4 : ℝ) ≤ 1 - rm ^ 2 := by linarith
  have hs := linearized_sqrt_cCoef_lower hN
  have hs0 : 0 < Real.sqrt (V22.cCoef N) := by linarith
  have hrho : (10 / 11 : ℝ) ≤ V22.rho N := by
    unfold V22.rho
    apply (le_div_iff₀ hn1).2
    linarith
  have hmain : (15 / 22 : ℝ) ≤ (1 - rm ^ 2) * V22.rho N := by
    have h := mul_le_mul hd hrho (by norm_num : (0 : ℝ) ≤ 10 / 11) (by linarith : 0 ≤ 1 - rm ^ 2)
    norm_num at h ⊢
    exact h
  have hden1 : (99 / 10 : ℝ) ≤ (N + 1) * Real.sqrt (V22.cCoef N) := by
    have h := mul_le_mul (show (11 : ℝ) ≤ N + 1 by linarith) hs (by norm_num : (0 : ℝ) ≤ 9 / 10) hn1.le
    norm_num at h
    exact h
  have hterm1 : 2 / ((N + 1) * Real.sqrt (V22.cCoef N)) ≤ (20 / 99 : ℝ) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 99 / 10) hden1
    norm_num at h
    exact h
  have hden2 : (81 / 40 : ℝ) ≤ 3 * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N) := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3)) hs
      (by norm_num : (0 : ℝ) ≤ 9 / 10) (by linarith : 0 ≤ 3 * (1 - rm ^ 2))
    norm_num at h
    exact h
  have hterm2 : rm ^ 2 / (3 * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N)) ≤ (10 / 81 : ℝ) := by
    calc
      _ ≤ (1 / 4 : ℝ) / (3 * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N)) :=
        div_le_div_of_nonneg_right hrmsq (by positivity)
      _ ≤ (1 / 4 : ℝ) / (81 / 40) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden2
      _ = _ := by norm_num
  unfold V22.rhoStar
  linarith

theorem linearized_nu_sqrt_fraction {c nu : ℝ} (hc : 0 < c) (hnu : 0 ≤ nu) :
    nu / Real.sqrt (1 + c * nu ^ 2) ≤ 1 / Real.sqrt c := by
  have hq : 0 < 1 + c * nu ^ 2 := by positivity
  have heq : nu * Real.sqrt c = Real.sqrt (c * nu ^ 2) := by
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq hnu]
    ring
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 hq) (Real.sqrt_pos.2 hc)).2
  rw [one_mul, heq]
  exact Real.sqrt_le_sqrt (by linarith)

theorem linearized_nu_cubic_sqrt_fraction {c nu : ℝ} (hc : 0 < c) (hnu : 0 ≤ nu) :
    nu ^ 3 / Real.sqrt (1 + c * nu ^ 2) ≤ nu ^ 2 / Real.sqrt c := by
  have h := mul_le_mul_of_nonneg_left (linearized_nu_sqrt_fraction hc hnu) (sq_nonneg nu)
  convert h using 1 <;> ring

theorem linearized_nu_sqrt_fraction_self {c nu : ℝ} (hc : 0 ≤ c) (hnu : 0 ≤ nu) :
    nu / Real.sqrt (1 + c * nu ^ 2) ≤ nu := by
  have hs : (1 : ℝ) ≤ Real.sqrt (1 + c * nu ^ 2) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ 1 + c * nu ^ 2 by nlinarith [mul_nonneg hc (sq_nonneg nu)])
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (1 + c * nu ^ 2))).2
  nlinarith

theorem linearized_epsilon_over_gamma_bound {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ≤
      2 / ((N + 1) * Real.sqrt (V22.cCoef N)) +
        rm ^ 2 / (3 * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N)) := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrh : r ≤ 1 / 2 := hrrm.trans hrmh
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hdm := shared_one_sub_sq_pos (by linarith : -1 < rm) (by linarith : rm < 1)
  have hc : 0 < V22.cCoef N := by linarith [linearized_cCoef_lower hN]
  have hs : 0 < Real.sqrt (V22.cCoef N) := Real.sqrt_pos.2 hc
  have hnu := activityNu_nonneg (N := N) hr0
  have hsq := activityNu_sq (r := r) hn.le
  have hrb : r ^ 2 < 1 := by nlinarith
  have ha : activityNu r N ^ 2 < N := by
    rw [hsq]
    simpa using mul_lt_mul_of_pos_right hrb hn
  have h := monotone_epsilon_over_gamma hr0 hrh hN ha le_rfl
  have hA : 1 + monotoneDeltaA r N N = 1 + V22.cCoef N * activityNu r N ^ 2 := by
    unfold monotoneDeltaA V22.cCoef
    ring
  rw [hA] at h
  apply h.trans
  have hq : 0 < Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2) := by positivity
  have hf := linearized_nu_sqrt_fraction hc hnu
  have hfc := linearized_nu_cubic_sqrt_fraction hc hnu
  have hsplit : monotoneEpsilonBound r N / Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2) =
      (2 / (N + 1)) * (activityNu r N / Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2)) +
      (1 / (3 * N * (1 - r ^ 2))) * (activityNu r N ^ 3 / Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2)) := by
    unfold monotoneEpsilonBound
    rw [activityNu_gap hn]
    field_simp [hn.ne', hn1.ne', hdr.ne', hq.ne'] <;> ring
  rw [hsplit]
  have h1 := mul_le_mul_of_nonneg_left hf (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn1.le)
  have h2 := mul_le_mul_of_nonneg_left hfc (by positivity : 0 ≤ 1 / (3 * N * (1 - r ^ 2)))
  have h2eq : (1 / (3 * N * (1 - r ^ 2))) * (activityNu r N ^ 2 / Real.sqrt (V22.cCoef N)) =
      r ^ 2 / (3 * (1 - r ^ 2) * Real.sqrt (V22.cCoef N)) := by
    rw [hsq]
    field_simp [hn.ne', hdr.ne', hs.ne'] <;> ring
  rw [h2eq] at h2
  have hrmsq : r ^ 2 ≤ rm ^ 2 := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hratio : r ^ 2 / (3 * (1 - r ^ 2) * Real.sqrt (V22.cCoef N)) ≤
      rm ^ 2 / (3 * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N)) := by
    calc
      _ ≤ rm ^ 2 / (3 * (1 - r ^ 2) * Real.sqrt (V22.cCoef N)) :=
        div_le_div_of_nonneg_right hrmsq (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg rm) (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith : 3 * (1 - rm ^ 2) ≤ 3 * (1 - r ^ 2)) hs.le)
  have h1eq : (2 / (N + 1)) * (1 / Real.sqrt (V22.cCoef N)) =
      2 / ((N + 1) * Real.sqrt (V22.cCoef N)) := by
    field_simp [hn1.ne', hs.ne'] <;> ring
  rw [h1eq] at h1
  linarith [h2.trans hratio]

/-- Exact source Lemma 4.10(b). -/
theorem linearized_rhoU_lower {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) : V22.rhoStar N rm ≤ V22.rhoU r N := by
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hsq : r ^ 2 ≤ rm ^ 2 := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hrho : 0 ≤ V22.rho N := by unfold V22.rho; positivity
  have hmain := mul_le_mul_of_nonneg_right (show 1 - rm ^ 2 ≤ 1 - r ^ 2 by linarith) hrho
  have he := linearized_epsilon_over_gamma_bound hN hr0 hrrm hrmh
  unfold V22.rhoU V22.rhoStar
  linarith

theorem linearized_rho_scaled_loss {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    2 * (N + 1) * (V22.rho N - V22.rhoU r N) ≤
      4 * activityNu r N + V22.kappaA N rm * activityNu r N ^ 2 := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrh : r ≤ 1 / 2 := hrrm.trans hrmh
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hdm := shared_one_sub_sq_pos (by linarith : -1 < rm) (by linarith : rm < 1)
  have hc : 0 < V22.cCoef N := by linarith [linearized_cCoef_lower hN]
  have hs : 0 < Real.sqrt (V22.cCoef N) := Real.sqrt_pos.2 hc
  have hnu := activityNu_nonneg (N := N) hr0
  have hsq := activityNu_sq (r := r) hn.le
  have hrb : r ^ 2 < 1 := by nlinarith
  have ha : activityNu r N ^ 2 < N := by
    rw [hsq]
    simpa using mul_lt_mul_of_pos_right hrb hn
  have h := monotone_epsilon_over_gamma hr0 hrh hN ha le_rfl
  have hA : 1 + monotoneDeltaA r N N = 1 + V22.cCoef N * activityNu r N ^ 2 := by
    unfold monotoneDeltaA V22.cCoef
    ring
  rw [hA] at h
  have hq : 0 < Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2) := by positivity
  have hf := linearized_nu_sqrt_fraction_self hc.le hnu
  have hfc := linearized_nu_cubic_sqrt_fraction hc hnu
  have hsplit : monotoneEpsilonBound r N / Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2) =
      (2 / (N + 1)) * (activityNu r N / Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2)) +
      (1 / (3 * N * (1 - r ^ 2))) * (activityNu r N ^ 3 / Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2)) := by
    unfold monotoneEpsilonBound
    rw [activityNu_gap hn]
    field_simp [hn.ne', hn1.ne', hdr.ne', hq.ne'] <;> ring
  have h1 := mul_le_mul_of_nonneg_left hf (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn1.le)
  have h2 := mul_le_mul_of_nonneg_left hfc (by positivity : 0 ≤ 1 / (3 * N * (1 - r ^ 2)))
  have hrmsq : r ^ 2 ≤ rm ^ 2 := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have h2replace : (1 / (3 * N * (1 - r ^ 2))) * (activityNu r N ^ 2 / Real.sqrt (V22.cCoef N)) ≤
      activityNu r N ^ 2 / (3 * N * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N)) := by
    have heq : (1 / (3 * N * (1 - r ^ 2))) * (activityNu r N ^ 2 / Real.sqrt (V22.cCoef N)) =
        activityNu r N ^ 2 / (3 * N * (1 - r ^ 2) * Real.sqrt (V22.cCoef N)) := by
      field_simp [hn.ne', hdr.ne', hs.ne'] <;> ring
    rw [heq]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ 3 * N) hs.le) (sub_nonneg.mpr hrmsq)]
  have hfrac : V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ≤
      2 * activityNu r N / (N + 1) +
        activityNu r N ^ 2 / (3 * N * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N)) := by
    rw [hsplit] at h
    have h1eq : (2 / (N + 1)) * activityNu r N = 2 * activityNu r N / (N + 1) := by ring
    rw [h1eq] at h1
    linarith [h2.trans h2replace]
  have hscaled := mul_le_mul_of_nonneg_left hfrac (by linarith : 0 ≤ 2 * (N + 1))
  have hbase : 2 * (N + 1) * (V22.rho N - V22.rhoU r N) =
      2 * activityNu r N ^ 2 + 2 * (N + 1) * (V22.epsilonPrime r N / Real.sqrt (V22.gamma r N)) := by
    unfold V22.rhoU V22.rho
    rw [hsq]
    field_simp [hn1.ne'] <;> ring
  have hright : 2 * activityNu r N ^ 2 + 2 * (N + 1) *
      (2 * activityNu r N / (N + 1) +
        activityNu r N ^ 2 / (3 * N * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N))) =
      4 * activityNu r N + V22.kappaA N rm * activityNu r N ^ 2 := by
    unfold V22.kappaA
    field_simp [hn.ne', hn1.ne', hdm.ne', hs.ne'] <;> ring
  rw [hbase]
  rw [← hright]
  linarith

/-- Exact source Lemma 4.10(c), with positivity discharged internally. -/
theorem linearized_reciprocal_loss {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) ≤
      (4 * activityNu r N + V22.kappaA N rm * activityNu r N ^ 2) / V22.rhoStar N rm := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hstar : 0 < V22.rhoStar N rm := by linarith [linearized_rhoStar_lower hN hrm0 hrmh]
  have hUstar := linearized_rhoU_lower hN hr0 hrrm hrmh
  have hU : 0 < V22.rhoU r N := hstar.trans_le hUstar
  have hdm := shared_one_sub_sq_pos (by linarith : -1 < rm) (by linarith : rm < 1)
  have hc : 0 < V22.cCoef N := by linarith [linearized_cCoef_lower hN]
  have hk : 0 ≤ V22.kappaA N rm := by unfold V22.kappaA; positivity
  have hnu := activityNu_nonneg (N := N) hr0
  have hnum : 0 ≤ 4 * activityNu r N + V22.kappaA N rm * activityNu r N ^ 2 := by positivity
  have heq : 2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) =
      (2 * (N + 1) * (V22.rho N - V22.rhoU r N)) / V22.rhoU r N := by
    unfold V22.rho
    field_simp [hn.ne', hn1.ne', hU.ne'] <;> ring
  rw [heq]
  calc
    _ ≤ (4 * activityNu r N + V22.kappaA N rm * activityNu r N ^ 2) / V22.rhoU r N :=
      div_le_div_of_nonneg_right (linearized_rho_scaled_loss hN hr0 hrrm hrmh) hU.le
    _ ≤ _ := div_le_div_of_nonneg_left hnum hstar hUstar

theorem linearized_eU_polynomial_actual {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) : N * V22.eU r N ≤ V22.E N r (activityNu r N) := by
  have hn : 0 < N := by linarith
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hnu := activityNu_nonneg (N := N) hr0
  have hc : 0 ≤ V22.cCoef N := by linarith [linearized_cCoef_lower hN]
  have hsq := activityNu_sq (r := r) hn.le
  have hrb : r ^ 2 < 1 := by nlinarith
  have ha : activityNu r N ^ 2 < N := by
    rw [hsq]
    simpa using mul_lt_mul_of_pos_right hrb hn
  have h := monotone_eU_upper hr0 hrh hN ha le_rfl
  have hA : 0 ≤ monotoneDeltaA r N N := by
    unfold monotoneDeltaA
    change 0 ≤ activityNu r N ^ 2 * V22.cCoef N
    exact mul_nonneg (sq_nonneg _) hc
  have hB : 0 ≤ monotoneDeltaBar r N N := by
    unfold monotoneDeltaBar
    rw [activityNu_quotient hn]
    exact div_nonneg (sq_nonneg _) hdr.le
  have hrootB : Real.sqrt (1 + monotoneDeltaBar r N N) ≤ 1 + monotoneDeltaBar r N N / 2 := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + monotoneDeltaBar r N N)
    have hs0 := Real.sqrt_nonneg (1 + monotoneDeltaBar r N N)
    nlinarith [sq_nonneg (monotoneDeltaBar r N N)]
  have hrootA : (1 : ℝ) ≤ Real.sqrt (1 + monotoneDeltaA r N N) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ 1 + monotoneDeltaA r N N by linarith)
  have hinvA : 1 / Real.sqrt (1 + monotoneDeltaA r N N) ≤ (1 : ℝ) := by
    apply (div_le_one (by linarith : 0 < Real.sqrt (1 + monotoneDeltaA r N N))).2
    exact hrootA
  have hsum : Real.sqrt (1 + monotoneDeltaBar r N N) + 1 / Real.sqrt (1 + monotoneDeltaA r N N) ≤
      2 + monotoneDeltaBar r N N / 2 := by linarith
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (2 * activityNu r N + activityNu r N ^ 3 / (3 * (1 - activityNu r N ^ 2 / N))) := by
    rw [activityNu_quotient hn]
    positivity
  have hprod := mul_le_mul_of_nonneg_left hsum hcoef
  have hexpand : activityNu r N ^ 2 / 2 +
      (1 / 2 : ℝ) * (2 * activityNu r N + activityNu r N ^ 3 / (3 * (1 - activityNu r N ^ 2 / N))) *
        (2 + monotoneDeltaBar r N N / 2) +
      (N + 1) * activityNu r N ^ 4 / (12 * N * (1 - activityNu r N ^ 2 / N) ^ 2) =
      V22.E N r (activityNu r N) := by
    unfold monotoneDeltaBar V22.E V22.e2 V22.e3 V22.e4 V22.e5
    rw [activityNu_quotient hn]
    field_simp [hn.ne', hdr.ne'] <;> ring
  rw [← hexpand]
  linarith

/-- Exact source Lemma 4.10(d), with all four positive coefficient terms retained. -/
theorem linearized_eU_upper {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    N * V22.eU r N ≤ V22.E N rm (activityNu r N) := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hdm := shared_one_sub_sq_pos (by linarith : -1 < rm) (by linarith : rm < 1)
  have hsq : r ^ 2 ≤ rm ^ 2 := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hnu := activityNu_nonneg (N := N) hr0
  apply (linearized_eU_polynomial_actual hN hr0 (hrrm.trans hrmh)).trans
  unfold V22.E V22.e2 V22.e3 V22.e4 V22.e5
  gcongr <;> nlinarith

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.linearized_cCoef_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_cCoef_lower
#check Erdos993Lean.Analytic.V22.Analysis.linearized_sqrt_cCoef_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_sqrt_cCoef_lower
#check Erdos993Lean.Analytic.V22.Analysis.linearized_rhoStar_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_rhoStar_lower
#check Erdos993Lean.Analytic.V22.Analysis.linearized_nu_sqrt_fraction
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_nu_sqrt_fraction
#check Erdos993Lean.Analytic.V22.Analysis.linearized_nu_cubic_sqrt_fraction
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_nu_cubic_sqrt_fraction
#check Erdos993Lean.Analytic.V22.Analysis.linearized_nu_sqrt_fraction_self
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_nu_sqrt_fraction_self
#check Erdos993Lean.Analytic.V22.Analysis.linearized_epsilon_over_gamma_bound
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_epsilon_over_gamma_bound
#check Erdos993Lean.Analytic.V22.Analysis.linearized_rhoU_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_rhoU_lower
#check Erdos993Lean.Analytic.V22.Analysis.linearized_rho_scaled_loss
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_rho_scaled_loss
#check Erdos993Lean.Analytic.V22.Analysis.linearized_reciprocal_loss
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_reciprocal_loss
#check Erdos993Lean.Analytic.V22.Analysis.linearized_eU_polynomial_actual
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_eU_polynomial_actual
#check Erdos993Lean.Analytic.V22.Analysis.linearized_eU_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.linearized_eU_upper
