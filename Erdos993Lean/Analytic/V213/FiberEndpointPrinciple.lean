module

public import Erdos993Lean.Analytic.V213.FiberEndpointGeometry
public import Erdos993Lean.Analytic.V213.FiberEndpointRoot

/-!
Literal Lemma6.11 endpoint propagation. The positive size-ratio domain,
actual inverse G, both target signs, closed threshold and all equality cases
are retained. The supremum is over the printed positive size-ratio domain.
No generated records or unproved paper lemma are premises.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberEndpointTarget (A c t : ℝ) : ℝ := A - 9 / 2 * t - c / t

noncomputable def fiberEndpointUpper (p d R t : ℝ) : ℝ :=
  1 + d - 2 / R * V22.G (min 0 (fiberEndpointLambda p t))

noncomputable def fiberEndpointRaw (p d R t : ℝ) : ℝ :=
  1 + d - 2 / R * V22.G (fiberEndpointLambda p t)

noncomputable def fiberEndpointDifference (p d R nu A c t : ℝ) : ℝ :=
  fiberEndpointRaw p d R t - nu * fiberEndpointTarget A c t

noncomputable def fiberEndpointK (p R nu c t : ℝ) : ℝ :=
  5 / R * fiberEndpointJ p t + nu * (9 / 2 * t ^ 2 - c)

noncomputable def fiberEndpointKPrime (p R nu t : ℝ) : ℝ :=
  5 / R * fiberEndpointJPrime p t + 9 * nu * t

noncomputable def fiberEndpointKSecond (p R nu t : ℝ) : ℝ :=
  5 / R * fiberEndpointJSecond p t + 9 * nu

theorem fiber_endpoint_upper_raw {p d R t : ℝ} (ht : 0 < t)
    (hs : t ≤ fiberEndpointStart p) : fiberEndpointUpper p d R t = fiberEndpointRaw p d R t := by
  unfold fiberEndpointUpper fiberEndpointRaw
  rw [min_eq_right (fiber_endpoint_lambda_nonpos ht hs)]

theorem fiber_endpoint_upper_constant {p d R t : ℝ}
    (hs : fiberEndpointStart p ≤ t) : fiberEndpointUpper p d R t = 1 + d := by
  have ht : 0 < t := lt_of_lt_of_le (fiber_endpoint_start_pos p) hs
  have hlog := Real.log_le_log (fiber_endpoint_start_pos p) hs
  unfold fiberEndpointStart at hlog
  rw [Real.log_exp] at hlog
  have hL : 0 ≤ fiberEndpointLambda p t := by unfold fiberEndpointLambda; linarith
  simp only [fiberEndpointUpper, min_eq_left hL, shared_G_zero, mul_zero, sub_zero]

theorem fiber_hasDerivAt_endpoint_target {A c t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberEndpointTarget A c) (-9 / 2 + c / t ^ 2) t := by
  have h := ((hasDerivAt_const t A).sub ((hasDerivAt_id t).const_mul (9 / 2 : ℝ))).sub
    ((hasDerivAt_const t c).div (hasDerivAt_id t) ht.ne')
  convert h using 1
  · funext x
    rfl
  · dsimp
    field_simp [ht.ne'] <;> ring

theorem fiber_hasDerivAt_endpoint_difference {p d R nu A c t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fiberEndpointDifference p d R nu A c) (fiberEndpointK p R nu c t / t ^ 2) t := by
  have hz := fiber_endpoint_z_pos p t
  have hg := (shared_hasDerivAt_G (fiberEndpointLambda p t)).comp t
    (fiber_hasDerivAt_endpoint_lambda ht)
  have hu := (hasDerivAt_const t (1 + d)).sub (hg.const_mul (2 / R))
  have h := hu.sub ((fiber_hasDerivAt_endpoint_target (A := A) (c := c) ht).const_mul nu)
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberEndpointK, fiberEndpointJ, fiberEndpointZ, V22.G1]
    field_simp [ht.ne', hz.ne'] <;> ring

theorem fiber_hasDerivAt_endpoint_K {p R nu c t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberEndpointK p R nu c) (fiberEndpointKPrime p R nu t) t := by
  have h := ((fiber_hasDerivAt_endpoint_J (p := p) ht).const_mul (5 / R)).add
    (((((hasDerivAt_id t).pow 2).const_mul (9 / 2 : ℝ)).sub_const c).const_mul nu)
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberEndpointKPrime]
    ring

theorem fiber_hasDerivAt_endpoint_KPrime {p R nu t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberEndpointKPrime p R nu) (fiberEndpointKSecond p R nu t) t := by
  have h := ((fiber_hasDerivAt_endpoint_JPrime (p := p) ht).const_mul (5 / R)).add
    ((hasDerivAt_id t).const_mul (9 * nu))
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberEndpointKSecond]
    ring

theorem fiber_endpoint_K_convex {p R nu c a : ℝ} (ha : 0 < a)
    (hR : 0 < R) (hnu : 0 ≤ nu) :
    ConvexOn ℝ (Icc a (fiberEndpointStart p)) (fiberEndpointK p R nu c) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fiberEndpointKPrime p R nu)
    (f'' := fiberEndpointKSecond p R nu) (convex_Icc _ _)
  · intro t ht
    exact (fiber_hasDerivAt_endpoint_K (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo a (fiberEndpointStart p) := by simpa only [interior_Icc] using ht
    exact (fiber_hasDerivAt_endpoint_K (ha.trans ht'.1)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo a (fiberEndpointStart p) := by simpa only [interior_Icc] using ht
    exact (fiber_hasDerivAt_endpoint_KPrime (ha.trans ht'.1)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo a (fiberEndpointStart p) := by simpa only [interior_Icc] using ht
    have hj := (fiber_endpoint_JSecond_pos (ha.trans ht'.1) ht'.2.le).le
    unfold fiberEndpointKSecond
    exact add_nonneg (mul_nonneg (by positivity) hj) (mul_nonneg (by norm_num) hnu)

theorem fiber_endpoint_K_terminal {p R nu c : ℝ} (hnu : 0 ≤ nu)
    (hs : fiberEndpointStart p ^ 2 ≤ 2 * c / 9) :
    fiberEndpointK p R nu c (fiberEndpointStart p) ≤ 0 := by
  simp only [fiberEndpointK, fiberEndpointJ, fiber_endpoint_z_start,
    sub_self, mul_zero, zero_div, add_zero, zero_add]
  exact mul_nonpos_of_nonneg_of_nonpos hnu (by nlinarith)

theorem fiber_endpoint_scaled_cap {A c d nu t : ℝ} (hd : 0 ≤ d)
    (hnu0 : 0 ≤ nu) (hnu1 : nu ≤ 1) (hf : fiberEndpointTarget A c t ≤ 1 + d) :
    nu * fiberEndpointTarget A c t ≤ 1 + d := by
  by_cases hpos : 0 ≤ fiberEndpointTarget A c t
  · exact (mul_le_mul_of_nonneg_right hnu1 hpos).trans (by simpa using hf)
  · exact (mul_nonpos_of_nonneg_of_nonpos hnu0 (le_of_lt (lt_of_not_ge hpos))).trans (by linarith)

theorem fiber_endpoint_single_target {p R d nu A c tau t : ℝ}
    (hR : 0 < R) (hd : 0 ≤ d) (hnu0 : 0 ≤ nu) (hnu1 : nu ≤ 1)
    (htau : 0 < tau) (httau : tau ≤ t)
    (hstar : fiberEndpointStart p ^ 2 ≤ 2 * c / 9)
    (hcap : ∀ x, 0 < x → fiberEndpointTarget A c x ≤ 1 + d)
    (hstart : nu * fiberEndpointTarget A c tau ≤ fiberEndpointUpper p d R tau) :
    nu * fiberEndpointTarget A c t ≤ fiberEndpointUpper p d R t := by
  have ht : 0 < t := lt_of_lt_of_le htau httau
  by_cases hts : t ≤ fiberEndpointStart p
  · have htaus : tau ≤ fiberEndpointStart p := httau.trans hts
    have hDa : 0 ≤ fiberEndpointDifference p d R nu A c tau := by
      rw [fiber_endpoint_upper_raw htau htaus] at hstart
      exact sub_nonneg.mpr hstart
    have hDb : 0 ≤ fiberEndpointDifference p d R nu A c (fiberEndpointStart p) := by
      have hscaled := fiber_endpoint_scaled_cap hd hnu0 hnu1
        (hcap _ (fiber_endpoint_start_pos p))
      simpa only [fiberEndpointDifference, fiberEndpointRaw, fiber_endpoint_start_lambda,
        shared_G_zero, mul_zero, sub_zero, sub_nonneg] using hscaled
    have hf : ContinuousOn (fiberEndpointDifference p d R nu A c)
        (Icc tau (fiberEndpointStart p)) := by
      intro x hx
      exact (fiber_hasDerivAt_endpoint_difference (lt_of_lt_of_le htau hx.1)).continuousAt.continuousWithinAt
    have hmin := fiber_endpoint_minimum_of_convex_weighted_derivative ⟨httau, hts⟩ hf
      (fiber_endpoint_K_convex htau hR hnu0) (fiber_endpoint_K_terminal hnu0 hstar)
      (fun x hx => fiber_hasDerivAt_endpoint_difference (htau.trans hx.1))
    have hnonneg := (le_min hDa hDb).trans hmin
    rw [fiber_endpoint_upper_raw ht hts]
    exact sub_nonneg.mp hnonneg
  · rw [fiber_endpoint_upper_constant (le_of_lt (lt_of_not_ge hts))]
    exact fiber_endpoint_scaled_cap hd hnu0 hnu1 (hcap _ ht)

theorem fiber_endpoint_principle {p R d eta A c tau : ℝ}
    (_hp : 0 < p) (hR : 0 < R) (hd : 0 ≤ d) (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (_hA : 0 < A) (hc : 0 < c) (htau : 0 < tau)
    (hstar : fiberEndpointStart p ^ 2 ≤ 2 * c / 9)
    (hcap : sSup ((fiberEndpointTarget A c) '' Ioi 0) ≤ 1 + d)
    (hstart : max (fiberEndpointTarget A c tau) (eta * fiberEndpointTarget A c tau) ≤
      fiberEndpointUpper p d R tau) :
    ∀ t, tau ≤ t → max (fiberEndpointTarget A c t) (eta * fiberEndpointTarget A c t) ≤
      fiberEndpointUpper p d R t := by
  have hbounded : BddAbove ((fiberEndpointTarget A c) '' Ioi 0) := by
    refine ⟨A, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht0 : 0 < t := ht
    have hdiv : 0 ≤ c / t := div_nonneg hc.le ht.le
    unfold fiberEndpointTarget
    linarith
  have hall : ∀ t, 0 < t → fiberEndpointTarget A c t ≤ 1 + d := by
    intro t ht
    exact (le_csSup hbounded ⟨t, ht, rfl⟩).trans hcap
  intro t ht
  have h1 := fiber_endpoint_single_target hR hd (by norm_num : (0 : ℝ) ≤ 1)
    (le_refl (1 : ℝ)) htau ht hstar hall (by simpa using (le_max_left _ _).trans hstart)
  have he := fiber_endpoint_single_target hR hd heta0.le heta1 htau ht hstar hall
    ((le_max_right _ _).trans hstart)
  simpa only [one_mul] using max_le h1 he

end Erdos993Lean.Analytic.V213
