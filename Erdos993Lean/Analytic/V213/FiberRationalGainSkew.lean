module

public import Erdos993Lean.Analytic.V213.FiberRationalGainDefinitions
public import Erdos993Lean.Analytic.V22.Analysis.SkewBounds

/-!
C118's skew controls: both artanh-error bounds and the unfavorable-direction
comparison in Eq100. All parameters remain real, including the closed upper
skew endpoint 1/2. No sampled or generated scalar family is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_ahat_cubic_lower {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r ^ 3 / 3 ≤ V22.aHat r := by
  let f : ℝ → ℝ := fun x => V22.aHat x - x ^ 3 / 3
  have hd : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt f (x ^ 4 / (1 - x ^ 2)) x := by
    intro x hx
    have ho := shared_one_sub_sq_pos (by linarith [hx.1] : -1 < x) (by linarith [hx.2] : x < 1)
    convert (hasDerivAt_sharedAHat (by linarith [hx.1]) (by linarith [hx.2])).sub
      ((hasDerivAt_pow 3 x).div_const 3) using 1
    all_goals field_simp [ho.ne'] <;> ring
  have hm : MonotoneOn f (Icc (0 : ℝ) r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) r := interior_subset hx
        exact div_nonneg (pow_nonneg hx'.1 4)
          (shared_one_sub_sq_pos (by linarith [hx'.1]) (by linarith [hx'.2])).le)
  have h := hm ⟨le_rfl,hr0⟩ ⟨hr0,le_rfl⟩ hr0
  have hf0 : f 0 = 0 := by simp [f,V22.aHat,sharedArtanh_zero]
  rw [hf0] at h
  dsimp only [f] at h
  linarith

theorem fiber_rational_skew_fraction {r b : ℝ} (hr0 : 0 ≤ r)
    (hrb : r ≤ b) (hbh : b ≤ 1 / 2) :
    r ^ 2 / (1 - r ^ 2) ≤ b ^ 2 / (1 - b ^ 2) := by
  have hb0 : 0 ≤ b := hr0.trans hrb
  have hor : 0 < 1 - r ^ 2 := by nlinarith
  have hob : 0 < 1 - b ^ 2 := by nlinarith
  apply (div_le_div_iff₀ hor hob).2
  nlinarith

theorem fiber_rational_A_antitone {r b : ℝ} (hr0 : 0 ≤ r)
    (hrb : r ≤ b) (hbh : b ≤ 1 / 2) :
    fiberRationalA b ≤ fiberRationalA r := by
  have hb0 : 0 ≤ b := hr0.trans hrb
  have hor : 0 < 1 - r ^ 2 := by nlinarith
  have hob : 0 < 1 - b ^ 2 := by nlinarith
  have hf := fiber_rational_skew_fraction hr0 hrb hbh
  have h1 := div_le_div_of_nonneg_right hf (by norm_num : (0 : ℝ) ≤ 3)
  have hf0 : 0 ≤ r ^ 2 / (1 - r ^ 2) := by positivity
  have h2a := div_le_div_of_nonneg_left hf0 hob (by nlinarith : 1 - b ^ 2 ≤ 1 - r ^ 2)
  have h2b := div_le_div_of_nonneg_right hf hob.le
  have h2 := div_le_div_of_nonneg_right (h2a.trans h2b) (by norm_num : (0 : ℝ) ≤ 12)
  have he1 : ∀ x : ℝ, (x ^ 2 / (1 - x ^ 2)) / 3 = x ^ 2 / (3 * (1 - x ^ 2)) := by
    intro x
    rw [div_div]
    congr 1
    ring
  have he2 : ∀ x : ℝ, ((x ^ 2 / (1 - x ^ 2)) / (1 - x ^ 2)) / 12 =
      x ^ 2 / (12 * (1 - x ^ 2) ^ 2) := by
    intro x
    rw [div_div,div_div]
    congr 1
    ring
  rw [he1 r,he1 b] at h1
  rw [he2 r,he2 b] at h2
  unfold fiberRationalA
  linarith

theorem fiber_rational_gain_skew_lower {a r b N : ℝ} (ha0 : 0 ≤ a)
    (har : a ≤ r) (hrb : r ≤ b) (hbh : b ≤ 1 / 2) (hN : 10 ≤ N) :
    fiberRationalGain a b N ≤ fiberRationalGain r r N := by
  have hr0 : 0 ≤ r := ha0.trans har
  have hb0 : 0 ≤ b := hr0.trans hrb
  have hm0 : 0 < N + 1 := by linarith
  have hm2 : 0 < N + 1 - 2 := by linarith
  have hob : 0 < 1 - b ^ 2 := by nlinarith
  have har2 : a ^ 2 ≤ r ^ 2 := (sq_le_sq₀ ha0 hr0).2 har
  have hA := fiber_rational_A_antitone hr0 hrb hbh
  have hmainb := fiber_rational_main_positive hb0 hbh (by linarith : 11 ≤ N + 1)
  have hmain : (N + 1) * fiberRationalA b - 4 + 8 / (N + 1) ≤
      (N + 1) * fiberRationalA r - 4 + 8 / (N + 1) := by
    nlinarith only [mul_le_mul_of_nonneg_left hA hm0.le]
  have hmul := mul_le_mul har2 hmain hmainb.le (sq_nonneg r)
  have hfrac := fiber_rational_skew_fraction hr0 hrb hbh
  have hcoef : 0 ≤ (N + 1 - 1) / (6 * (N + 1 - 2)) := by
    apply div_nonneg <;> linarith
  have hneg := mul_le_mul_of_nonneg_right hfrac hcoef
  have he : ∀ x : ℝ, (x ^ 2 / (1 - x ^ 2)) * ((N + 1 - 1) / (6 * (N + 1 - 2))) =
      x ^ 2 * (N + 1 - 1) / (6 * (1 - x ^ 2) * (N + 1 - 2)) := by
    intro x
    rw [div_mul_div_comm]
    congr 1
    ring
  rw [he r,he b] at hneg
  have h4 := pow_le_pow_left₀ ha0 har 4
  have h6 := pow_le_pow_left₀ ha0 har 6
  have hquart := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hsext := mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ (N + 1) / 18)
  unfold fiberRationalGain
  dsimp only
  linarith only [hmul,hneg,hquart,hsext]

end Erdos993Lean.Analytic.V213
