module

public import Erdos993Lean.Analytic.V213.FiberUniformGain
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Lemma6.10's frozen positive-activity gain is strictly increasing
whenever m*a>=18/5. All derivatives belong to the literal D_* and C_b
definitions; the start and equality cases remain in the closed domain.
No generated DF10 family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberGainSlope (b : ℝ) : ℝ :=
  (1 - b ^ 2 / (3 * (1 - b ^ 2))) ^ 2 / 2 - b ^ 2 / (12 * (1 - b ^ 2) ^ 2)

theorem fiber_gain_slope_lower {b : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2) :
    (29 / 81 : ℝ) ≤ fiberGainSlope b := by
  have ha : 3 / 4 ≤ 1 - b ^ 2 := by nlinarith
  have ha0 : 0 < 1 - b ^ 2 := by linarith
  have hp : 8 / 9 ≤ 1 - b ^ 2 / (3 * (1 - b ^ 2)) := by
    have hx : b ^ 2 / (3 * (1 - b ^ 2)) ≤ (1 / 9 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - b ^ 2))).2
      nlinarith
    linarith
  have hs : (8 / 9 : ℝ) ^ 2 ≤ (1 - b ^ 2 / (3 * (1 - b ^ 2))) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith)).2 hp
  have hc : b ^ 2 / (12 * (1 - b ^ 2) ^ 2) ≤ (1 / 27 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - b ^ 2) ^ 2)).2
    have ha2 : (3 / 4 : ℝ) ^ 2 ≤ (1 - b ^ 2) ^ 2 :=
      (sq_le_sq₀ (by norm_num) ha0.le).2 ha
    nlinarith
  unfold fiberGainSlope
  linarith

theorem fiber_hasDerivAt_gain_D {m : ℝ} (hm : 2 < m) :
    HasDerivAt fiberGainD (-61 / (20 * m ^ 2) + 1 / (2 * (m - 2) ^ 2)) m := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have h1 := ((hasDerivAt_id m).const_mul 20)
  have h2 := (((hasDerivAt_id m).sub_const 2).const_mul 2)
  have h := ((hasDerivAt_const m (61 : ℝ)).div h1 (by positivity)).sub
    ((hasDerivAt_const m (1 : ℝ)).div h2 (by positivity))
  convert h using 1
  · funext x
    rfl
  · dsimp
    field_simp [hm0.ne', hm2.ne'] <;> ring

theorem fiber_hasDerivAt_gain_C {b m : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hm : 2 < m) :
    HasDerivAt (fiberGainC b)
      (fiberGainSlope b - 8 / m ^ 2 + 1 / (6 * (1 - b ^ 2) * (m - 2) ^ 2)) m := by
  have ha0 : 0 < 1 - b ^ 2 := by nlinarith
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have h1 := ((((hasDerivAt_id m).const_mul
    (1 - b ^ 2 / (3 * (1 - b ^ 2)))).sub_const 4).pow 2).div
      ((hasDerivAt_id m).const_mul 2) (by positivity)
  have h2 := ((hasDerivAt_id m).sub_const 1).div
    (((hasDerivAt_id m).sub_const 2).const_mul (6 * (1 - b ^ 2))) (by positivity)
  have h3 := ((hasDerivAt_id m).const_mul (b ^ 2)).div_const (12 * (1 - b ^ 2) ^ 2)
  have h := (h1.sub h2).sub h3
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberGainSlope]
    field_simp [ha0.ne', hm0.ne', hm2.ne'] <;> ring

theorem fiber_gain_frozen_hasDerivAt {a b m : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 2)
    (hm : 2 < m) :
    HasDerivAt (fun x => fiberGainD x + a ^ 2 * fiberGainC b x)
      (-61 / (20 * m ^ 2) + 1 / (2 * (m - 2) ^ 2) +
        a ^ 2 * (fiberGainSlope b - 8 / m ^ 2 +
          1 / (6 * (1 - b ^ 2) * (m - 2) ^ 2))) m :=
  (fiber_hasDerivAt_gain_D hm).add ((fiber_hasDerivAt_gain_C hb0 hbh hm).const_mul (a ^ 2))

theorem fiber_gain_frozen_derivative_lower {a b m : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbh : b ≤ 1 / 2) (hm : 11 ≤ m)
    (hma : 18 / 5 ≤ m * a) :
    9 / (100 * m ^ 2) ≤ deriv (fun x => fiberGainD x + a ^ 2 * fiberGainC b x) m := by
  have hb0 := ha.le.trans hab
  have ha0 : 0 < 1 - b ^ 2 := by nlinarith
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hmSq : 0 < m ^ 2 := by positivity
  rw [(fiber_gain_frozen_hasDerivAt hb0 hbh (by linarith : 2 < m)).deriv]
  have hDextra : 1 / (2 * m ^ 2) ≤ 1 / (2 * (m - 2) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hD : -(51 / 20 : ℝ) ≤ m ^ 2 *
      (-61 / (20 * m ^ 2) + 1 / (2 * (m - 2) ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hDextra hmSq.le
    have he : m ^ 2 * (1 / (2 * m ^ 2)) = (1 / 2 : ℝ) := by
      field_simp [hmSq.ne']
    have he' : m ^ 2 * (-61 / (20 * m ^ 2)) = -(61 / 20 : ℝ) := by
      field_simp [hmSq.ne']
    rw [he] at h
    rw [mul_add, he']
    linarith
  have hC : 29 / 81 * m ^ 2 - 8 ≤ m ^ 2 *
      (fiberGainSlope b - 8 / m ^ 2 + 1 / (6 * (1 - b ^ 2) * (m - 2) ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left (fiber_gain_slope_lower hb0 hbh) hmSq.le
    have hp : 0 ≤ 1 / (6 * (1 - b ^ 2) * (m - 2) ^ 2) := by positivity
    have he : m ^ 2 * (8 / m ^ 2) = (8 : ℝ) := by field_simp [hmSq.ne']
    have hpe := mul_nonneg hmSq.le hp
    rw [mul_add, mul_sub, he]
    linarith
  have hCa := mul_le_mul_of_nonneg_left hC (sq_nonneg a)
  have hmasq : (324 / 25 : ℝ) ≤ m ^ 2 * a ^ 2 := by
    have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 18 / 5) (by positivity : 0 ≤ m * a)).2 hma
    nlinarith
  have ha2 : a ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 100 * m ^ 2)).2
  nlinarith

theorem fiber_gain_frozen_strictMono {a b m0 : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbh : b ≤ 1 / 2)
    (hm0 : 11 ≤ m0) (hma : 18 / 5 ≤ m0 * a) :
    StrictMonoOn (fun m => fiberGainD m + a ^ 2 * fiberGainC b m) (Ici m0) := by
  have hcont : ContinuousOn (fun m => fiberGainD m + a ^ 2 * fiberGainC b m) (Ici m0) := by
    intro m hm
    change m0 ≤ m at hm
    exact (fiber_gain_frozen_hasDerivAt (ha.le.trans hab) hbh
      (by linarith [hm] : 2 < m)).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Ici m0) hcont
  intro m hm
  have hm' : m0 < m := by simpa only [interior_Ici, mem_Ioi] using hm
  have hmpos : 0 < m := by linarith
  have hma' : 18 / 5 ≤ m * a := hma.trans
    (mul_le_mul_of_nonneg_right hm'.le ha.le)
  exact lt_of_lt_of_le (by positivity)
    (fiber_gain_frozen_derivative_lower ha hab hbh (hm0.trans hm'.le) hma')

end Erdos993Lean.Analytic.V213
