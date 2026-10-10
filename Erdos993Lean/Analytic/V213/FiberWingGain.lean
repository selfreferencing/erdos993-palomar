module

public import Erdos993Lean.Analytic.V213.FiberUniformGain

/-!
The literal Eq86 gain estimate and its improved small-skew
coefficient. These are real analytic consequences of the accepted Eq79,
on every N>=13 and 0<a<=r<=b<=1/5; no finite family is consumed.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real

noncomputable def fiberWingA (b : ℝ) : ℝ :=
  (1 - b ^ 2 / (3 * (1 - b ^ 2))) ^ 2 / 2 - b ^ 2 / (12 * (1 - b ^ 2) ^ 2)
noncomputable def fiberWingK (b : ℝ) : ℝ :=
  4 * (1 - b ^ 2 / (3 * (1 - b ^ 2))) + 13 / (72 * (1 - b ^ 2))

theorem fiber_wing_coefficients {b : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 1 / 5) :
    10007 / 20736 ≤ fiberWingA b ∧ 12 / 25 < fiberWingA b ∧ fiberWingK b < 21 / 5 := by
  have hbs : b ^ 2 ≤ 1 / 25 := by nlinarith
  have hab : 24 / 25 ≤ 1 - b ^ 2 := by linarith
  have ha : 0 < 1 - b ^ 2 := by linarith
  have hp : 71 / 72 ≤ 1 - b ^ 2 / (3 * (1 - b ^ 2)) := by
    have h : b ^ 2 / (3 * (1 - b ^ 2)) ≤ (1 / 72 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - b ^ 2))).2
      nlinarith only [hbs]
    linarith only [h]
  have hp1 : 1 - b ^ 2 / (3 * (1 - b ^ 2)) ≤ 1 := by
    have h : 0 ≤ b ^ 2 / (3 * (1 - b ^ 2)) := by positivity
    linarith only [h]
  have hsq : (71 / 72 : ℝ) ^ 2 ≤ (1 - b ^ 2 / (3 * (1 - b ^ 2))) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ 1 - b ^ 2 / (3 * (1 - b ^ 2)))).2 hp
  have haloss : b ^ 2 / (12 * (1 - b ^ 2) ^ 2) ≤ (25 / 6912 : ℝ) := by
    have habsq : (24 / 25 : ℝ) ^ 2 ≤ (1 - b ^ 2) ^ 2 :=
      (sq_le_sq₀ (by norm_num) ha.le).2 hab
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - b ^ 2) ^ 2)).2
    nlinarith only [hbs, habsq]
  have hkinv : 13 / (72 * (1 - b ^ 2)) ≤ (325 / 1728 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 72 * (1 - b ^ 2))).2
    linarith only [hab]
  have hA : 10007 / 20736 ≤ fiberWingA b := by
    unfold fiberWingA
    linarith only [hsq, haloss]
  refine ⟨hA, ?_, ?_⟩
  · linarith only [hA]
  · unfold fiberWingK
    linarith only [hp1, hkinv]

theorem fiber_wing_coefficients_improved {b : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ 3 / 25) :
    199 / 200 ≤ 1 - b ^ 2 / (3 * (1 - b ^ 2)) ∧
    b ^ 2 / (12 * (1 - b ^ 2) ^ 2) < 1 / 800 ∧ 79 / 160 < fiberWingA b := by
  have hbs : b ^ 2 ≤ 9 / 625 := by nlinarith
  have hab : 616 / 625 ≤ 1 - b ^ 2 := by linarith
  have ha : 0 < 1 - b ^ 2 := by linarith
  have hp : 199 / 200 ≤ 1 - b ^ 2 / (3 * (1 - b ^ 2)) := by
    have h : b ^ 2 / (3 * (1 - b ^ 2)) ≤ (1 / 200 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - b ^ 2))).2
      nlinarith only [hbs]
    linarith only [h]
  have haloss : b ^ 2 / (12 * (1 - b ^ 2) ^ 2) < (1 / 800 : ℝ) := by
    have habsq : (616 / 625 : ℝ) ^ 2 ≤ (1 - b ^ 2) ^ 2 :=
      (sq_le_sq₀ (by norm_num) ha.le).2 hab
    apply (div_lt_iff₀ (by positivity : 0 < 12 * (1 - b ^ 2) ^ 2)).2
    nlinarith only [hbs, habsq]
  have hsq : (199 / 200 : ℝ) ^ 2 ≤ (1 - b ^ 2 / (3 * (1 - b ^ 2))) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ 1 - b ^ 2 / (3 * (1 - b ^ 2)))).2 hp
  refine ⟨hp, haloss, ?_⟩
  unfold fiberWingA
  linarith only [hsq, haloss]

theorem fiber_wing_gain_expansion {N a r b : ℝ} (hN : 13 ≤ N)
    (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (hbh : b ≤ 1 / 5) :
    a ^ 2 * fiberWingA b * (N + 1) + (37 / 15 + 8 * a ^ 2) / (N + 1) -
      a ^ 2 * fiberWingK b ≤ V22.phiR r N := by
  have hb : 0 ≤ b := (ha.le.trans har).trans hrb
  have hm : 0 < N + 1 := by linarith
  have ht : 0 < N - 1 := by linarith
  have hab : 0 < 1 - b ^ 2 := by nlinarith
  have hD : 37 / (15 * (N + 1)) ≤ fiberGainD (N + 1) := by
    have hx : 1 / (N - 1) ≤ (1 / 12 : ℝ) := by
      apply (div_le_iff₀ ht).2
      linarith only [hN]
    have he : fiberGainD (N + 1) = (51 / 20 - 1 / (N - 1)) / (N + 1) := by
      unfold fiberGainD
      rw [show N + 1 - 2 = N - 1 by ring]
      field_simp [hm.ne', ht.ne']
      ring
    rw [he]
    apply (le_div_iff₀ hm).2
    have hc : 37 / (15 * (N + 1)) * (N + 1) = (37 / 15 : ℝ) := by
      field_simp [hm.ne']
    rw [hc]
    linarith only [hx]
  have hratio : N / (N - 1) ≤ (13 / 12 : ℝ) := by
    apply (div_le_iff₀ ht).2
    linarith only [hN]
  have hterm : N / (6 * (1 - b ^ 2) * (N - 1)) ≤ 13 / (72 * (1 - b ^ 2)) := by
    have h := div_le_div_of_nonneg_right hratio (by positivity : 0 ≤ 6 * (1 - b ^ 2))
    convert h using 1 <;> field_simp [hab.ne', ht.ne'] <;> ring
  have hCe : fiberGainC b (N + 1) = fiberWingA b * (N + 1) +
      8 / (N + 1) - 4 * (1 - b ^ 2 / (3 * (1 - b ^ 2))) -
      N / (6 * (1 - b ^ 2) * (N - 1)) := by
    unfold fiberGainC fiberWingA
    rw [show N + 1 - 2 = N - 1 by ring]
    field_simp [hm.ne', ht.ne', hab.ne']
    ring
  have hC : fiberWingA b * (N + 1) + 8 / (N + 1) - fiberWingK b ≤ fiberGainC b (N + 1) := by
    rw [hCe]
    unfold fiberWingK
    linarith only [hterm]
  have hC0 : 0 ≤ fiberGainC b (N + 1) :=
    (by norm_num : (0 : ℝ) ≤ 769 / 891).trans
      ((fiber_gain_C_half_lower (by linarith)).trans
        (fiber_gain_C_lower hb (by linarith : b ≤ 1 / 2) (by linarith)))
  have hsq : a ^ 2 ≤ r ^ 2 := (sq_le_sq₀ ha.le (ha.le.trans har)).2 har
  have hCr := mul_le_mul_of_nonneg_right hsq hC0
  have hCa := mul_le_mul_of_nonneg_left hC (sq_nonneg a)
  have hp := fiber_uniform_phi_lower (by linarith : 10 ≤ N) (ha.le.trans har) hrb
    (by linarith : b ≤ 1 / 2)
  have he : a ^ 2 * fiberWingA b * (N + 1) + (37 / 15 + 8 * a ^ 2) / (N + 1) -
      a ^ 2 * fiberWingK b = 37 / (15 * (N + 1)) +
      a ^ 2 * (fiberWingA b * (N + 1) + 8 / (N + 1) - fiberWingK b) := by
    field_simp [hm.ne'] <;> ring
  rw [he]
  linarith only [hD, hCa, hCr, hp]

theorem fiber_wing_amgm {alpha c k a m : ℝ} (halpha : 0 < alpha) (hm : 0 < m)
    (hac : k ^ 2 ≤ alpha * c) :
    2 * k * a ≤ alpha * a ^ 2 * m + c / m := by
  have hd : (alpha * a ^ 2 * m ^ 2 + c) / m = alpha * a ^ 2 * m + c / m := by
    field_simp [hm.ne'] <;> ring
  rw [← hd]
  apply (le_div_iff₀ hm).2
  have hp := sq_nonneg (alpha * a * m - k)
  have he : (alpha * a * m - k) ^ 2 + (alpha * c - k ^ 2) =
      alpha * (alpha * a ^ 2 * m ^ 2 + c - 2 * k * a * m) := by ring
  have hx : 0 ≤ alpha * (alpha * a ^ 2 * m ^ 2 + c - 2 * k * a * m) := by
    rw [← he]
    linarith only [hp, hac]
  have hy : 2 * k * a * m ≤ alpha * a ^ 2 * m ^ 2 + c := by
    nlinarith only [hx, halpha]
  exact hy

theorem fiber_wing_gain_uniform {N a r b : ℝ} (hN : 13 ≤ N) (ha : 0 < a)
    (har : a ≤ r) (hrb : r ≤ b) (hbh : b ≤ 1 / 5) :
    54 * a / 25 - 21 * a ^ 2 / 5 ≤ V22.phiR r N := by
  have hb : 0 ≤ b := (ha.le.trans har).trans hrb
  have hc := fiber_wing_coefficients hb hbh
  have he := fiber_wing_gain_expansion hN ha har hrb hbh
  have hm : 0 < N + 1 := by linarith
  have h1 := mul_le_mul_of_nonneg_right hc.2.1.le (by positivity : 0 ≤ a ^ 2 * (N + 1))
  have h2 : (37 / 15 : ℝ) / (N + 1) ≤ (37 / 15 + 8 * a ^ 2) / (N + 1) :=
    div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg a]) hm.le
  have h3 := mul_le_mul_of_nonneg_left hc.2.2.le (sq_nonneg a)
  have ham := fiber_wing_amgm (a := a) (m := N + 1)
    (by norm_num : (0 : ℝ) < 12 / 25) hm
    (by norm_num : (27 / 25 : ℝ) ^ 2 ≤ (12 / 25) * (37 / 15))
  nlinarith only [he, h1, h2, h3, ham]

theorem fiber_wing_gain_improved {N a r b : ℝ} (hN : 13 ≤ N) (ha : 1 / 20 ≤ a)
    (har : a ≤ r) (hrb : r ≤ b) (hbh : b ≤ 3 / 25) :
    221 * a / 100 - 21 * a ^ 2 / 5 ≤ V22.phiR r N := by
  have ha0 : 0 < a := by linarith
  have hb : 0 ≤ b := (ha0.le.trans har).trans hrb
  have hc := fiber_wing_coefficients hb (by linarith : b ≤ 1 / 5)
  have hi := fiber_wing_coefficients_improved hb hbh
  have he := fiber_wing_gain_expansion hN ha0 har hrb (by linarith : b ≤ 1 / 5)
  have hm : 0 < N + 1 := by linarith
  have h1 := mul_le_mul_of_nonneg_right hi.2.2.le (by positivity : 0 ≤ a ^ 2 * (N + 1))
  have h2 : (373 / 150 : ℝ) / (N + 1) ≤ (37 / 15 + 8 * a ^ 2) / (N + 1) :=
    div_le_div_of_nonneg_right (by nlinarith only [ha]) hm.le
  have h3 := mul_le_mul_of_nonneg_left hc.2.2.le (sq_nonneg a)
  have ham := fiber_wing_amgm (a := a) (m := N + 1)
    (by norm_num : (0 : ℝ) < 79 / 160) hm
    (by norm_num : (221 / 200 : ℝ) ^ 2 ≤ (79 / 160) * (373 / 150))
  nlinarith only [he, h1, h2, h3, ham]

end Erdos993Lean.Analytic.V213
