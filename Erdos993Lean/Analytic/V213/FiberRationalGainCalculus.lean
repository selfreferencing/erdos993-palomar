module

public import Erdos993Lean.Analytic.V213.FiberRationalGainDefinitions

/-!
Actual differentiation of Eq100 and its full-domain Eq101 lower bound.
The reciprocal normal form is used only on N>1, where both original width
denominators are nonzero. No monotonicity of the exact Phi is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_rational_gain_reciprocal_form {a b N : ℝ} (hN : 1 < N) :
    fiberRationalGain a b N =
      a ^ 2 * ((N + 1) * fiberRationalA b - 4 + 8 / (N + 1)) +
        (71 / 20) / (N + 1) - (1 / 2) / (N + 1) - (1 / 2) / (N - 1) -
          (b ^ 2 / (6 * (1 - b ^ 2))) * (1 + 1 / (N - 1)) +
            4 * a ^ 4 / 3 + (N + 1) * (a ^ 6 / 18) := by
  have hp : N + 1 ≠ 0 := ne_of_gt (by linarith : 0 < N + 1)
  have hm : N - 1 ≠ 0 := ne_of_gt (by linarith : 0 < N - 1)
  unfold fiberRationalGain
  dsimp only
  have he : N + 1 - 2 = N - 1 := by ring
  rw [he]
  field_simp [hp,hm] <;> ring

theorem fiber_hasDerivAt_rational_gain {a b N : ℝ} (hN : 1 < N) :
    HasDerivAt (fiberRationalGain a b) (fiberRationalGainPrime a b N) N := by
  have hp : N + 1 ≠ 0 := ne_of_gt (by linarith : 0 < N + 1)
  have hm : N - 1 ≠ 0 := ne_of_gt (by linarith : 0 < N - 1)
  have dm := (hasDerivAt_id N).add_const 1
  have dn := (hasDerivAt_id N).sub_const 1
  have h8 := (hasDerivAt_const N (8 : ℝ)).div dm hp
  have hmain := (((dm.const_mul (fiberRationalA b)).sub_const 4).add h8).const_mul (a ^ 2)
  have h71 := (hasDerivAt_const N (71 / 20 : ℝ)).div dm hp
  have hhalf1 := (hasDerivAt_const N (1 / 2 : ℝ)).div dm hp
  have hhalf2 := (hasDerivAt_const N (1 / 2 : ℝ)).div dn hm
  have hb := (((hasDerivAt_const N (1 : ℝ)).div dn hm).const_add 1).const_mul
    (b ^ 2 / (6 * (1 - b ^ 2)))
  have hlast := dm.const_mul (a ^ 6 / 18)
  have h := (((((hmain.add h71).sub hhalf1).sub hhalf2).sub hb).add_const
    (4 * a ^ 4 / 3)).add hlast
  have he : HasDerivAt (fun x : ℝ =>
      a ^ 2 * ((x + 1) * fiberRationalA b - 4 + 8 / (x + 1)) +
        (71 / 20) / (x + 1) - (1 / 2) / (x + 1) - (1 / 2) / (x - 1) -
          (b ^ 2 / (6 * (1 - b ^ 2))) * (1 + 1 / (x - 1)) +
            4 * a ^ 4 / 3 + (x + 1) * (a ^ 6 / 18)) (fiberRationalGainPrime a b N) N := by
    convert h using 1
    · funext x
      dsimp
      ring
    · dsimp [fiberRationalGainPrime]
      have he : N + 1 - 2 = N - 1 := by ring
      rw [he]
      field_simp [hp,hm] <;> ring
  apply he.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hN] with x hx
  exact fiber_rational_gain_reciprocal_form hx

theorem fiber_rational_gain_derivative_lower {a b N : ℝ} (ha : 23 / 100 ≤ a)
    (hab : a ≤ b) (hbh : b ≤ 1 / 2) (hN : 14 ≤ N) :
    12883 / 13500000 ≤ fiberRationalGainPrime a b N := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := ha0.trans hab
  have hA := fiber_rational_A_lower hb0 hbh
  have hm : 15 ≤ N + 1 := by linarith
  have hm0 : 0 < N + 1 := by linarith
  have hm2 : 0 < N + 1 - 2 := by linarith
  have ho0 : 0 < 1 - b ^ 2 := by nlinarith
  have h8 : 8 / (N + 1) ^ 2 ≤ (8 / 225 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < (N + 1) ^ 2)).2
    nlinarith only [hm]
  have h71 : 71 / (20 * (N + 1) ^ 2) ≤ (71 / 4500 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 20 * (N + 1) ^ 2)).2
    nlinarith only [hm]
  have ha2 : (23 / 100 : ℝ) ^ 2 ≤ a ^ 2 :=
    (sq_le_sq₀ (by norm_num) ha0).2 ha
  have hcoef : 19 / 54 - 8 / 225 ≤ fiberRationalA b - 8 / (N + 1) ^ 2 := by
    linarith only [hA,h8]
  have hmul := mul_le_mul ha2 hcoef (by norm_num : (0 : ℝ) ≤ 19 / 54 - 8 / 225)
    (sq_nonneg a)
  have h1 : 0 ≤ 1 / (2 * (N + 1) ^ 2) := by positivity
  have h2 : 0 ≤ 1 / (2 * (N + 1 - 2) ^ 2) := by positivity
  have h3 : 0 ≤ b ^ 2 / (6 * (1 - b ^ 2) * (N + 1 - 2) ^ 2) := by positivity
  have h6 : 0 ≤ a ^ 6 / 18 := by positivity
  unfold fiberRationalGainPrime
  dsimp only
  linarith only [hmul,h71,h1,h2,h3,h6]

theorem fiber_rational_gain_derivative_positive {a b N : ℝ} (ha : 23 / 100 ≤ a)
    (hab : a ≤ b) (hbh : b ≤ 1 / 2) (hN : 14 ≤ N) :
    0 < fiberRationalGainPrime a b N := by
  have h := fiber_rational_gain_derivative_lower ha hab hbh hN
  linarith

theorem fiber_rational_gain_increases {a b : ℝ} (ha : 23 / 100 ≤ a)
    (hab : a ≤ b) (hbh : b ≤ 1 / 2) :
    StrictMonoOn (fiberRationalGain a b) (Ici (14 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fiberRationalGainPrime a b) (convex_Ici _)
  · intro N hN
    change 14 ≤ N at hN
    exact (fiber_hasDerivAt_rational_gain (by linarith [hN] : 1 < N)).continuousAt.continuousWithinAt
  · intro N hN
    have h : 14 < N := by simpa only [interior_Ici,mem_Ioi] using hN
    exact (fiber_hasDerivAt_rational_gain (by linarith : 1 < N)).hasDerivWithinAt
  · intro N hN
    have h : 14 < N := by simpa only [interior_Ici,mem_Ioi] using hN
    exact fiber_rational_gain_derivative_positive ha hab hbh h.le

end Erdos993Lean.Analytic.V213
