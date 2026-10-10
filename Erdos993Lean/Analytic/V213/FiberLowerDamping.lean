module

public import Erdos993Lean.Analytic.V213.FiberMassLinearization

/-!
Eq81: the exact lower-offset damping inequality on the whole
real N>=14 domain. A direct square completion proves the small-ratio case;
no finite family or unproved source theorem is a premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

noncomputable def fiberLowerH (N : ℝ) : ℝ := N - 1 + 1 / N

theorem fiber_lower_H_pos {N : ℝ} (hN : 14 ≤ N) : 0 < fiberLowerH N := by
  have hN0 : 0 < N := by linarith
  unfold fiberLowerH
  have hi : 0 < 1 / N := by positivity
  linarith

theorem fiber_lower_sqrt_ratio {N : ℝ} (hN : 14 ≤ N) :
    Real.sqrt N ≤ (N + 1) / 4 := by
  have hN0 : 0 ≤ N := by linarith
  have hp : 0 ≤ N * (N - 14) := mul_nonneg hN0 (by linarith)
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith

theorem fiber_lower_damping_square {N w xi : ℝ} (hN : 14 ≤ N)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hxi0 : 0 ≤ xi) (hxisq : xi ^ 2 ≤ 1 / 3) :
    (1 - w) * Real.exp (-1 / (N + 1) ^ 2) ≤
      (1 - w + fiberLowerH N * xi ^ 2) *
        Real.exp (-(2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1)) := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have hH := fiber_lower_H_pos hN
  have ha : 0 ≤ 1 - w := by linarith
  have hs0 : 0 ≤ Real.sqrt (N * w) := Real.sqrt_nonneg _
  have hsSq : Real.sqrt (N * w) ^ 2 = N * w := Real.sq_sqrt (mul_nonneg hn.le hw0)
  by_cases hazero : 1 - w = 0
  · rw [hazero, zero_mul, zero_add]
    positivity
  have ha0 : 0 < 1 - w := lt_of_le_of_ne ha (Ne.symm hazero)
  let k : ℝ := fiberLowerH N * xi ^ 2 / (1 - w)
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hkpos : 0 < 1 + k := by linarith
  have hlog : -(1 / (N + 1) ^ 2) ≤
      Real.log (1 + k) - (2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1) := by
    by_cases hk1 : 1 ≤ k
    · have hl := (Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).trans
        (Real.log_le_log (by norm_num : (0 : ℝ) < 1 + 1) (by linarith : (1 : ℝ) + 1 ≤ 1 + k))
      norm_num at hl
      have hxih : xi ≤ (3 / 5 : ℝ) := by nlinarith
      have hs := (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hw1 hn.le)).trans
        (by simpa only [mul_one] using fiber_lower_sqrt_ratio hN)
      have hsxi := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hxi0)
      have hE : (2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1) ≤ (31 / 90 : ℝ) := by
        apply (div_le_iff₀ hm).2
        have hh : 2 * xi * ((N + 1) / 4) ≤ 3 / 10 * (N + 1) := by
          have hx := mul_le_mul_of_nonneg_right hxih hm.le
          nlinarith
        nlinarith
      have hp : 0 < 1 / (N + 1) ^ 2 := by positivity
      linarith
    · have hk1' : k ≤ 1 := le_of_lt (lt_of_not_ge hk1)
      have hlower := Real.le_log_one_add_of_nonneg hk0
      have hhalf : k / 2 ≤ 2 * k / (k + 2) := by
        apply (le_div_iff₀ (by linarith : 0 < k + 2)).2
        nlinarith
      have hl := hhalf.trans hlower
      have haw : 4 * (1 - w) * w ≤ (1 : ℝ) := by nlinarith [sq_nonneg (2 * w - 1)]
      have hK : N * w ≤ fiberLowerH N / (2 * (1 - w)) - 2 / (N + 1) := by
        apply (le_sub_iff_add_le).2
        apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - w))).2
        have hdiv : 4 * (1 - w) / (N + 1) ≤ (4 / 15 : ℝ) := by
          apply (div_le_iff₀ hm).2
          nlinarith
        have hterm : 2 * (1 - w) * N * w ≤ N / 2 := by
          have hh := mul_le_mul_of_nonneg_left haw hn.le
          nlinarith
        unfold fiberLowerH
        have hinv : 0 ≤ 1 / N := by positivity
        have he : (N * w + 2 / (N + 1)) * (2 * (1 - w)) =
            2 * (1 - w) * N * w + 4 * (1 - w) / (N + 1) := by ring
        rw [he]
        linarith
      have hKxi := mul_le_mul_of_nonneg_right hK (sq_nonneg xi)
      have hsquare := sq_nonneg (Real.sqrt (N * w) * xi - 1 / (N + 1))
      have hid : k / 2 - (2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1) =
          (fiberLowerH N / (2 * (1 - w)) - 2 / (N + 1)) * xi ^ 2 -
            2 * xi * Real.sqrt (N * w) / (N + 1) := by
        dsimp [k]
        field_simp [ha0.ne', hm.ne'] <;> ring
      have hsquare' : 0 ≤ N * w * xi ^ 2 -
          2 * xi * Real.sqrt (N * w) / (N + 1) + 1 / (N + 1) ^ 2 := by
        simp only [sub_sq, mul_pow, div_pow, one_pow] at hsquare
        rw [hsSq] at hsquare
        convert hsquare using 1 <;> ring
      linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_log hkpos] at he
  have hmul := mul_le_mul_of_nonneg_left he ha0.le
  have hid : (1 - w) * ((1 + k) / Real.exp ((2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1))) =
      (1 - w + fiberLowerH N * xi ^ 2) *
        Real.exp (-(2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1)) := by
    rw [neg_div, Real.exp_neg]
    dsimp [k]
    field_simp [ha0.ne'] <;> ring
  rw [hid] at hmul
  simpa only [neg_div] using hmul

theorem fiber_lower_damping {N w xi : ℝ} (hN : 14 ≤ N)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hxi0 : 0 ≤ xi) (hxih : xi ≤ 1 / Real.sqrt 3) :
    (1 - w) * Real.exp (-1 / (N + 1) ^ 2) ≤
      (1 - w + fiberLowerH N * xi ^ 2) *
        Real.exp (-(2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1)) := by
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hx : xi * Real.sqrt 3 ≤ 1 := (le_div_iff₀ hs0).mp hxih
  have hxisq : xi ^ 2 ≤ (1 / 3 : ℝ) := by
    have hsq := (sq_le_sq₀ (mul_nonneg hxi0 hs0.le) (by norm_num : (0 : ℝ) ≤ 1)).2 hx
    nlinarith
  exact fiber_lower_damping_square hN hw0 hw1 hxi0 hxisq

end Erdos993Lean.Analytic.V213
