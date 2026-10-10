module

public import Erdos993Lean.F4U.Light.Soundness.Norm

@[expose] public section


namespace F4U.Light

/-- Endpoint positivity and the interior discriminant cover every quadratic on [-1,1]. -/
theorem quadratic_pos_on_unit (a b c : ℝ)
    (hm : 0 < a - b + c) (hp : 0 < a + b + c)
    (hd : 0 < a → |b| < 2 * a → b * b < 4 * a * c)
    {u : ℝ} (hu : |u| ≤ 1) : 0 < a * u ^ 2 + b * u + c := by
  have hu' := abs_le.mp hu
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg (u - 1), sq_nonneg (u + 1)]
  by_cases ha : 0 < a
  · by_cases hb : |b| < 2 * a
    · have hdisc := hd ha hb
      have hs := sq_nonneg (2 * a * u + b)
      have hident : 4 * a * (a * u ^ 2 + b * u + c) =
          (2 * a * u + b) ^ 2 + (4 * a * c - b * b) := by ring
      have hproduct : 0 < 4 * a * (a * u ^ 2 + b * u + c) := by
        rw [hident]
        linarith
      exact (mul_pos_iff_of_pos_left (by linarith : (0 : ℝ) < 4 * a)).mp hproduct
    · have hab : 2 * a ≤ |b| := le_of_not_gt hb
      rcases le_or_gt 0 b with hb0 | hb0
      · rw [abs_of_nonneg hb0] at hab
        have hn1 : 0 ≤ u + 1 := by linarith [hu'.1]
        have hn2 : 0 ≤ a * (u - 1) + b := by nlinarith [hu'.1]
        have hn := mul_nonneg hn1 hn2
        nlinarith
      · rw [abs_of_neg hb0] at hab
        have hn1 : 0 ≤ 1 - u := by linarith [hu'.2]
        have hn2 : 0 ≤ -a * (u + 1) - b := by nlinarith [hu'.2]
        have hn := mul_nonneg hn1 hn2
        nlinarith
  · have ha' : a ≤ 0 := le_of_not_gt ha
    have h1 : 0 ≤ (1 - u) / 2 := by linarith [hu'.2]
    have h2 : 0 ≤ (1 + u) / 2 := by linarith [hu'.1]
    have he : 0 < (1 - u) / 2 * (a - b + c) +
        (1 + u) / 2 * (a + b + c) := by
      by_cases hz : (1 - u) / 2 = 0
      · have hu1 : u = 1 := by linarith
        simpa [hu1] using hp
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (lt_of_le_of_ne h1 (Ne.symm hz)) hm) (mul_nonneg h2 (le_of_lt hp))
    have hcorr : 0 ≤ a * (u ^ 2 - 1) := mul_nonneg_of_nonpos_of_nonpos ha' (by linarith)
    nlinarith

theorem eval_split_three (G : List Int) (u : ℝ) :
    eval G u = (G.getD 0 0 : ℝ) + (G.getD 1 0 : ℝ) * u +
      (G.getD 2 0 : ℝ) * u ^ 2 + u ^ 3 * eval (G.drop 3) u := by
  cases G with
  | nil => simp
  | cons g0 G =>
    cases G with
    | nil => simp [eval]
    | cons g1 G =>
      cases G with
      | nil => simp [eval]; ring
      | cons g2 G => simp [eval]; ring

/-- Terms of order at least three have a lower bound proportional to u². -/
theorem tail_lower_bound (G : List Int) {u : ℝ} (hu : |u| ≤ 1) :
    -(sumAbs (G.drop 3) : ℝ) * u ^ 2 ≤ u ^ 3 * eval (G.drop 3) u := by
  have ht := abs_eval_le_sumAbs (G.drop 3) hu
  have hmul : |u * eval (G.drop 3) u| ≤ (sumAbs (G.drop 3) : ℝ) := by
    rw [abs_mul]
    calc
      |u| * |eval (G.drop 3) u| ≤ 1 * (sumAbs (G.drop 3) : ℝ) :=
        mul_le_mul hu ht (abs_nonneg _) (by norm_num)
      _ = (sumAbs (G.drop 3) : ℝ) := one_mul _
  have hlo := neg_le_of_abs_le hmul
  have hh := mul_le_mul_of_nonneg_left hlo (sq_nonneg u)
  nlinarith

/-- Soundness of the prototype's strict integer quadratic minorant. -/
theorem quadOK_sound {G : List Int} (h : quadOK G = true)
    {u : ℝ} (hu : |u| ≤ 1) : 0 < eval G u := by
  let g0 := G.getD 0 0
  let g1 := G.getD 1 0
  let g2 := G.getD 2 0
  let T := sumAbs (G.drop 3)
  let a := 200 * (g2 - T)
  let b := 200 * g1
  let c := 199 * g0
  change (decide (0 < g0) && decide (0 < a - b + c) && decide (0 < a + b + c) &&
    (!(decide (0 < a) && decide (absI b < 2 * a)) || decide (b * b < 4 * a * c))) = true at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hleft, hlast⟩
  rcases Bool.and_eq_true_iff.mp hleft with ⟨hleft, hp⟩
  rcases Bool.and_eq_true_iff.mp hleft with ⟨h0, hm⟩
  have hi0 : 0 < g0 := of_decide_eq_true h0
  have him : 0 < a - b + c := of_decide_eq_true hm
  have hip : 0 < a + b + c := of_decide_eq_true hp
  have hid : 0 < a → absI b < 2 * a → b * b < 4 * a * c := by
    intro ha hb
    simpa [ha, hb] using hlast
  have hr0 : (0 : ℝ) < (g0 : ℝ) := by exact_mod_cast hi0
  have hrm : (0 : ℝ) < (a : ℝ) - (b : ℝ) + (c : ℝ) := by exact_mod_cast him
  have hrp : (0 : ℝ) < (a : ℝ) + (b : ℝ) + (c : ℝ) := by exact_mod_cast hip
  have hrd : (0 : ℝ) < (a : ℝ) → |(b : ℝ)| < 2 * (a : ℝ) →
      (b : ℝ) * (b : ℝ) < 4 * (a : ℝ) * (c : ℝ) := by
    intro ha hb
    have hia : 0 < a := by exact_mod_cast ha
    have hib : absI b < 2 * a := by rw [← absI_cast] at hb; exact_mod_cast hb
    exact_mod_cast hid hia hib
  have hq := quadratic_pos_on_unit (a : ℝ) (b : ℝ) (c : ℝ) hrm hrp hrd hu
  have ht := tail_lower_bound G hu
  have he := eval_split_three G u
  dsimp [a, b, c, g0, g1, g2, T] at hq hr0
  push_cast at hq
  nlinarith

end F4U.Light
