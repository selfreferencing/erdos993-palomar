module

public import Erdos993Lean.F4U.Light.Checker
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section


namespace F4U.Light

noncomputable def eval : List Int → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * eval p x

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl
@[simp] theorem eval_cons (a : Int) (p : List Int) (x : ℝ) :
    eval (a :: p) x = (a : ℝ) + x * eval p x := rfl

theorem absI_cast (a : Int) : (absI a : ℝ) = |(a : ℝ)| := by
  unfold absI
  split_ifs with h
  · rw [Int.cast_neg, abs_of_neg (by exact_mod_cast h)]
  · rw [abs_of_nonneg (by exact_mod_cast (le_of_not_gt h))]

theorem sumAbs_nonneg (p : List Int) : (0 : ℝ) ≤ (sumAbs p : ℝ) := by
  induction p with
  | nil => simp [sumAbs]
  | cons a p ih =>
    simp only [sumAbs, Int.cast_add, absI_cast]
    exact add_nonneg (abs_nonneg _) ih

/-- The list bound retains every coefficient, including zero entries. -/
theorem abs_eval_le_sumAbs (p : List Int) {u : ℝ} (hu : |u| ≤ 1) :
    |eval p u| ≤ (sumAbs p : ℝ) := by
  induction p with
  | nil => simp [sumAbs]
  | cons a p ih =>
    simp only [eval_cons, sumAbs, Int.cast_add, absI_cast]
    calc
      |(a : ℝ) + u * eval p u| ≤ |(a : ℝ)| + |u * eval p u| := abs_add_le _ _
      _ = |(a : ℝ)| + |u| * |eval p u| := by rw [abs_mul]
      _ ≤ |(a : ℝ)| + 1 * (sumAbs p : ℝ) := by
        exact add_le_add_right (mul_le_mul hu ih (abs_nonneg _) (by norm_num)) _
      _ = |(a : ℝ)| + (sumAbs p : ℝ) := by ring

/-- Soundness of the strict integer norm check on the entire closed unit interval. -/
theorem normOK_sound {G : List Int} (h : normOK G = true)
    {u : ℝ} (hu : |u| ≤ 1) : 0 < eval G u := by
  cases G with
  | nil => simp [normOK] at h
  | cons g0 rest =>
    have hi : 200 * sumAbs rest < 199 * g0 := of_decide_eq_true h
    have hr : (200 : ℝ) * (sumAbs rest : ℝ) < 199 * (g0 : ℝ) := by
      exact_mod_cast hi
    have habs := abs_eval_le_sumAbs rest hu
    have hmul : |u * eval rest u| ≤ (sumAbs rest : ℝ) := by
      rw [abs_mul]
      calc
        |u| * |eval rest u| ≤ 1 * (sumAbs rest : ℝ) :=
          mul_le_mul hu habs (abs_nonneg _) (by norm_num)
        _ = (sumAbs rest : ℝ) := one_mul _
    have hlo := (neg_le_of_abs_le hmul)
    have hn := sumAbs_nonneg rest
    simp only [eval_cons]
    linarith

end F4U.Light
