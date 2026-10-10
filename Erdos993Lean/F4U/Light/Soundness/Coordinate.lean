module

public import Erdos993Lean.F4U.Light.Soundness.Polynomial
public import Mathlib.Data.List.Induction

@[expose] public section


namespace F4U.Light

theorem length_pneg (p : List Int) : (pneg p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [pneg, ih]

theorem length_psub (p q : List Int) : (psub p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [psub, length_pneg]
  | cons a p ih =>
    cases q with
    | nil => simp [psub]
    | cons b q => simp [psub, ih, Nat.succ_max_succ]

theorem toQGo_append (xs ys H : List Int) : toQGo (xs ++ ys) H = toQGo ys (toQGo xs H) := by
  induction xs generalizing H with
  | nil => rfl
  | cons b xs ih => simp only [List.cons_append, toQGo, ih]

theorem length_toQGo (p H : List Int) : (toQGo p H).length = H.length + p.length := by
  induction p generalizing H with
  | nil => simp [toQGo]
  | cons b p ih =>
    simp only [toQGo, ih, length_psub, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem homogeneous_append_singleton (D z : ℝ) (p : List Int) (b : Int) :
    homogeneous D z (p ++ [b]) = D * homogeneous D z p + (b : ℝ) * z ^ p.length := by
  induction p with
  | nil => simp [homogeneous]
  | cons a p ih =>
    simp only [List.cons_append, homogeneous, List.length_append, List.length_nil,
      List.length_cons, ih, pow_succ, pow_zero, mul_one, add_zero]
    ring

theorem eval_toQGo_nil (p : List Int) (q : ℝ) :
    eval (toQGo p []) q = homogeneous (1 - q) q p := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p b ih =>
    rw [toQGo_append, toQGo, toQGo, eval_psub, eval_append]
    simp only [eval_cons, eval_nil, Int.cast_zero, zero_add, mul_zero, add_zero]
    rw [length_toQGo, List.length_nil, Nat.zero_add, ih, homogeneous_append_singleton]
    ring

/-- Coordinate change carries the actual trimmed degree and its positive multiplier. -/
theorem eval_toQ (p : List Int) {q : ℝ} (hq : q ≠ 1) :
    eval (toQ p) q = (1 - q) ^ ((trimZ p).length - 1) * eval p (q / (1 - q)) := by
  rw [toQ, eval_toQGo_nil, homogeneous_eq_scaled_eval]
  · rw [eval_trimZ]
  · exact sub_ne_zero.mpr (Ne.symm hq)

end F4U.Light
