module

public import Erdos993Lean.F4U.Light.Soundness.Norm
public import Mathlib.Data.Nat.Choose.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FieldSimp

@[expose] public section


namespace F4U.Light

theorem descFact_eq (n k : Nat) : descFact n k = n.descFactorial k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [descFact, Nat.descFactorial_succ, ih]

theorem fact_eq (k : Nat) : fact k = k.factorial := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [fact, Nat.factorial_succ, ih]

/-- The executable division formula equals the usual binomial coefficient. -/
theorem binom_eq_choose (n k : Nat) : binom n k = n.choose k := by
  simp only [binom, descFact_eq, fact_eq, ← Nat.choose_eq_descFactorial_div_factorial]

@[simp] theorem eval_padd (p q : List Int) (x : ℝ) :
    eval (padd p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q => simp only [padd, eval_cons, Int.cast_add, ih]; ring

@[simp] theorem eval_pneg (p : List Int) (x : ℝ) : eval (pneg p) x = -eval p x := by
  induction p with
  | nil => simp [pneg]
  | cons a p ih => simp only [pneg, eval_cons, Int.cast_neg, ih]; ring

@[simp] theorem eval_psub (p q : List Int) (x : ℝ) :
    eval (psub p q) x = eval p x - eval q x := by
  induction p generalizing q with
  | nil => simp [psub]
  | cons a p ih =>
    cases q with
    | nil => simp [psub]
    | cons b q => simp only [psub, eval_cons, Int.cast_sub, ih]; ring

@[simp] theorem eval_pscale (a : Int) (p : List Int) (x : ℝ) :
    eval (pscale a p) x = (a : ℝ) * eval p x := by
  induction p with
  | nil => simp [pscale]
  | cons b p ih => simp only [pscale, eval_cons, Int.cast_mul, ih]; ring

@[simp] theorem eval_append (p q : List Int) (x : ℝ) :
    eval (p ++ q) x = eval p x + x ^ p.length * eval q x := by
  induction p with
  | nil => simp
  | cons a p ih => simp only [List.cons_append, eval_cons, List.length_cons, ih, pow_succ]; ring

@[simp] theorem eval_trimZ (p : List Int) (x : ℝ) : eval (trimZ p) x = eval p x := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [trimZ]
    split_ifs with h
    · rcases h with ⟨ha, ht⟩
      have hp : eval p x = 0 := by rw [← ih, ht]; rfl
      simp [eval, ha, hp]
    · simp only [eval_cons, ih]

theorem eval_mlGo (c r prev : Int) (G : List Int) (u : ℝ) :
    eval (mlGo c r prev G) u = ((c : ℝ) + (r : ℝ) * u) * eval G u + (r : ℝ) * prev := by
  induction G generalizing prev with
  | nil => simp [mlGo, eval]
  | cons g G ih =>
    simp only [mlGo, eval_cons, Int.cast_add, Int.cast_mul, ih]
    ring

theorem eval_mulLinAdd (c r b : Int) (G : List Int) (u : ℝ) :
    eval (mulLinAdd c r b G) u = ((c : ℝ) + (r : ℝ) * u) * eval G u + (b : ℝ) := by
  cases G with
  | nil => simp [mulLinAdd, eval]
  | cons g G =>
    simp only [mulLinAdd, eval_cons, eval_mlGo, Int.cast_add, Int.cast_mul]
    ring

theorem hornerGo_append (c r D : Int) (xs ys : List Int) (P : Int) (G : List Int) :
    hornerGo c r D (xs ++ ys) P G =
      hornerGo c r D ys (P * D ^ xs.length) (hornerGo c r D xs P G) := by
  induction xs generalizing P G with
  | nil => simp [hornerGo]
  | cons b xs ih =>
    simp only [List.cons_append, hornerGo, List.length_cons, ih, pow_succ]
    congr 1
    ring

theorem shiftScale_cons (c r D a : Int) (p : List Int) :
    shiftScale c r D (a :: p) = mulLinAdd c r (a * D ^ p.length) (shiftScale c r D p) := by
  simp only [shiftScale, List.reverse_cons, hornerGo_append, List.length_reverse, one_mul,
    hornerGo]

noncomputable def homogeneous (D z : ℝ) : List Int → ℝ
  | [] => 0
  | a :: p => (a : ℝ) * D ^ p.length + z * homogeneous D z p

theorem eval_shiftScale_homogeneous (c r D : Int) (B : List Int) (u : ℝ) :
    eval (shiftScale c r D B) u = homogeneous D ((c : ℝ) + (r : ℝ) * u) B := by
  induction B with
  | nil => rfl
  | cons a B ih =>
    rw [shiftScale_cons, eval_mulLinAdd, ih]
    simp only [homogeneous, Int.cast_mul, Int.cast_pow]
    ring

theorem homogeneous_eq_scaled_eval (D z : ℝ) (hD : D ≠ 0) (B : List Int) :
    homogeneous D z B = D ^ (B.length - 1) * eval B (z / D) := by
  induction B with
  | nil => simp [homogeneous]
  | cons a B ih =>
    cases B with
    | nil => simp [homogeneous, eval]
    | cons b B =>
      simp only [homogeneous, List.length_cons, Nat.add_sub_cancel, eval_cons] at ih ⊢
      rw [ih]
      rw [pow_succ]
      field_simp [hD]

/-- The positive homogeneous multiplier is explicit; no normalization is assumed. -/
theorem eval_shiftScale (c r D : Int) (hD : (D : ℝ) ≠ 0) (B : List Int) (u : ℝ) :
    eval (shiftScale c r D B) u = (D : ℝ) ^ (B.length - 1) *
      eval B (((c : ℝ) + (r : ℝ) * u) / D) := by
  rw [eval_shiftScale_homogeneous, homogeneous_eq_scaled_eval _ _ hD]

end F4U.Light
