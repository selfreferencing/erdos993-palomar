module

public import Erdos993Lean.F4U.Light.Soundness.Polynomial

/-! Integer bivariate polynomial arithmetic for exact Phase2 linking.

Rows are ascending in the second variable; each row is an ascending list in the
first variable, exactly as in the fixed `Fn.rows` data. Every executable operation
uses `Int`, `Nat`, `List`, and `Bool`. Real evaluation appears only in the proved
semantic interface. No rational evaluation, particular function reconstruction,
denominator orientation, logarithm comparison, or LightCore assertion is made.
-/

@[expose] public section

namespace F4U.Light.Linking.Polynomial2

abbrev Rows := List (List Int)

noncomputable def eval : Rows → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: p, x, y => F4U.Light.eval a x + y * eval p x y

@[simp] theorem eval_nil (x y : ℝ) : eval [] x y = 0 := rfl

@[simp] theorem eval_cons (a : List Int) (p : Rows) (x y : ℝ) :
    eval (a :: p) x y = F4U.Light.eval a x + y * eval p x y := rfl

def const (c : Int) : Rows := [[c]]
def X : Rows := [[0, 1]]
def Y : Rows := [[], [1]]

@[simp] theorem eval_const (c : Int) (x y : ℝ) : eval (const c) x y = c := by
  simp [const]

@[simp] theorem eval_X (x y : ℝ) : eval X x y = x := by simp [X]
@[simp] theorem eval_Y (x y : ℝ) : eval Y x y = y := by simp [Y]

def padd : Rows → Rows → Rows
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => F4U.Light.padd a b :: padd p q

def pscale (c : Int) : Rows → Rows
  | [] => []
  | a :: p => F4U.Light.pscale c a :: pscale c p

def pneg (p : Rows) : Rows := pscale (-1) p
def psub (p q : Rows) : Rows := padd p (pneg q)

@[simp] theorem eval_padd (p q : Rows) (x y : ℝ) :
    eval (padd p q) x y = eval p x y + eval q x y := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q => simp only [padd, eval_cons, F4U.Light.eval_padd, ih]; ring

@[simp] theorem eval_pscale (c : Int) (p : Rows) (x y : ℝ) :
    eval (pscale c p) x y = (c : ℝ) * eval p x y := by
  induction p with
  | nil => simp [pscale]
  | cons a p ih => simp only [pscale, eval_cons, F4U.Light.eval_pscale, ih]; ring

@[simp] theorem eval_pneg (p : Rows) (x y : ℝ) :
    eval (pneg p) x y = -eval p x y := by simp [pneg]

@[simp] theorem eval_psub (p q : Rows) (x y : ℝ) :
    eval (psub p q) x y = eval p x y - eval q x y := by simp [psub, sub_eq_add_neg]

/-- Inner-variable convolution, with all padding retained. -/
def mulRow : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => F4U.Light.padd (F4U.Light.pscale a q) (0 :: mulRow p q)

@[simp] theorem eval_mulRow (p q : List Int) (x : ℝ) :
    F4U.Light.eval (mulRow p q) x = F4U.Light.eval p x * F4U.Light.eval q x := by
  induction p with
  | nil => simp [mulRow]
  | cons a p ih =>
    simp only [mulRow, F4U.Light.eval_padd, F4U.Light.eval_pscale,
      F4U.Light.eval_cons, Int.cast_zero, zero_add, ih]
    ring

def mulByRow (a : List Int) : Rows → Rows
  | [] => []
  | b :: q => mulRow a b :: mulByRow a q

@[simp] theorem eval_mulByRow (a : List Int) (q : Rows) (x y : ℝ) :
    eval (mulByRow a q) x y = F4U.Light.eval a x * eval q x y := by
  induction q with
  | nil => simp [mulByRow]
  | cons b q ih => simp only [mulByRow, eval_cons, eval_mulRow, ih]; ring

/-- Outer-variable convolution; an empty row is the zero coefficient row. -/
def pmul : Rows → Rows → Rows
  | [], _ => []
  | a :: p, q => padd (mulByRow a q) ([] :: pmul p q)

@[simp] theorem eval_pmul (p q : Rows) (x y : ℝ) :
    eval (pmul p q) x y = eval p x y * eval q x y := by
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    simp only [pmul, eval_padd, eval_mulByRow, eval_cons,
      F4U.Light.eval_nil, zero_add, ih]
    ring

def ppow (p : Rows) : Nat → Rows
  | 0 => const 1
  | n + 1 => pmul (ppow p n) p

@[simp] theorem eval_ppow (p : Rows) (n : Nat) (x y : ℝ) :
    eval (ppow p n) x y = eval p x y ^ n := by
  induction n with
  | zero => simp [ppow]
  | succ n ih => simp only [ppow, eval_pmul, ih, pow_succ]

def shiftRow : Nat → List Int → List Int
  | 0, p => p
  | n + 1, p => 0 :: shiftRow n p

def shiftRows : Nat → Rows → Rows
  | 0, p => p
  | n + 1, p => [] :: shiftRows n p

@[simp] theorem eval_shiftRow (n : Nat) (p : List Int) (x : ℝ) :
    F4U.Light.eval (shiftRow n p) x = x ^ n * F4U.Light.eval p x := by
  induction n with
  | zero => simp [shiftRow]
  | succ n ih => simp only [shiftRow, F4U.Light.eval_cons, Int.cast_zero,
      zero_add, ih, pow_succ]; ring

@[simp] theorem eval_shiftRows (n : Nat) (p : Rows) (x y : ℝ) :
    eval (shiftRows n p) x y = y ^ n * eval p x y := by
  induction n with
  | zero => simp [shiftRows]
  | succ n ih => simp only [shiftRows, eval_cons, F4U.Light.eval_nil,
      zero_add, ih, pow_succ]; ring

structure Term where
  coefficient : Int
  xPower : Nat
  yPower : Nat
  deriving DecidableEq, Repr

def monomial (c : Int) (i j : Nat) : Rows := shiftRows j [shiftRow i [c]]

@[simp] theorem eval_monomial (c : Int) (i j : Nat) (x y : ℝ) :
    eval (monomial c i j) x y = (c : ℝ) * x ^ i * y ^ j := by
  simp only [monomial, eval_shiftRows, eval_cons, eval_shiftRow,
    F4U.Light.eval_cons, F4U.Light.eval_nil, eval_nil, mul_zero, add_zero]
  ring

def ofSparse : List Term → Rows
  | [] => []
  | a :: p => padd (monomial a.coefficient a.xPower a.yPower) (ofSparse p)

noncomputable def evalSparse : List Term → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: p, x, y => (a.coefficient : ℝ) * x ^ a.xPower * y ^ a.yPower + evalSparse p x y

@[simp] theorem eval_ofSparse (p : List Term) (x y : ℝ) :
    eval (ofSparse p) x y = evalSparse p x y := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [ofSparse, eval_padd, eval_monomial, evalSparse, ih]

/-- Trim each inner row and then remove only trailing zero outer rows. -/
def trim : Rows → Rows
  | [] => []
  | a :: p =>
      let b := F4U.Light.trimZ a
      let q := trim p
      if b = [] ∧ q = [] then [] else b :: q

@[simp] theorem eval_trim (p : Rows) (x y : ℝ) : eval (trim p) x y = eval p x y := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [trim]
    split_ifs with h
    · rcases h with ⟨ha, hp⟩
      have hrow : F4U.Light.eval a x = 0 := by rw [← F4U.Light.eval_trimZ, ha]; rfl
      have htail : eval p x y = 0 := by rw [← ih, hp]; rfl
      simp [eval_cons, hrow, htail]
    · simp only [eval_cons, F4U.Light.eval_trimZ, ih]

def exactEq (p q : Rows) : Bool := decide (p = q)
def normalizedEq (p q : Rows) : Bool := decide (trim p = trim q)

/-- Exact equality retains the coefficient arrays supplied by the consumer. -/
theorem exactEq_sound {p q : Rows} (h : exactEq p q = true) (x y : ℝ) :
    eval p x y = eval q x y := by
  have hpq : p = q := of_decide_eq_true h
  rw [hpq]

/-- Padding can be removed only through the proved evaluation-preserving trim. -/
theorem normalizedEq_sound {p q : Rows} (h : normalizedEq p q = true) (x y : ℝ) :
    eval p x y = eval q x y := by
  have hpq : trim p = trim q := of_decide_eq_true h
  rw [← eval_trim p x y, hpq, eval_trim]

def coefficientMass : Rows → Int
  | [] => 0
  | a :: p => F4U.Light.sumAbs a + coefficientMass p

theorem coefficientMass_nonneg (p : Rows) : (0 : ℝ) ≤ (coefficientMass p : ℝ) := by
  induction p with
  | nil => simp [coefficientMass]
  | cons a p ih =>
    simp only [coefficientMass, Int.cast_add]
    exact add_nonneg (F4U.Light.sumAbs_nonneg a) ih

/-- Every coefficient, including zero padding, remains in the explicit row object. -/
theorem abs_eval_le_coefficientMass (p : Rows) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |eval p x y| ≤ (coefficientMass p : ℝ) := by
  induction p with
  | nil => simp [coefficientMass]
  | cons a p ih =>
    simp only [eval_cons, coefficientMass, Int.cast_add]
    calc
      |F4U.Light.eval a x + y * eval p x y| ≤
          |F4U.Light.eval a x| + |y * eval p x y| := abs_add_le _ _
      _ = |F4U.Light.eval a x| + |y| * |eval p x y| := by rw [abs_mul]
      _ ≤ (F4U.Light.sumAbs a : ℝ) + 1 * (coefficientMass p : ℝ) := by
        exact add_le_add (F4U.Light.abs_eval_le_sumAbs a hx)
          (mul_le_mul hy ih (abs_nonneg _) (by norm_num))
      _ = (F4U.Light.sumAbs a : ℝ) + (coefficientMass p : ℝ) := by ring

/-- Strict constant coefficient versus the absolute mass of every other coefficient. -/
def rectangleNormOK : Rows → Bool
  | (c :: a) :: p => decide (F4U.Light.sumAbs a + coefficientMass p < c)
  | _ => false

theorem rectangleNormOK_sound {p : Rows} (h : rectangleNormOK p = true)
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : 0 < eval p x y := by
  cases p with
  | nil => simp [rectangleNormOK] at h
  | cons a p =>
    cases a with
    | nil => simp [rectangleNormOK] at h
    | cons c a =>
      have hi : F4U.Light.sumAbs a + coefficientMass p < c := of_decide_eq_true h
      have hr : (F4U.Light.sumAbs a : ℝ) + (coefficientMass p : ℝ) < (c : ℝ) := by
        exact_mod_cast hi
      have hxa : |x * F4U.Light.eval a x| ≤ (F4U.Light.sumAbs a : ℝ) := by
        rw [abs_mul]
        calc
          |x| * |F4U.Light.eval a x| ≤ 1 * (F4U.Light.sumAbs a : ℝ) :=
            mul_le_mul hx (F4U.Light.abs_eval_le_sumAbs a hx) (abs_nonneg _) (by norm_num)
          _ = (F4U.Light.sumAbs a : ℝ) := by ring
      have hyp : |y * eval p x y| ≤ (coefficientMass p : ℝ) := by
        rw [abs_mul]
        calc
          |y| * |eval p x y| ≤ 1 * (coefficientMass p : ℝ) :=
            mul_le_mul hy (abs_eval_le_coefficientMass p hx hy) (abs_nonneg _) (by norm_num)
          _ = (coefficientMass p : ℝ) := by ring
      have hxaLower := neg_le_of_abs_le hxa
      have hypLower := neg_le_of_abs_le hyp
      simp only [eval_cons, F4U.Light.eval_cons]
      linarith

/-- A reduction step carries both integer coefficient identities and the actual
old denominator. Nonvanishing of the removed factor is a conclusion, not input. -/
theorem reduction_factor_nonzero {rawD factor newD : Rows} {scale : Int}
    (hscale : 0 < scale)
    (hD : normalizedEq (pscale scale rawD) (pmul factor newD) = true)
    (x y : ℝ) (hrawD : eval rawD x y ≠ 0) :
    eval factor x y ≠ 0 ∧ eval newD x y ≠ 0 := by
  have hs : (scale : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hscale)
  have hd := normalizedEq_sound hD x y
  simp only [eval_pscale, eval_pmul] at hd
  have hp : eval factor x y * eval newD x y ≠ 0 := by
    rw [← hd]
    exact mul_ne_zero hs hrawD
  exact mul_ne_zero_iff.mp hp

/-- Two proved integer array identities give the lossless fraction step.
The only nonvanishing premise is the already-retained original denominator. -/
theorem reduction_sound {rawN rawD factor newN newD : Rows} {scale : Int}
    (hscale : 0 < scale)
    (hN : normalizedEq (pscale scale rawN) (pmul factor newN) = true)
    (hD : normalizedEq (pscale scale rawD) (pmul factor newD) = true)
    (x y : ℝ) (hrawD : eval rawD x y ≠ 0) :
    eval newD x y ≠ 0 ∧ eval rawN x y / eval rawD x y = eval newN x y / eval newD x y := by
  have hs : (scale : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hscale)
  have hdNZ := (reduction_factor_nonzero hscale hD x y hrawD).2
  have hn := normalizedEq_sound hN x y
  have hd := normalizedEq_sound hD x y
  simp only [eval_pscale, eval_pmul] at hn hd
  refine ⟨hdNZ, (div_eq_div_iff hrawD hdNZ).mpr ?_⟩
  have hcross : (scale : ℝ) * (eval rawN x y * eval newD x y) =
      (scale : ℝ) * (eval newN x y * eval rawD x y) := by
    calc
      _ = ((scale : ℝ) * eval rawN x y) * eval newD x y := by ring
      _ = (eval factor x y * eval newN x y) * eval newD x y := by rw [hn]
      _ = (eval factor x y * eval newD x y) * eval newN x y := by ring
      _ = ((scale : ℝ) * eval rawD x y) * eval newN x y := by rw [← hd]
      _ = _ := by ring
  exact mul_left_cancel₀ hs hcross

end F4U.Light.Linking.Polynomial2
