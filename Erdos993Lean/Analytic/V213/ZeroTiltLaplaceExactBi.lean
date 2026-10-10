module

public import Erdos993Lean.BCFG.Bivariate

/-! Executable polynomial arithmetic for the ten printed certificates.
The raw coefficient lists have no asserted ring instance. Every operation is
interpreted by an explicit Real evaluation theorem. No finite check is run here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

open Erdos993Lean.BCFG

def innerMul (a : Uni) (p : Bi) : Bi := p.map (Uni.mul a)

def mul : Bi → Bi → Bi
  | [], _ => []
  | a :: p, q => Bi.add (innerMul a q) ([] :: mul p q)

def neg (p : Bi) : Bi := p.map (Uni.scale (-1))

def pow (p : Bi) : Nat → Bi
  | 0 => [[1]]
  | n+1 => mul (pow p n) p

@[simp] theorem eval_innerMul (a : Uni) (p : Bi) (s z : ℝ) :
    Bi.evalReal (innerMul a p) s z = Uni.evalReal a z * Bi.evalReal p s z := by
  induction p with
  | nil => simp [innerMul]
  | cons b p ih =>
      simp only [innerMul, List.map_cons, Bi.evalReal_cons, Uni.evalReal_mul] at *
      rw [ih]
      ring

@[simp] theorem eval_mul (p q : Bi) (s z : ℝ) :
    Bi.evalReal (mul p q) s z = Bi.evalReal p s z * Bi.evalReal q s z := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      simp only [mul, Bi.evalReal_add, eval_innerMul, Bi.evalReal_cons,
        Uni.evalReal_nil, zero_add, ih]
      ring

@[simp] theorem eval_neg (p : Bi) (s z : ℝ) :
    Bi.evalReal (neg p) s z = -Bi.evalReal p s z := by
  induction p with
  | nil => simp [neg]
  | cons a p ih =>
      simp only [neg, List.map_cons, Bi.evalReal_cons, Uni.evalReal_scale] at *
      rw [ih]
      norm_num
      ring

@[simp] theorem eval_pow (p : Bi) (n : Nat) (s z : ℝ) :
    Bi.evalReal (pow p n) s z = Bi.evalReal p s z ^ n := by
  induction n with
  | zero => simp [pow, Bi.evalReal, Uni.evalReal]
  | succ n ih => simp [pow, eval_mul, ih, pow_succ]

/-- A small syntax for the literal polynomial expressions; coefficients are
exact Rat, and both affine variables remain explicit. -/
inductive Expr where
  | constant : Rat → Expr
  | first : Expr
  | second : Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → Nat → Expr
  deriving Repr

namespace Expr

instance (n : Nat) : OfNat Expr n := ⟨constant n⟩
instance : Add Expr := ⟨add⟩
instance : Neg Expr := ⟨neg⟩
instance : Sub Expr := ⟨fun a b => add a (neg b)⟩
instance : Mul Expr := ⟨mul⟩
instance : Pow Expr Nat := ⟨pow⟩

noncomputable def eval : Expr → ℝ → ℝ → ℝ
  | constant a, _, _ => a
  | first, x, _ => x
  | second, _, y => y
  | add a b, x, y => eval a x y + eval b x y
  | neg a, x, y => -eval a x y
  | mul a b, x, y => eval a x y * eval b x y
  | pow a n, x, y => eval a x y ^ n

def encode : Expr → Bi → Bi → Bi
  | constant a, _, _ => [[a]]
  | first, x, _ => x
  | second, _, y => y
  | add a b, x, y => Bi.add (encode a x y) (encode b x y)
  | neg a, x, y => FinitePolynomial.neg (encode a x y)
  | mul a b, x, y => FinitePolynomial.mul (encode a x y) (encode b x y)
  | pow a n, x, y => FinitePolynomial.pow (encode a x y) n

theorem encode_sound (e : Expr) (x y : Bi) (s z : ℝ) :
    Bi.evalReal (encode e x y) s z = eval e (Bi.evalReal x s z) (Bi.evalReal y s z) := by
  induction e with
  | constant a => simp [encode, eval, Bi.evalReal, Uni.evalReal]
  | first => rfl
  | second => rfl
  | add a b ha hb => simp [encode, eval, ha, hb]
  | neg a ha => simp [encode, eval, ha]
  | mul a b ha hb => simp [encode, eval, ha, hb]
  | pow a n ha => simp [encode, eval, ha]

/-- The chart uses its actual two endpoints, not a midpoint convention. -/
def chart (e : Expr) (l h v w : Rat) : Bi :=
  encode e [[l], [h-l]] [[v,w-v]]

theorem chart_sound (e : Expr) (l h v w : Rat) (s z : ℝ) :
    Bi.evalReal (chart e l h v w) s z =
      eval e ((l : ℝ)+((h : ℝ)-(l : ℝ))*s)
        ((v : ℝ)+((w : ℝ)-(v : ℝ))*z) := by
  rw [chart, encode_sound]
  simp only [Bi.evalReal, Uni.evalReal, Rat.cast_sub, mul_zero, add_zero]
  congr 1 <;> ring

end Expr

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.eval_innerMul
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.eval_innerMul
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.eval_mul
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.eval_mul
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.eval_neg
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.eval_neg
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.eval_pow
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.eval_pow
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode_sound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.chart_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.chart_sound
