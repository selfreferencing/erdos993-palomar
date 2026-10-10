module

public import F4Heavy.Analysis.PolynomialSemantics
public import F4Heavy.Analysis.MatrixSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

/-- A small syntax whose normalization uses only explicit integer fractions. -/
inductive PolynomialExpr where
  | const : Fraction → PolynomialExpr
  | activity : PolynomialExpr
  | parent : PolynomialExpr
  | add : PolynomialExpr → PolynomialExpr → PolynomialExpr
  | mul : PolynomialExpr → PolynomialExpr → PolynomialExpr
  | pow : PolynomialExpr → Nat → PolynomialExpr

namespace PolynomialExpr

def valid : PolynomialExpr → Bool
  | .const c => 0 < c.den
  | .activity | .parent => true
  | .add a b | .mul a b => a.valid && b.valid
  | .pow a _ => a.valid

def normalize : PolynomialExpr → Polynomial
  | .const c => if c.num == 0 then [] else [⟨0, 0, c⟩]
  | .activity => [⟨1, 0, Fraction.one⟩]
  | .parent => [⟨0, 1, Fraction.one⟩]
  | .add a b => polyAdd a.normalize b.normalize
  | .mul a b => polyMul a.normalize b.normalize
  | .pow a n => polyPow a.normalize n

noncomputable def value (v x : ℝ) : PolynomialExpr → ℝ
  | .const c => fractionValue c
  | .activity => v
  | .parent => x
  | .add a b => a.value v x + b.value v x
  | .mul a b => a.value v x * b.value v x
  | .pow a n => a.value v x ^ n

theorem normalize_valid (e : PolynomialExpr) (h : e.valid = true) :
    validPolynomial e.normalize := by
  induction e with
  | const c =>
    have hd : 0 < c.den := by simpa [valid] using h
    simp only [normalize]
    split <;> simp_all [validPolynomial]
  | activity => simp [normalize, validPolynomial, Fraction.one, Fraction.ofInt]
  | parent => simp [normalize, validPolynomial, Fraction.one, Fraction.ofInt]
  | add a b ia ib =>
    have hh : a.valid = true ∧ b.valid = true := by simpa [valid] using h
    exact polyAdd_valid _ _ (ia hh.1) (ib hh.2)
  | mul a b ia ib =>
    have hh : a.valid = true ∧ b.valid = true := by simpa [valid] using h
    exact polyMul_valid _ _ (ia hh.1) (ib hh.2)
  | pow a n ia => exact polyPow_valid _ n (ia h)

theorem normalize_value (e : PolynomialExpr) (v x : ℝ) (h : e.valid = true) :
    polynomialValue e.normalize v x = e.value v x := by
  induction e with
  | const c =>
    by_cases hz : c.num = 0
    · simp [normalize, hz, value, polynomialValue, fractionValue]
    · simp [normalize, hz, value, polynomialValue, termValue]
  | activity => simp [normalize, value, polynomialValue, termValue, fractionValue_one]
  | parent => simp [normalize, value, polynomialValue, termValue, fractionValue_one]
  | add a b ia ib =>
    have hh : a.valid = true ∧ b.valid = true := by simpa [valid] using h
    exact (polyAdd_value _ _ v x (a.normalize_valid hh.1) (b.normalize_valid hh.2)).trans
      (congrArg₂ (· + ·) (ia hh.1) (ib hh.2))
  | mul a b ia ib =>
    have hh : a.valid = true ∧ b.valid = true := by simpa [valid] using h
    exact (polyMul_value _ _ v x (a.normalize_valid hh.1) (b.normalize_valid hh.2)).trans
      (congrArg₂ (· * ·) (ia hh.1) (ib hh.2))
  | pow a n ia =>
    exact (polyPow_value _ n v x (a.normalize_valid h)).trans (congrArg (· ^ n) (ia h))

def check (a b : PolynomialExpr) : Bool :=
  a.valid && b.valid && polyEq a.normalize b.normalize

theorem check_sound (a b : PolynomialExpr) (h : check a b = true) (v x : ℝ) :
    a.value v x = b.value v x := by
  have hh : (a.valid = true ∧ b.valid = true) ∧ polyEq a.normalize b.normalize = true := by
    simpa [check] using h
  rw [← normalize_value a v x hh.1.1, ← normalize_value b v x hh.1.2]
  exact polyEq_sound _ _ v x hh.2

def row (p : List Fraction) : PolynomialExpr :=
  p.foldr (fun c z => .add (.const c) (.mul .parent z)) (.const Fraction.zero)

def matrix (p : List (List Fraction)) : PolynomialExpr :=
  p.foldr (fun r z => .add (row r) (.mul .activity z)) (.const Fraction.zero)

theorem row_value (p : List Fraction) (v x : ℝ) :
    (row p).value v x = realHorner (p.map fractionValue) x := by
  induction p with
  | nil => simp [row, value, realHorner, fractionValue_zero]
  | cons c p ih =>
    change fractionValue c + x * (row p).value v x = _
    rw [ih]
    rfl

theorem matrix_value (p : List (List Fraction)) (v x : ℝ) :
    (matrix p).value v x = matrixValue p v x := by
  induction p with
  | nil => simp [matrix, value, matrixValue, realHorner, fractionValue_zero]
  | cons r p ih =>
    change (row r).value v x + v * (matrix p).value v x = _
    rw [row_value, ih]
    rfl

end PolynomialExpr
end F4Heavy.Analysis
