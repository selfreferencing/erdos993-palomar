module

public import F4Heavy.Analysis.MatrixLinear
public import F4Heavy.Analysis.TransformBasics

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Heavy.Finite

namespace CoefficientMatrix

def validRow (p : List Fraction) : Bool := p.all (fun c => 0 < c.den)
def valid (p : List (List Fraction)) : Bool := p.all validRow
def add (p q : List (List Fraction)) : List (List Fraction) :=
  p.zipWith (fun a b => a.zipWith Fraction.add b) q
def scale (c : Fraction) (p : List (List Fraction)) : List (List Fraction) :=
  p.map (fun row => row.map (Fraction.mul c))

theorem row_add_valid (p q : List Fraction) (hp : validRow p = true)
    (hq : validRow q = true) : validRow (p.zipWith Fraction.add q) = true := by
  induction p generalizing q with
  | nil => simp [validRow]
  | cons a p ih =>
    cases q with
    | nil => simp [validRow]
    | cons b q =>
      have hp' : 0 < a.den ∧ validRow p = true := by simpa [validRow] using hp
      have hq' : 0 < b.den ∧ validRow q = true := by simpa [validRow] using hq
      simpa only [List.zipWith_cons_cons, validRow, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] using And.intro (fraction_add_den_pos a b hp'.1 hq'.1)
          (ih q hp'.2 hq'.2)

theorem row_add_value (p q : List Fraction) (hp : validRow p = true)
    (hq : validRow q = true) :
    (p.zipWith Fraction.add q).map fractionValue =
      (p.map fractionValue).zipWith (· + ·) (q.map fractionValue) := by
  induction p generalizing q with
  | nil => simp
  | cons a p ih =>
    cases q with
    | nil => simp
    | cons b q =>
      have hp' : 0 < a.den ∧ validRow p = true := by simpa [validRow] using hp
      have hq' : 0 < b.den ∧ validRow q = true := by simpa [validRow] using hq
      simp only [List.zipWith_cons_cons, List.map_cons,
        fractionValue_add a b hp'.1 hq'.1, ih q hp'.2 hq'.2]

theorem add_valid (p q : List (List Fraction)) (hp : valid p = true)
    (hq : valid q = true) : valid (add p q) = true := by
  induction p generalizing q with
  | nil => simp [valid, add]
  | cons a p ih =>
    cases q with
    | nil => simp [valid, add]
    | cons b q =>
      have hp' : validRow a = true ∧ valid p = true := by simpa [valid] using hp
      have hq' : validRow b = true ∧ valid q = true := by simpa [valid] using hq
      simpa only [add, List.zipWith_cons_cons, valid, List.all_cons, Bool.and_eq_true]
        using And.intro (row_add_valid a b hp'.1 hq'.1) (ih q hp'.2 hq'.2)

theorem add_value (p q : List (List Fraction)) (hp : valid p = true)
    (hq : valid q = true) : realCoefficients (add p q) =
      realMatrixAdd (realCoefficients p) (realCoefficients q) := by
  induction p generalizing q with
  | nil => simp [add, realCoefficients, realMatrixAdd]
  | cons a p ih =>
    cases q with
    | nil => simp [add, realCoefficients, realMatrixAdd]
    | cons b q =>
      have hp' : validRow a = true ∧ valid p = true := by simpa [valid] using hp
      have hq' : validRow b = true ∧ valid q = true := by simpa [valid] using hq
      simpa only [add, realCoefficients, realMatrixAdd, List.zipWith_cons_cons, List.map_cons,
        row_add_value a b hp'.1 hq'.1] using
          congrArg (List.cons ((a.map fractionValue).zipWith (· + ·) (b.map fractionValue)))
            (ih q hp'.2 hq'.2)

theorem scale_valid (c : Fraction) (p : List (List Fraction))
    (hc : 0 < c.den) (hp : valid p = true) : valid (scale c p) = true := by
  have hp' : ∀ row ∈ p, ∀ a ∈ row, 0 < a.den := by
    simpa [valid, validRow] using hp
  simp only [valid, scale, List.all_map, validRow, List.all_eq_true,
    decide_eq_true_eq, Function.comp_def]
  intro row hr a ha
  exact fraction_mul_den_pos c a hc (hp' row hr a ha)

theorem scale_value (c : Fraction) (p : List (List Fraction))
    (hc : 0 < c.den) (hp : valid p = true) :
    realCoefficients (scale c p) = realMatrixScale (fractionValue c) (realCoefficients p) := by
  have hp' : ∀ row ∈ p, ∀ a ∈ row, 0 < a.den := by simpa [valid, validRow] using hp
  simp only [realCoefficients, scale, realMatrixScale, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro row hr
  apply List.map_congr_left
  intro a ha
  exact fractionValue_mul c a hc (hp' row hr a ha)

end CoefficientMatrix

inductive CoefficientExpr where
  | matrix : List (List Fraction) → CoefficientExpr
  | add : CoefficientExpr → CoefficientExpr → CoefficientExpr
  | scale : Fraction → CoefficientExpr → CoefficientExpr

namespace CoefficientExpr

def valid : CoefficientExpr → Bool
  | .matrix p => CoefficientMatrix.valid p
  | .add a b => a.valid && b.valid
  | .scale c a => (0 < c.den) && a.valid

def normalize : CoefficientExpr → List (List Fraction)
  | .matrix p => p
  | .add a b => CoefficientMatrix.add a.normalize b.normalize
  | .scale c a => CoefficientMatrix.scale c a.normalize

noncomputable def value : CoefficientExpr → List (List ℝ)
  | .matrix p => realCoefficients p
  | .add a b => realMatrixAdd a.value b.value
  | .scale c a => realMatrixScale (fractionValue c) a.value

theorem normalize_valid (e : CoefficientExpr) (h : e.valid = true) :
    CoefficientMatrix.valid e.normalize = true := by
  induction e with
  | matrix p => exact h
  | add a b ia ib =>
      have hh : a.valid = true ∧ b.valid = true := by simpa [valid] using h
      exact CoefficientMatrix.add_valid _ _ (ia hh.1) (ib hh.2)
  | scale c a ia =>
      have hh : 0 < c.den ∧ a.valid = true := by simpa [valid] using h
      exact CoefficientMatrix.scale_valid _ _ hh.1 (ia hh.2)

theorem normalize_value (e : CoefficientExpr) (h : e.valid = true) :
    realCoefficients e.normalize = e.value := by
  induction e with
  | matrix p => rfl
  | add a b ia ib =>
      have hh : a.valid = true ∧ b.valid = true := by simpa [valid] using h
      exact (CoefficientMatrix.add_value _ _ (a.normalize_valid hh.1)
        (b.normalize_valid hh.2)).trans (congrArg₂ realMatrixAdd (ia hh.1) (ib hh.2))
  | scale c a ia =>
      have hh : 0 < c.den ∧ a.valid = true := by simpa [valid] using h
      exact (CoefficientMatrix.scale_value _ _ hh.1 (a.normalize_valid hh.2)).trans
        (congrArg (realMatrixScale (fractionValue c)) (ia hh.2))

def check (a b : CoefficientExpr) : Bool :=
  a.valid && b.valid && matrixEq a.normalize b.normalize

theorem check_sound (a b : CoefficientExpr) (h : check a b = true) : a.value = b.value := by
  have hh : (a.valid = true ∧ b.valid = true) ∧ matrixEq a.normalize b.normalize = true := by
    simpa [check] using h
  rw [← normalize_value a hh.1.1, ← normalize_value b hh.1.2]
  exact matrixEq_sound _ _ hh.2

end CoefficientExpr
end F4Heavy.Analysis
