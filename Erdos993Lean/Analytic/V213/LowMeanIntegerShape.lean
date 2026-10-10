module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr

/-!
Arithmetic syntax bridge. Erasing result witnesses leaves the exact
formula tree, so an integer check proves a specified mathematical formula,
not merely positivity of an unrelated fraction. Group soundness uses the
range-all bridge. No finite family is invoked here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

instance lowMeanFractionDecidableEq : DecidableEq lowMeanFraction :=
  inferInstanceAs (DecidableEq (ℤ × ℕ))

inductive LowMeanIntegerShape where
  | atom (value : lowMeanFraction)
  | add (left right : LowMeanIntegerShape)
  | neg (arg : LowMeanIntegerShape)
  | mul (left right : LowMeanIntegerShape)
  | div (left right : LowMeanIntegerShape)
  | pow (arg : LowMeanIntegerShape) (exponent : ℕ)
  | abs (arg : LowMeanIntegerShape)
  | minimum (left right : LowMeanIntegerShape)
  | maximum (left right : LowMeanIntegerShape)
  | selectLE (left right yes no : LowMeanIntegerShape)
  | selectLT (left right yes no : LowMeanIntegerShape)
  deriving DecidableEq

def lowMeanIntegerExprErase : LowMeanIntegerExpr → LowMeanIntegerShape
  | .atom x => .atom x
  | .add _ x y => .add (lowMeanIntegerExprErase x) (lowMeanIntegerExprErase y)
  | .neg _ x => .neg (lowMeanIntegerExprErase x)
  | .mul _ x y => .mul (lowMeanIntegerExprErase x) (lowMeanIntegerExprErase y)
  | .div _ x y => .div (lowMeanIntegerExprErase x) (lowMeanIntegerExprErase y)
  | .pow _ x n => .pow (lowMeanIntegerExprErase x) n
  | .abs _ x => .abs (lowMeanIntegerExprErase x)
  | .minimum _ x y => .minimum (lowMeanIntegerExprErase x) (lowMeanIntegerExprErase y)
  | .maximum _ x y => .maximum (lowMeanIntegerExprErase x) (lowMeanIntegerExprErase y)
  | .selectLE _ x y yes no => .selectLE (lowMeanIntegerExprErase x) (lowMeanIntegerExprErase y)
      (lowMeanIntegerExprErase yes) (lowMeanIntegerExprErase no)
  | .selectLT _ x y yes no => .selectLT (lowMeanIntegerExprErase x) (lowMeanIntegerExprErase y)
      (lowMeanIntegerExprErase yes) (lowMeanIntegerExprErase no)

noncomputable def lowMeanIntegerShapeReal : LowMeanIntegerShape → ℝ
  | .atom x => lowMeanFractionReal x
  | .add x y => lowMeanIntegerShapeReal x + lowMeanIntegerShapeReal y
  | .neg x => -lowMeanIntegerShapeReal x
  | .mul x y => lowMeanIntegerShapeReal x * lowMeanIntegerShapeReal y
  | .div x y => lowMeanIntegerShapeReal x / lowMeanIntegerShapeReal y
  | .pow x n => lowMeanIntegerShapeReal x ^ n
  | .abs x => |lowMeanIntegerShapeReal x|
  | .minimum x y => min (lowMeanIntegerShapeReal x) (lowMeanIntegerShapeReal y)
  | .maximum x y => max (lowMeanIntegerShapeReal x) (lowMeanIntegerShapeReal y)
  | .selectLE x y yes no => if lowMeanIntegerShapeReal x ≤ lowMeanIntegerShapeReal y
      then lowMeanIntegerShapeReal yes else lowMeanIntegerShapeReal no
  | .selectLT x y yes no => if lowMeanIntegerShapeReal x < lowMeanIntegerShapeReal y
      then lowMeanIntegerShapeReal yes else lowMeanIntegerShapeReal no

theorem lowMean_integerShape_erase (e : LowMeanIntegerExpr) :
    lowMeanIntegerShapeReal (lowMeanIntegerExprErase e) = lowMeanIntegerExprReal e := by
  induction e <;> simp_all [lowMeanIntegerShapeReal, lowMeanIntegerExprErase, lowMeanIntegerExprReal]

def lowMeanIntegerShapeCheck (e : LowMeanIntegerExpr) (s : LowMeanIntegerShape) : Bool :=
  lowMeanIntegerExprCheck e && decide (lowMeanIntegerExprErase e = s)

theorem lowMean_integerShape_sound {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape}
    (h : lowMeanIntegerShapeCheck e s = true) :
    lowMeanFractionValid (lowMeanIntegerExprValue e) ∧
      lowMeanIntegerShapeReal s = lowMeanFractionReal (lowMeanIntegerExprValue e) := by
  simp only [lowMeanIntegerShapeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hs⟩ := lowMean_integerExpr_sound e h.1
  exact ⟨hv, by rw [← h.2, lowMean_integerShape_erase, hs]⟩

def lowMeanIntegerPositiveCheck (e : LowMeanIntegerExpr) (s : LowMeanIntegerShape)
    (bound : lowMeanFraction) : Bool :=
  lowMeanIntegerShapeCheck e s && decide (lowMeanFractionValid bound ∧
    lowMeanFractionLT bound (lowMeanIntegerExprValue e))

theorem lowMean_integerPositive_sound {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape}
    {bound : lowMeanFraction} (h : lowMeanIntegerPositiveCheck e s bound = true) :
    lowMeanFractionReal bound < lowMeanIntegerShapeReal s := by
  simp only [lowMeanIntegerPositiveCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hs⟩ := lowMean_integerShape_sound h.1
  rw [hs]
  exact (lowMean_fraction_lt_iff h.2.1 hv).mp h.2.2

/-- The required grouped proof route: a single kernel range-all evaluation
provides every exact formula inequality in its frozen group. -/
theorem lowMean_integer_group_sound {n : ℕ}
    (expressions : ℕ → LowMeanIntegerExpr) (shapes : ℕ → LowMeanIntegerShape)
    (bounds : ℕ → lowMeanFraction)
    (h : (List.range n).all (fun i => lowMeanIntegerPositiveCheck (expressions i) (shapes i) (bounds i)) = true) :
    ∀ i < n, lowMeanFractionReal (bounds i) < lowMeanIntegerShapeReal (shapes i) := by
  intro i hi
  exact lowMean_integerPositive_sound (Erdos993Lean.F4Fast.forall_lt_of_range_all h i hi)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_integerShape_sound
#print axioms Erdos993Lean.Analytic.V213.lowMean_integerPositive_sound
#print axioms Erdos993Lean.Analytic.V213.lowMean_integer_group_sound
