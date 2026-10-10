module

public import Erdos993Lean.Analytic.V213.LowMeanRational
public import Erdos993Lean.F4Fast.RangeAll

/-!
Arithmetic infrastructure: explicit signed numerators and positive
natural denominators. Cross multiplication checks are interpreted in the
reals. Reduced result witnesses prevent denominator growth; no large Rat
evaluation, generated family invocation, or new trusted primitive is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

@[reducible] def lowMeanFraction := ℤ × ℕ
noncomputable def lowMeanFractionReal (x : lowMeanFraction) : ℝ := (x.1 : ℝ) / x.2
def lowMeanFractionValid (x : lowMeanFraction) : Prop := 0 < x.2
def lowMeanFractionEq (x y : lowMeanFraction) : Prop := x.1 * (y.2 : ℤ) = y.1 * (x.2 : ℤ)
def lowMeanFractionLE (x y : lowMeanFraction) : Prop := x.1 * (y.2 : ℤ) ≤ y.1 * (x.2 : ℤ)
def lowMeanFractionLT (x y : lowMeanFraction) : Prop := x.1 * (y.2 : ℤ) < y.1 * (x.2 : ℤ)
def lowMeanFractionAdd (x y : lowMeanFraction) : lowMeanFraction :=
  (x.1 * y.2 + y.1 * x.2, x.2 * y.2)
def lowMeanFractionNeg (x : lowMeanFraction) : lowMeanFraction := (-x.1, x.2)
def lowMeanFractionMul (x y : lowMeanFraction) : lowMeanFraction := (x.1 * y.1, x.2 * y.2)
def lowMeanFractionPow (x : lowMeanFraction) (n : ℕ) : lowMeanFraction := (x.1 ^ n, x.2 ^ n)
def lowMeanFractionAbs (x : lowMeanFraction) : lowMeanFraction := (|x.1|, x.2)

theorem lowMean_fraction_den_pos {x : lowMeanFraction} (hx : lowMeanFractionValid x) :
    (0 : ℝ) < x.2 := by exact_mod_cast hx

theorem lowMean_fraction_eq_iff {x y : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) :
    lowMeanFractionEq x y ↔ lowMeanFractionReal x = lowMeanFractionReal y := by
  unfold lowMeanFractionEq lowMeanFractionReal
  rw [div_eq_div_iff (lowMean_fraction_den_pos hx).ne' (lowMean_fraction_den_pos hy).ne']
  norm_cast

theorem lowMean_fraction_le_iff {x y : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) :
    lowMeanFractionLE x y ↔ lowMeanFractionReal x ≤ lowMeanFractionReal y := by
  unfold lowMeanFractionLE lowMeanFractionReal
  rw [div_le_div_iff₀ (lowMean_fraction_den_pos hx) (lowMean_fraction_den_pos hy)]
  norm_cast

theorem lowMean_fraction_lt_iff {x y : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) :
    lowMeanFractionLT x y ↔ lowMeanFractionReal x < lowMeanFractionReal y := by
  unfold lowMeanFractionLT lowMeanFractionReal
  rw [div_lt_div_iff₀ (lowMean_fraction_den_pos hx) (lowMean_fraction_den_pos hy)]
  norm_cast

theorem lowMean_fraction_add {x y : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) :
    lowMeanFractionReal (lowMeanFractionAdd x y) = lowMeanFractionReal x + lowMeanFractionReal y := by
  have hd1 := (lowMean_fraction_den_pos hx).ne'
  have hd2 := (lowMean_fraction_den_pos hy).ne'
  unfold lowMeanFractionReal lowMeanFractionAdd
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp

theorem lowMean_fraction_neg (x : lowMeanFraction) :
    lowMeanFractionReal (lowMeanFractionNeg x) = -lowMeanFractionReal x := by
  simp [lowMeanFractionReal, lowMeanFractionNeg, neg_div]

theorem lowMean_fraction_mul (x y : lowMeanFraction) :
    lowMeanFractionReal (lowMeanFractionMul x y) = lowMeanFractionReal x * lowMeanFractionReal y := by
  simp [lowMeanFractionReal, lowMeanFractionMul, div_mul_div_comm]

theorem lowMean_fraction_pow (x : lowMeanFraction) (n : ℕ) :
    lowMeanFractionReal (lowMeanFractionPow x n) = lowMeanFractionReal x ^ n := by
  simp [lowMeanFractionReal, lowMeanFractionPow, div_pow]

theorem lowMean_fraction_abs (x : lowMeanFraction) :
    lowMeanFractionReal (lowMeanFractionAbs x) = |lowMeanFractionReal x| := by
  simp [lowMeanFractionReal, lowMeanFractionAbs, abs_div]

/-- A reduced arithmetic witness is checked only by integer products. -/
theorem lowMean_fraction_add_witness {x y z : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) (hz : lowMeanFractionValid z)
    (hcheck : lowMeanFractionEq z (lowMeanFractionAdd x y)) :
    lowMeanFractionReal z = lowMeanFractionReal x + lowMeanFractionReal y := by
  have hxy : lowMeanFractionValid (lowMeanFractionAdd x y) := Nat.mul_pos hx hy
  exact ((lowMean_fraction_eq_iff hz hxy).mp hcheck).trans (lowMean_fraction_add hx hy)

theorem lowMean_fraction_mul_witness {x y z : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) (hz : lowMeanFractionValid z)
    (hcheck : lowMeanFractionEq z (lowMeanFractionMul x y)) :
    lowMeanFractionReal z = lowMeanFractionReal x * lowMeanFractionReal y := by
  have hxy : lowMeanFractionValid (lowMeanFractionMul x y) := Nat.mul_pos hx hy
  exact ((lowMean_fraction_eq_iff hz hxy).mp hcheck).trans (lowMean_fraction_mul x y)

theorem lowMean_fraction_div_witness {x y z : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) (hz : lowMeanFractionValid z)
    (hy0 : y.1 ≠ 0) (hcheck : lowMeanFractionEq (lowMeanFractionMul z y) x) :
    lowMeanFractionReal z = lowMeanFractionReal x / lowMeanFractionReal y := by
  have hyR : lowMeanFractionReal y ≠ 0 := by
    unfold lowMeanFractionReal
    exact div_ne_zero (by exact_mod_cast hy0) (lowMean_fraction_den_pos hy).ne'
  apply (eq_div_iff hyR).mpr
  rw [← lowMean_fraction_mul]
  have hzy : lowMeanFractionValid (lowMeanFractionMul z y) := Nat.mul_pos hz hy
  exact (lowMean_fraction_eq_iff hzy hx).mp hcheck

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_fraction_eq_iff
#print axioms Erdos993Lean.Analytic.V213.lowMean_fraction_le_iff
#print axioms Erdos993Lean.Analytic.V213.lowMean_fraction_add_witness
#print axioms Erdos993Lean.Analytic.V213.lowMean_fraction_div_witness
