module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerArithmetic

/-!
Generic integer expression checker. Each operation carries a reduced
fraction witness. The checker uses only Int/Nat arithmetic, and its
soundness theorem gives the complete real interpretation of the tree.
No generated record is invoked here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

instance lowMeanFractionValidDecidable (x : lowMeanFraction) : Decidable (lowMeanFractionValid x) :=
  inferInstanceAs (Decidable (0 < x.2))
instance lowMeanFractionEqDecidable (x y : lowMeanFraction) : Decidable (lowMeanFractionEq x y) :=
  inferInstanceAs (Decidable (x.1 * (y.2 : ℤ) = y.1 * (x.2 : ℤ)))
instance lowMeanFractionLEDecidable (x y : lowMeanFraction) : Decidable (lowMeanFractionLE x y) :=
  inferInstanceAs (Decidable (x.1 * (y.2 : ℤ) ≤ y.1 * (x.2 : ℤ)))
instance lowMeanFractionLTDecidable (x y : lowMeanFraction) : Decidable (lowMeanFractionLT x y) :=
  inferInstanceAs (Decidable (x.1 * (y.2 : ℤ) < y.1 * (x.2 : ℤ)))

inductive LowMeanIntegerExpr where
  | atom (value : lowMeanFraction)
  | add (value : lowMeanFraction) (left right : LowMeanIntegerExpr)
  | neg (value : lowMeanFraction) (arg : LowMeanIntegerExpr)
  | mul (value : lowMeanFraction) (left right : LowMeanIntegerExpr)
  | div (value : lowMeanFraction) (left right : LowMeanIntegerExpr)
  | pow (value : lowMeanFraction) (arg : LowMeanIntegerExpr) (exponent : ℕ)
  | abs (value : lowMeanFraction) (arg : LowMeanIntegerExpr)
  | minimum (value : lowMeanFraction) (left right : LowMeanIntegerExpr)
  | maximum (value : lowMeanFraction) (left right : LowMeanIntegerExpr)
  | selectLE (value : lowMeanFraction) (left right yes no : LowMeanIntegerExpr)
  | selectLT (value : lowMeanFraction) (left right yes no : LowMeanIntegerExpr)

def lowMeanIntegerExprValue : LowMeanIntegerExpr → lowMeanFraction
  | .atom x => x
  | .add x _ _ => x
  | .neg x _ => x
  | .mul x _ _ => x
  | .div x _ _ => x
  | .pow x _ _ => x
  | .abs x _ => x
  | .minimum x _ _ => x
  | .maximum x _ _ => x
  | .selectLE x _ _ _ _ => x
  | .selectLT x _ _ _ _ => x

noncomputable def lowMeanIntegerExprReal : LowMeanIntegerExpr → ℝ
  | .atom x => lowMeanFractionReal x
  | .add _ x y => lowMeanIntegerExprReal x + lowMeanIntegerExprReal y
  | .neg _ x => -lowMeanIntegerExprReal x
  | .mul _ x y => lowMeanIntegerExprReal x * lowMeanIntegerExprReal y
  | .div _ x y => lowMeanIntegerExprReal x / lowMeanIntegerExprReal y
  | .pow _ x n => lowMeanIntegerExprReal x ^ n
  | .abs _ x => |lowMeanIntegerExprReal x|
  | .minimum _ x y => min (lowMeanIntegerExprReal x) (lowMeanIntegerExprReal y)
  | .maximum _ x y => max (lowMeanIntegerExprReal x) (lowMeanIntegerExprReal y)
  | .selectLE _ x y yes no =>
      if lowMeanIntegerExprReal x ≤ lowMeanIntegerExprReal y then lowMeanIntegerExprReal yes else lowMeanIntegerExprReal no
  | .selectLT _ x y yes no =>
      if lowMeanIntegerExprReal x < lowMeanIntegerExprReal y then lowMeanIntegerExprReal yes else lowMeanIntegerExprReal no

def lowMeanIntegerExprCheck : LowMeanIntegerExpr → Bool
  | .atom x => decide (lowMeanFractionValid x)
  | .add z x y => lowMeanIntegerExprCheck x && lowMeanIntegerExprCheck y &&
      decide (lowMeanFractionValid z ∧ lowMeanFractionEq z
        (lowMeanFractionAdd (lowMeanIntegerExprValue x) (lowMeanIntegerExprValue y)))
  | .neg z x => lowMeanIntegerExprCheck x && decide (lowMeanFractionValid z ∧
      lowMeanFractionEq z (lowMeanFractionNeg (lowMeanIntegerExprValue x)))
  | .mul z x y => lowMeanIntegerExprCheck x && lowMeanIntegerExprCheck y &&
      decide (lowMeanFractionValid z ∧ lowMeanFractionEq z
        (lowMeanFractionMul (lowMeanIntegerExprValue x) (lowMeanIntegerExprValue y)))
  | .div z x y => lowMeanIntegerExprCheck x && lowMeanIntegerExprCheck y &&
      decide (lowMeanFractionValid z ∧ (lowMeanIntegerExprValue y).1 ≠ 0 ∧
        lowMeanFractionEq (lowMeanFractionMul z (lowMeanIntegerExprValue y)) (lowMeanIntegerExprValue x))
  | .pow z x n => lowMeanIntegerExprCheck x && decide (lowMeanFractionValid z ∧
      lowMeanFractionEq z (lowMeanFractionPow (lowMeanIntegerExprValue x) n))
  | .abs z x => lowMeanIntegerExprCheck x && decide (lowMeanFractionValid z ∧
      lowMeanFractionEq z (lowMeanFractionAbs (lowMeanIntegerExprValue x)))
  | .minimum z x y => lowMeanIntegerExprCheck x && lowMeanIntegerExprCheck y &&
      decide (lowMeanFractionValid z ∧ lowMeanFractionEq z
        (if lowMeanFractionLE (lowMeanIntegerExprValue x) (lowMeanIntegerExprValue y)
          then lowMeanIntegerExprValue x else lowMeanIntegerExprValue y))
  | .maximum z x y => lowMeanIntegerExprCheck x && lowMeanIntegerExprCheck y &&
      decide (lowMeanFractionValid z ∧ lowMeanFractionEq z
        (if lowMeanFractionLE (lowMeanIntegerExprValue x) (lowMeanIntegerExprValue y)
          then lowMeanIntegerExprValue y else lowMeanIntegerExprValue x))
  | .selectLE z x y yes no => lowMeanIntegerExprCheck x && lowMeanIntegerExprCheck y &&
      decide (lowMeanFractionValid z) &&
      (if lowMeanFractionLE (lowMeanIntegerExprValue x) (lowMeanIntegerExprValue y)
        then lowMeanIntegerExprCheck yes && decide (lowMeanFractionEq z (lowMeanIntegerExprValue yes))
        else lowMeanIntegerExprCheck no && decide (lowMeanFractionEq z (lowMeanIntegerExprValue no)))
  | .selectLT z x y yes no => lowMeanIntegerExprCheck x && lowMeanIntegerExprCheck y &&
      decide (lowMeanFractionValid z) &&
      (if lowMeanFractionLT (lowMeanIntegerExprValue x) (lowMeanIntegerExprValue y)
        then lowMeanIntegerExprCheck yes && decide (lowMeanFractionEq z (lowMeanIntegerExprValue yes))
        else lowMeanIntegerExprCheck no && decide (lowMeanFractionEq z (lowMeanIntegerExprValue no)))

/-- Every accepted expression denotes exactly the fraction in its root.
The operation witnesses and every denominator are checked by the kernel. -/
theorem lowMean_integerExpr_sound (e : LowMeanIntegerExpr) (h : lowMeanIntegerExprCheck e = true) :
    lowMeanFractionValid (lowMeanIntegerExprValue e) ∧
      lowMeanIntegerExprReal e = lowMeanFractionReal (lowMeanIntegerExprValue e) := by
  induction e with
  | atom x =>
    simpa only [lowMeanIntegerExprCheck, decide_eq_true_eq, lowMeanIntegerExprValue,
      lowMeanIntegerExprReal, and_true] using h
  | add z x y ihx ihy =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hy⟩, hz, he⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    obtain ⟨hvy, hsy⟩ := ihy hy
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, hsy]
    exact (lowMean_fraction_add_witness hvx hvy hz he).symm
  | neg z x ihx =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hx, hz, he⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    have hv : lowMeanFractionValid (lowMeanFractionNeg (lowMeanIntegerExprValue x)) := hvx
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, ← lowMean_fraction_neg]
    exact ((lowMean_fraction_eq_iff hz hv).mp he).symm
  | mul z x y ihx ihy =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hy⟩, hz, he⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    obtain ⟨hvy, hsy⟩ := ihy hy
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, hsy]
    exact (lowMean_fraction_mul_witness hvx hvy hz he).symm
  | div z x y ihx ihy =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hy⟩, hz, hy0, he⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    obtain ⟨hvy, hsy⟩ := ihy hy
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, hsy]
    exact (lowMean_fraction_div_witness hvx hvy hz hy0 he).symm
  | pow z x n ihx =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hx, hz, he⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    have hv : lowMeanFractionValid (lowMeanFractionPow (lowMeanIntegerExprValue x) n) := pow_pos hvx n
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, ← lowMean_fraction_pow]
    exact ((lowMean_fraction_eq_iff hz hv).mp he).symm
  | abs z x ihx =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hx, hz, he⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    have hv : lowMeanFractionValid (lowMeanFractionAbs (lowMeanIntegerExprValue x)) := hvx
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, ← lowMean_fraction_abs]
    exact ((lowMean_fraction_eq_iff hz hv).mp he).symm
  | minimum z x y ihx ihy =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hy⟩, hz, he⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    obtain ⟨hvy, hsy⟩ := ihy hy
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, hsy]
    split_ifs at he with hxy
    · rw [min_eq_left ((lowMean_fraction_le_iff hvx hvy).mp hxy)]
      exact ((lowMean_fraction_eq_iff hz hvx).mp he).symm
    · have hxyR : lowMeanFractionReal (lowMeanIntegerExprValue y) ≤
        lowMeanFractionReal (lowMeanIntegerExprValue x) := le_of_not_ge (mt (lowMean_fraction_le_iff hvx hvy).mpr hxy)
      rw [min_eq_right hxyR]
      exact ((lowMean_fraction_eq_iff hz hvy).mp he).symm
  | maximum z x y ihx ihy =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hy⟩, hz, he⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    obtain ⟨hvy, hsy⟩ := ihy hy
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, hsy]
    split_ifs at he with hxy
    · rw [max_eq_right ((lowMean_fraction_le_iff hvx hvy).mp hxy)]
      exact ((lowMean_fraction_eq_iff hz hvy).mp he).symm
    · have hxyR : lowMeanFractionReal (lowMeanIntegerExprValue y) ≤
        lowMeanFractionReal (lowMeanIntegerExprValue x) := le_of_not_ge (mt (lowMean_fraction_le_iff hvx hvy).mpr hxy)
      rw [max_eq_left hxyR]
      exact ((lowMean_fraction_eq_iff hz hvx).mp he).symm
  | selectLE z x y yes no ihx ihy ihyes ihno =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hx, hy⟩, hz⟩, hc⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    obtain ⟨hvy, hsy⟩ := ihy hy
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, hsy]
    split_ifs at hc with hxy
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hyes, he⟩ := hc
      obtain ⟨hvyes, hsyes⟩ := ihyes hyes
      rw [ite_eq_left ((lowMean_fraction_le_iff hvx hvy).mp hxy), hsyes]
      exact ((lowMean_fraction_eq_iff hz hvyes).mp he).symm
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hno, he⟩ := hc
      obtain ⟨hvno, hsno⟩ := ihno hno
      rw [ite_eq_right (mt (lowMean_fraction_le_iff hvx hvy).mpr hxy), hsno]
      exact ((lowMean_fraction_eq_iff hz hvno).mp he).symm
  | selectLT z x y yes no ihx ihy ihyes ihno =>
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hx, hy⟩, hz⟩, hc⟩ := h
    obtain ⟨hvx, hsx⟩ := ihx hx
    obtain ⟨hvy, hsy⟩ := ihy hy
    refine ⟨hz, ?_⟩
    dsimp only [lowMeanIntegerExprReal, lowMeanIntegerExprValue]
    rw [hsx, hsy]
    split_ifs at hc with hxy
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hyes, he⟩ := hc
      obtain ⟨hvyes, hsyes⟩ := ihyes hyes
      rw [ite_eq_left ((lowMean_fraction_lt_iff hvx hvy).mp hxy), hsyes]
      exact ((lowMean_fraction_eq_iff hz hvyes).mp he).symm
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hno, he⟩ := hc
      obtain ⟨hvno, hsno⟩ := ihno hno
      rw [ite_eq_right (mt (lowMean_fraction_lt_iff hvx hvy).mpr hxy), hsno]
      exact ((lowMean_fraction_eq_iff hz hvno).mp he).symm

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_integerExpr_sound
