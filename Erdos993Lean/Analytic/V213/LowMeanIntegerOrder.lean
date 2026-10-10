module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerShape

/-! Nonstrict and exact-value checks over the same explicit Int/Nat syntax. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanIntegerLowerCheck (e : LowMeanIntegerExpr) (s : LowMeanIntegerShape) (bound : lowMeanFraction) : Bool :=
  lowMeanIntegerShapeCheck e s && decide (lowMeanFractionValid bound ∧ lowMeanFractionLE bound (lowMeanIntegerExprValue e))
def lowMeanIntegerEqualityCheck (e : LowMeanIntegerExpr) (s : LowMeanIntegerShape) (value : lowMeanFraction) : Bool :=
  lowMeanIntegerShapeCheck e s && decide (lowMeanIntegerExprValue e = value)

theorem lowMean_integerLower_sound {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape} {bound : lowMeanFraction}
    (h : lowMeanIntegerLowerCheck e s bound = true) : lowMeanFractionReal bound ≤ lowMeanIntegerShapeReal s := by
  simp only [lowMeanIntegerLowerCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hs⟩ := lowMean_integerShape_sound h.1
  rw [hs]
  exact (lowMean_fraction_le_iff h.2.1 hv).mp h.2.2

theorem lowMean_integerEquality_sound {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape} {value : lowMeanFraction}
    (h : lowMeanIntegerEqualityCheck e s value = true) : lowMeanIntegerShapeReal s = lowMeanFractionReal value := by
  simp only [lowMeanIntegerEqualityCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hs⟩ := lowMean_integerShape_sound h.1
  exact hs.trans (congrArg lowMeanFractionReal h.2)

end Erdos993Lean.Analytic.V213
