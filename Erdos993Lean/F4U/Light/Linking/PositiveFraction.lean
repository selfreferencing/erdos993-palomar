module
public import Erdos993Lean.F4U.Light.Linking.Rational
public import Erdos993Lean.F4U.Light.Construction.PrimitiveEvaluation
@[expose] public section
namespace F4U.Light.Linking
noncomputable section

/-- A checked literal numerator and the oriented actual denominator certify
one retained rational pair in its true activity coordinate. -/
theorem value_positive_of_numerator {F : F4U.Light.Fn} {p : RationalPair} {sign scale : Int}
    (hsign : sign=1 ∨ sign=(-1)) (hscale : 0 < scale)
    (hrows : F.rows.length ≤ F.m+1)
    (heq : Polynomial2.normalizedEq (Polynomial2.pscale sign p.numerator)
      (Polynomial2.pscale scale F.rows) = true)
    (hF : F4U.Light.NumeratorPositive F) {x t : ℝ}
    (hx : F4U.Light.ActivityInterval F x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hden : 0 < Polynomial2.eval (Polynomial2.pscale sign p.denominator)
      (F4U.Light.activityArg F x) t) :
    0 < p.value (F4U.Light.activityArg F x) t := by
  have he := Polynomial2.normalizedEq_sound heq (F4U.Light.activityArg F x) t
  rw [Polynomial2.eval_pscale,Polynomial2.eval_pscale,
    F4Unified.LightConstruction.polynomial2_eval_primitiveNumerator F hrows] at he
  have hc : (0:ℝ)<scale := by exact_mod_cast hscale
  have hn : 0 < Polynomial2.eval (Polynomial2.pscale sign p.numerator)
      (F4U.Light.activityArg F x) t := by
    rw [Polynomial2.eval_pscale,he]
    exact mul_pos hc (hF x t hx ht0 ht1)
  have hp := div_pos hn hden
  rcases hsign with rfl | rfl
  · simpa [Polynomial2.eval_pscale,RationalPair.value] using hp
  · simpa [Polynomial2.eval_pscale,RationalPair.value] using hp

#print axioms value_positive_of_numerator
end
end F4U.Light.Linking
