module

public import Erdos993Lean.Analytic.V213.FreeCountLogDispatch
public import Erdos993Lean.Analytic.V213.FreeCountCAChildlessPolynomials
public import Erdos993Lean.Analytic.V213.P03ScalarData.Fixed001
public import Erdos993Lean.Analytic.V213.P03ScalarData.LogDomains

/-! These are semantic casts and three actual Real
consequences of individually selected retained records. The logarithm guards
are the original checked logUseOK entries. No rational record is re-evaluated.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

open Real Envelopes PrintedScalarRecords
open Erdos993Lean.ExactComparisons

theorem expFive_cast (x : Rat) :
    (F3All.expFive x : ℝ) = expPartial 5 (x : ℝ) := by
  simp [F3All.expFive, expPartial, Finset.sum_range_succ, Nat.factorial]
  <;> ring

theorem nFour_cast (x D : Rat) :
    (F3All.nFour x D : ℝ) = childlessN4 (D : ℝ) (x : ℝ) := by
  simp [F3All.nFour, childlessN4]

theorem nFive_cast (x D : Rat) :
    (F3All.nFive x D : ℝ) = childlessN5 (D : ℝ) (x : ℝ) := by
  simp [F3All.nFive, childlessN5]

/-- F10, with its actual log-domain guard and actual Real envelope. -/
theorem log_369_80_lt : log (369/80 : ℝ) < 153/100 := by
  have he := (log_envelopes_of_useOK guard_log_domain0002).2
  have hf := fixed_F10
  have h := he.trans_lt hf
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- F11, likewise at the lower envelope. -/
theorem log_463_200_gt : (4/5 : ℝ) < log (463/200 : ℝ) := by
  have he := (log_envelopes_of_useOK guard_log_domain0003).1
  have h := fixed_F11.trans_le he
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- F12; the Padé theorem is used on its closed valid input interval. -/
theorem exp_five_fourths_lt_four : exp (5/4 : ℝ) < 4 := by
  have hf := fixed_F12
  rw [expUpper_cast] at hf
  push_cast at hf
  exact (exp_envelopes (y := (5/4 : ℝ)) (by norm_num) (by norm_num)).2.trans_lt hf

end Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.expFive_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.expFive_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.nFour_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.nFour_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.nFive_cast
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.nFive_cast
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.log_369_80_lt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.log_369_80_lt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.log_463_200_gt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.log_463_200_gt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.exp_five_fourths_lt_four
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.exp_five_fourths_lt_four
