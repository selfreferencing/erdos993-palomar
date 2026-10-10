module

public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerInterval11Tables
public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerIntervalLower

/-! Checked integer clearing recovers the unchanged original interval11 identity predicate. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.GHeavyB3

theorem integer_interval11_source :
    interval11.coeffs = IUni.ratioRow M interval11SourceNumInt interval11SourceDenInt := by rfl

theorem integer_interval11_guards :
    interval11DenInt ≠ 0 ∧ interval11ChartDenInt ≠ 0 ∧
    interval11.lo = (interval11ChartAInt : Rat)/(interval11ChartDenInt : Rat) ∧
    interval11.hi-interval11.lo = (interval11ChartBInt : Rat)/(interval11ChartDenInt : Rat) := by
  decide +kernel

theorem integer_interval11_den_ne_zero : interval11DenInt ≠ 0 := integer_interval11_guards.1

theorem integer_interval11_fraction_checks :
    (List.range (M+1)).all (fun j =>
      decide (interval11SourceDenInt.getD j 1 ≠ 0) &&
      decide (interval11SourceNumInt.getD j 0 * interval11DenInt = interval11CoeffInt.getD j 0 * interval11SourceDenInt.getD j 1)) = true := by
  decide +kernel

theorem integer_interval11_coefficients : ∀ j < M+1,
    (interval11.coeffs).getD j 0 = (interval11CoeffInt.getD j 0 : Rat)/(interval11DenInt : Rat) := by
  apply IUni.ratioRow_coeffs M (interval11.coeffs) interval11SourceNumInt interval11SourceDenInt interval11CoeffInt interval11DenInt integer_interval11_source
    integer_interval11_den_ne_zero
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval11_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval11_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

theorem integer_interval11_bern_calc :
    IUni.cachedBernVector M basisInt interval11CoeffInt = interval11BernInt := by
  decide +kernel

theorem integer_interval11_bern_checked :
    Uni.bernVector M (interval11.coeffs) =
      Uni.scale ((1 : Rat)/(interval11DenInt : Rat)) (IUni.castRat interval11BernInt) := by
  have hcoeff : ∀ j < M+1, (interval11.coeffs).getD j 0 =
      ((1 : Rat)/(interval11DenInt : Rat)) * (interval11CoeffInt.getD j 0 : Rat) := by
    intro j hj
    rw [integer_interval11_coefficients j hj]
    simp only [div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  have h := Uni.bernVector_eq_intCached M (interval11.coeffs) basisInt interval11CoeffInt
    ((1 : Rat)/(interval11DenInt : Rat)) integer_basis_checked hcoeff
  rw [integer_interval11_bern_calc] at h
  exact h

theorem integer_interval11_composition_calc :
    IUni.affineHom intervalLowerBernInt interval11ChartAInt interval11ChartBInt
      interval11ChartDenInt M = interval11CompositionInt := by decide +kernel

theorem integer_interval11_clear_check :
    IUni.checkEq
      (IUni.scale interval11DenInt interval11CompositionInt)
      (IUni.scale (intervalLowerDenInt * interval11ChartPowerDenInt) interval11BernInt) = true := by
  decide +kernel

theorem integer_interval11_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [interval11.lo, interval11.hi-interval11.lo])
      (Uni.bernVector M interval11.coeffs) = true := by
  have hChart := IUni.composition_eq_integer
    (IUni.castRat intervalLowerBernInt) intervalLowerBernInt interval11.lo (interval11.hi-interval11.lo)
    interval11ChartAInt interval11ChartBInt interval11ChartDenInt M interval11CompositionInt
    rfl integer_interval_lower_guards.2 integer_interval11_guards.2.1
    integer_interval11_guards.2.2.1 integer_interval11_guards.2.2.2 integer_interval11_composition_calc
  have hChartDen : interval11ChartPowerDenInt ≠ 0 :=
    pow_ne_zero _ integer_interval11_guards.2.1
  exact Uni.interval_identity_of_integer_clear M lower interval11
    intervalLowerBernInt interval11CompositionInt interval11BernInt
    intervalLowerDenInt interval11ChartPowerDenInt interval11DenInt
    integer_interval_lower_den_ne_zero hChartDen integer_interval11_den_ne_zero
    integer_interval_lower_bern_checked hChart integer_interval11_bern_checked integer_interval11_clear_check

#print axioms integer_interval11_source
#print axioms integer_interval11_guards
#print axioms integer_interval11_fraction_checks
#print axioms integer_interval11_bern_calc
#print axioms integer_interval11_bern_checked
#print axioms integer_interval11_composition_calc
#print axioms integer_interval11_clear_check
#print axioms integer_interval11_identity
end Erdos993Lean.BCFG.CertData.GHeavyB3
