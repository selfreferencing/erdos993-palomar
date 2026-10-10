module

public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerInterval0Tables
public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerIntervalLower

/-! Checked integer clearing recovers the unchanged original interval0 identity predicate. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.GHeavyB3

theorem integer_interval0_source :
    interval0.coeffs = IUni.ratioRow M interval0SourceNumInt interval0SourceDenInt := by rfl

theorem integer_interval0_guards :
    interval0DenInt ≠ 0 ∧ interval0ChartDenInt ≠ 0 ∧
    interval0.lo = (interval0ChartAInt : Rat)/(interval0ChartDenInt : Rat) ∧
    interval0.hi-interval0.lo = (interval0ChartBInt : Rat)/(interval0ChartDenInt : Rat) := by
  decide +kernel

theorem integer_interval0_den_ne_zero : interval0DenInt ≠ 0 := integer_interval0_guards.1

theorem integer_interval0_fraction_checks :
    (List.range (M+1)).all (fun j =>
      decide (interval0SourceDenInt.getD j 1 ≠ 0) &&
      decide (interval0SourceNumInt.getD j 0 * interval0DenInt = interval0CoeffInt.getD j 0 * interval0SourceDenInt.getD j 1)) = true := by
  decide +kernel

theorem integer_interval0_coefficients : ∀ j < M+1,
    (interval0.coeffs).getD j 0 = (interval0CoeffInt.getD j 0 : Rat)/(interval0DenInt : Rat) := by
  apply IUni.ratioRow_coeffs M (interval0.coeffs) interval0SourceNumInt interval0SourceDenInt interval0CoeffInt interval0DenInt integer_interval0_source
    integer_interval0_den_ne_zero
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval0_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval0_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

theorem integer_interval0_bern_calc :
    IUni.cachedBernVector M basisInt interval0CoeffInt = interval0BernInt := by
  decide +kernel

theorem integer_interval0_bern_checked :
    Uni.bernVector M (interval0.coeffs) =
      Uni.scale ((1 : Rat)/(interval0DenInt : Rat)) (IUni.castRat interval0BernInt) := by
  have hcoeff : ∀ j < M+1, (interval0.coeffs).getD j 0 =
      ((1 : Rat)/(interval0DenInt : Rat)) * (interval0CoeffInt.getD j 0 : Rat) := by
    intro j hj
    rw [integer_interval0_coefficients j hj]
    simp only [div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  have h := Uni.bernVector_eq_intCached M (interval0.coeffs) basisInt interval0CoeffInt
    ((1 : Rat)/(interval0DenInt : Rat)) integer_basis_checked hcoeff
  rw [integer_interval0_bern_calc] at h
  exact h

theorem integer_interval0_composition_calc :
    IUni.affineHom intervalLowerBernInt interval0ChartAInt interval0ChartBInt
      interval0ChartDenInt M = interval0CompositionInt := by decide +kernel

theorem integer_interval0_clear_check :
    IUni.checkEq
      (IUni.scale interval0DenInt interval0CompositionInt)
      (IUni.scale (intervalLowerDenInt * interval0ChartPowerDenInt) interval0BernInt) = true := by
  decide +kernel

theorem integer_interval0_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [interval0.lo, interval0.hi-interval0.lo])
      (Uni.bernVector M interval0.coeffs) = true := by
  have hChart := IUni.composition_eq_integer
    (IUni.castRat intervalLowerBernInt) intervalLowerBernInt interval0.lo (interval0.hi-interval0.lo)
    interval0ChartAInt interval0ChartBInt interval0ChartDenInt M interval0CompositionInt
    rfl integer_interval_lower_guards.2 integer_interval0_guards.2.1
    integer_interval0_guards.2.2.1 integer_interval0_guards.2.2.2 integer_interval0_composition_calc
  have hChartDen : interval0ChartPowerDenInt ≠ 0 :=
    pow_ne_zero _ integer_interval0_guards.2.1
  exact Uni.interval_identity_of_integer_clear M lower interval0
    intervalLowerBernInt interval0CompositionInt interval0BernInt
    intervalLowerDenInt interval0ChartPowerDenInt interval0DenInt
    integer_interval_lower_den_ne_zero hChartDen integer_interval0_den_ne_zero
    integer_interval_lower_bern_checked hChart integer_interval0_bern_checked integer_interval0_clear_check

#print axioms integer_interval0_source
#print axioms integer_interval0_guards
#print axioms integer_interval0_fraction_checks
#print axioms integer_interval0_bern_calc
#print axioms integer_interval0_bern_checked
#print axioms integer_interval0_composition_calc
#print axioms integer_interval0_clear_check
#print axioms integer_interval0_identity
end Erdos993Lean.BCFG.CertData.GHeavyB3
