module

public import Erdos993Lean.BCFG.Generated.FHeavyB3.IntegerInterval1Tables
public import Erdos993Lean.BCFG.Generated.FHeavyB3.IntegerIntervalLower

/-! Checked integer clearing recovers the unchanged original interval1 identity predicate. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.FHeavyB3

theorem integer_interval1_source :
    interval1.coeffs = IUni.ratioRow M interval1SourceNumInt interval1SourceDenInt := by rfl

theorem integer_interval1_guards :
    interval1DenInt ≠ 0 ∧ interval1ChartDenInt ≠ 0 ∧
    interval1.lo = (interval1ChartAInt : Rat)/(interval1ChartDenInt : Rat) ∧
    interval1.hi-interval1.lo = (interval1ChartBInt : Rat)/(interval1ChartDenInt : Rat) := by
  decide +kernel

theorem integer_interval1_den_ne_zero : interval1DenInt ≠ 0 := integer_interval1_guards.1

theorem integer_interval1_fraction_checks :
    (List.range (M+1)).all (fun j =>
      decide (interval1SourceDenInt.getD j 1 ≠ 0) &&
      decide (interval1SourceNumInt.getD j 0 * interval1DenInt = interval1CoeffInt.getD j 0 * interval1SourceDenInt.getD j 1)) = true := by
  decide +kernel

theorem integer_interval1_coefficients : ∀ j < M+1,
    (interval1.coeffs).getD j 0 = (interval1CoeffInt.getD j 0 : Rat)/(interval1DenInt : Rat) := by
  apply IUni.ratioRow_coeffs M (interval1.coeffs) interval1SourceNumInt interval1SourceDenInt interval1CoeffInt interval1DenInt integer_interval1_source
    integer_interval1_den_ne_zero
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval1_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval1_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

theorem integer_interval1_bern_calc :
    IUni.cachedBernVector M basisInt interval1CoeffInt = interval1BernInt := by
  decide +kernel

theorem integer_interval1_bern_checked :
    Uni.bernVector M (interval1.coeffs) =
      Uni.scale ((1 : Rat)/(interval1DenInt : Rat)) (IUni.castRat interval1BernInt) := by
  have hcoeff : ∀ j < M+1, (interval1.coeffs).getD j 0 =
      ((1 : Rat)/(interval1DenInt : Rat)) * (interval1CoeffInt.getD j 0 : Rat) := by
    intro j hj
    rw [integer_interval1_coefficients j hj]
    simp only [div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  have h := Uni.bernVector_eq_intCached M (interval1.coeffs) basisInt interval1CoeffInt
    ((1 : Rat)/(interval1DenInt : Rat)) integer_basis_checked hcoeff
  rw [integer_interval1_bern_calc] at h
  exact h

theorem integer_interval1_composition_calc :
    IUni.affineHom intervalLowerBernInt interval1ChartAInt interval1ChartBInt
      interval1ChartDenInt M = interval1CompositionInt := by decide +kernel

theorem integer_interval1_clear_check :
    IUni.checkEq
      (IUni.scale interval1DenInt interval1CompositionInt)
      (IUni.scale (intervalLowerDenInt * interval1ChartPowerDenInt) interval1BernInt) = true := by
  decide +kernel

theorem integer_interval1_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [interval1.lo, interval1.hi-interval1.lo])
      (Uni.bernVector M interval1.coeffs) = true := by
  have hChart := IUni.composition_eq_integer
    (IUni.castRat intervalLowerBernInt) intervalLowerBernInt interval1.lo (interval1.hi-interval1.lo)
    interval1ChartAInt interval1ChartBInt interval1ChartDenInt M interval1CompositionInt
    rfl integer_interval_lower_guards.2 integer_interval1_guards.2.1
    integer_interval1_guards.2.2.1 integer_interval1_guards.2.2.2 integer_interval1_composition_calc
  have hChartDen : interval1ChartPowerDenInt ≠ 0 :=
    pow_ne_zero _ integer_interval1_guards.2.1
  exact Uni.interval_identity_of_integer_clear M lower interval1
    intervalLowerBernInt interval1CompositionInt interval1BernInt
    intervalLowerDenInt interval1ChartPowerDenInt interval1DenInt
    integer_interval_lower_den_ne_zero hChartDen integer_interval1_den_ne_zero
    integer_interval_lower_bern_checked hChart integer_interval1_bern_checked integer_interval1_clear_check

#print axioms integer_interval1_source
#print axioms integer_interval1_guards
#print axioms integer_interval1_fraction_checks
#print axioms integer_interval1_bern_calc
#print axioms integer_interval1_bern_checked
#print axioms integer_interval1_composition_calc
#print axioms integer_interval1_clear_check
#print axioms integer_interval1_identity
end Erdos993Lean.BCFG.CertData.FHeavyB3
