module

public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerInterval10Tables
public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerIntervalLower

/-! Checked integer clearing recovers the unchanged original interval10 identity predicate. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.GHeavyB3

theorem integer_interval10_source :
    interval10.coeffs = IUni.ratioRow M interval10SourceNumInt interval10SourceDenInt := by rfl

theorem integer_interval10_guards :
    interval10DenInt ≠ 0 ∧ interval10ChartDenInt ≠ 0 ∧
    interval10.lo = (interval10ChartAInt : Rat)/(interval10ChartDenInt : Rat) ∧
    interval10.hi-interval10.lo = (interval10ChartBInt : Rat)/(interval10ChartDenInt : Rat) := by
  decide +kernel

theorem integer_interval10_den_ne_zero : interval10DenInt ≠ 0 := integer_interval10_guards.1

theorem integer_interval10_fraction_checks :
    (List.range (M+1)).all (fun j =>
      decide (interval10SourceDenInt.getD j 1 ≠ 0) &&
      decide (interval10SourceNumInt.getD j 0 * interval10DenInt = interval10CoeffInt.getD j 0 * interval10SourceDenInt.getD j 1)) = true := by
  decide +kernel

theorem integer_interval10_coefficients : ∀ j < M+1,
    (interval10.coeffs).getD j 0 = (interval10CoeffInt.getD j 0 : Rat)/(interval10DenInt : Rat) := by
  apply IUni.ratioRow_coeffs M (interval10.coeffs) interval10SourceNumInt interval10SourceDenInt interval10CoeffInt interval10DenInt integer_interval10_source
    integer_interval10_den_ne_zero
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval10_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval10_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

theorem integer_interval10_bern_calc :
    IUni.cachedBernVector M basisInt interval10CoeffInt = interval10BernInt := by
  decide +kernel

theorem integer_interval10_bern_checked :
    Uni.bernVector M (interval10.coeffs) =
      Uni.scale ((1 : Rat)/(interval10DenInt : Rat)) (IUni.castRat interval10BernInt) := by
  have hcoeff : ∀ j < M+1, (interval10.coeffs).getD j 0 =
      ((1 : Rat)/(interval10DenInt : Rat)) * (interval10CoeffInt.getD j 0 : Rat) := by
    intro j hj
    rw [integer_interval10_coefficients j hj]
    simp only [div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  have h := Uni.bernVector_eq_intCached M (interval10.coeffs) basisInt interval10CoeffInt
    ((1 : Rat)/(interval10DenInt : Rat)) integer_basis_checked hcoeff
  rw [integer_interval10_bern_calc] at h
  exact h

theorem integer_interval10_composition_calc :
    IUni.affineHom intervalLowerBernInt interval10ChartAInt interval10ChartBInt
      interval10ChartDenInt M = interval10CompositionInt := by decide +kernel

theorem integer_interval10_clear_check :
    IUni.checkEq
      (IUni.scale interval10DenInt interval10CompositionInt)
      (IUni.scale (intervalLowerDenInt * interval10ChartPowerDenInt) interval10BernInt) = true := by
  decide +kernel

theorem integer_interval10_identity :
    Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [interval10.lo, interval10.hi-interval10.lo])
      (Uni.bernVector M interval10.coeffs) = true := by
  have hChart := IUni.composition_eq_integer
    (IUni.castRat intervalLowerBernInt) intervalLowerBernInt interval10.lo (interval10.hi-interval10.lo)
    interval10ChartAInt interval10ChartBInt interval10ChartDenInt M interval10CompositionInt
    rfl integer_interval_lower_guards.2 integer_interval10_guards.2.1
    integer_interval10_guards.2.2.1 integer_interval10_guards.2.2.2 integer_interval10_composition_calc
  have hChartDen : interval10ChartPowerDenInt ≠ 0 :=
    pow_ne_zero _ integer_interval10_guards.2.1
  exact Uni.interval_identity_of_integer_clear M lower interval10
    intervalLowerBernInt interval10CompositionInt interval10BernInt
    intervalLowerDenInt interval10ChartPowerDenInt interval10DenInt
    integer_interval_lower_den_ne_zero hChartDen integer_interval10_den_ne_zero
    integer_interval_lower_bern_checked hChart integer_interval10_bern_checked integer_interval10_clear_check

#print axioms integer_interval10_source
#print axioms integer_interval10_guards
#print axioms integer_interval10_fraction_checks
#print axioms integer_interval10_bern_calc
#print axioms integer_interval10_bern_checked
#print axioms integer_interval10_composition_calc
#print axioms integer_interval10_clear_check
#print axioms integer_interval10_identity
end Erdos993Lean.BCFG.CertData.GHeavyB3
