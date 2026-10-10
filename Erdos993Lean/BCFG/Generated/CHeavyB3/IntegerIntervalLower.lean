module

public import Erdos993Lean.BCFG.Generated.CHeavyB3.IntegerIntervalLowerTables
public import Erdos993Lean.BCFG.Generated.CHeavyB3.IntegerBasis
public import Erdos993Lean.F4Fast.IntegerInterval
public import Erdos993Lean.F4Fast.RangeAll

/-! Checked source-exact lower Bernstein polynomial shared by the split intervals. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.CHeavyB3

theorem integer_interval_lower_source :
    lower = IUni.ratioRow M intervalLowerSourceNumInt intervalLowerSourceDenInt := by rfl

theorem integer_interval_lower_guards :
    intervalLowerDenInt ≠ 0 ∧ intervalLowerBernInt.length ≤ M+1 := by decide +kernel

theorem integer_interval_lower_den_ne_zero : intervalLowerDenInt ≠ 0 :=
  integer_interval_lower_guards.1

theorem integer_interval_lower_fraction_checks :
    (List.range (M+1)).all (fun j =>
      decide (intervalLowerSourceDenInt.getD j 1 ≠ 0) &&
      decide (intervalLowerSourceNumInt.getD j 0 * intervalLowerDenInt = intervalLowerCoeffInt.getD j 0 * intervalLowerSourceDenInt.getD j 1)) = true := by
  decide +kernel

theorem integer_interval_lower_coefficients : ∀ j < M+1,
    (lower).getD j 0 = (intervalLowerCoeffInt.getD j 0 : Rat)/(intervalLowerDenInt : Rat) := by
  apply IUni.ratioRow_coeffs M (lower) intervalLowerSourceNumInt intervalLowerSourceDenInt intervalLowerCoeffInt intervalLowerDenInt integer_interval_lower_source
    integer_interval_lower_den_ne_zero
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval_lower_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  · intro j hj
    have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_interval_lower_fraction_checks j hj
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

theorem integer_interval_lower_bern_calc :
    IUni.cachedBernVector M basisInt intervalLowerCoeffInt = intervalLowerBernInt := by
  decide +kernel

theorem integer_interval_lower_bern_checked :
    Uni.bernVector M (lower) =
      Uni.scale ((1 : Rat)/(intervalLowerDenInt : Rat)) (IUni.castRat intervalLowerBernInt) := by
  have hcoeff : ∀ j < M+1, (lower).getD j 0 =
      ((1 : Rat)/(intervalLowerDenInt : Rat)) * (intervalLowerCoeffInt.getD j 0 : Rat) := by
    intro j hj
    rw [integer_interval_lower_coefficients j hj]
    simp only [div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  have h := Uni.bernVector_eq_intCached M (lower) basisInt intervalLowerCoeffInt
    ((1 : Rat)/(intervalLowerDenInt : Rat)) integer_basis_checked hcoeff
  rw [integer_interval_lower_bern_calc] at h
  exact h

#print axioms integer_interval_lower_source
#print axioms integer_interval_lower_guards
#print axioms integer_interval_lower_fraction_checks
#print axioms integer_interval_lower_bern_calc
#print axioms integer_interval_lower_bern_checked
end Erdos993Lean.BCFG.CertData.CHeavyB3
