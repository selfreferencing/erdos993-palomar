module
public import Erdos993Lean.F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo
public import Erdos993Lean.F4U.Light.Construction.GeneratedBindings.E1_FULL
public import Erdos993Lean.F4U.Light.Construction.NativeActivity
public import Erdos993Lean.F4U.Light.Linking.PositiveFraction
@[expose] public section
namespace F4Unified.LightConstruction.ActualPositivity.E1_guard_r_lo
noncomputable section
open F4U.Light.Linking
open F4U.Light.Linking.Generated.DAG_E1_FULL_01

def certificateInput (lam : ℝ) : ℝ := lam

theorem certificate_interval {lam : ℝ} (hlam : InRow .E1 lam) :
    F4U.Light.ActivityInterval F4U.Light.Data.E1_guard_r_lo.fn (certificateInput lam) := by
  have h := activity_lambda_coverage hlam
  norm_num [rowData,q,F4U.Light.ActivityInterval,F4U.Light.intervalLower,
    F4U.Light.intervalUpper,F4U.Light.Data.E1_guard_r_lo.fn,certificateInput] at h ⊢
  exact h

theorem certificate_input_restored {lam : ℝ} (hlam : InRow .E1 lam) :
    F4U.Light.activityArg F4U.Light.Data.E1_guard_r_lo.fn (certificateInput lam) = nativeInput .E1 lam := by rfl

theorem actual_denominator_nonzero {lam t : ℝ} (hlam : InRow .E1 lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.numeratorOrientation E1_guard_r_lo_pair.denominator)
      (nativeInput .E1 lam) t ≠ 0 := by
  have h := (E1_guard_r_lo_sound (GroupDomain_E1_FULL.input lam) t
    (GroupDomain_E1_FULL.original_DivisorsNonzero hlam ht0 ht1)).1
  have hn : Polynomial2.eval E1_guard_r_lo_pair.denominator (nativeInput .E1 lam) t ≠ 0 := by
    simpa only [RationalPair.NonzeroDenominator,GroupDomain_E1_FULL.input,nativeInput] using h
  rw [Polynomial2.eval_pscale]
  exact mul_ne_zero (by norm_num [F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.numeratorOrientation]) hn

theorem denominator_base_positive :
    0 < Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.numeratorOrientation E1_guard_r_lo_pair.denominator)
      (nativeLo .E1) 0 := by
  have hb := checkPositiveBase_sound F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.base_checked
  convert hb using 1 <;> norm_num [nativeLo,nativeInput,rowData,q,
    F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.baseActivityNumerator,F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.baseActivityDenominator]

theorem actual_denominator_positive {lam t : ℝ} (hlam : InRow .E1 lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.numeratorOrientation E1_guard_r_lo_pair.denominator)
      (nativeInput .E1 lam) t :=
  denominator_positive_on_row .E1 _
    (fun lam t hlam ht0 ht1 => actual_denominator_nonzero hlam ht0 ht1)
    denominator_base_positive hlam ht0 ht1

/-- The named original function is positive on its full retained row/chart. -/
theorem actual_positive {lam t : ℝ} (hlam : InRow .E1 lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < guardFunctionValue .E1 .r0_lo lam t := by
  have hd := actual_denominator_positive hlam ht0 ht1
  have hv := value_positive_of_numerator
    (F:=F4U.Light.Data.E1_guard_r_lo.fn) (p:=E1_guard_r_lo_pair)
    (sign:=F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.numeratorOrientation) (scale:=F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.primitiveScale)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo.numerator_checked
    (F4U.Light.checkFn_sound F4U.Light.Data.E1_guard_r_lo.checked)
    (x:=certificateInput lam) (t:=t) (certificate_interval hlam) ht0 ht1
    (by simpa only [certificate_input_restored hlam] using hd)
  rw [certificate_input_restored hlam] at hv
  have hs := (E1_guard_r_lo_sound (GroupDomain_E1_FULL.input lam) t
    (GroupDomain_E1_FULL.original_DivisorsNonzero hlam ht0 ht1)).2
  have he : E1_guard_r_lo_pair.value (nativeInput .E1 lam) t =
      n00128_expression (GroupDomain_E1_FULL.input lam) t := by
    simpa only [GroupDomain_E1_FULL.input,nativeInput,E1_guard_r_lo_expression] using hs
  rw [he,F4Unified.LightConstruction.GeneratedBindings.E1_FULL.E1_guard_r_lo_eq_actual hlam] at hv
  exact hv

#print axioms certificate_interval
#print axioms certificate_input_restored
#print axioms actual_denominator_nonzero
#print axioms denominator_base_positive
#print axioms actual_denominator_positive
#print axioms actual_positive
end
end F4Unified.LightConstruction.ActualPositivity.E1_guard_r_lo
