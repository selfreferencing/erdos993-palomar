module
public import Erdos993Lean.F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0
public import Erdos993Lean.F4U.Light.Construction.GeneratedBindings.E2_B
public import Erdos993Lean.F4U.Light.Construction.NativeActivity
public import Erdos993Lean.F4U.Light.Linking.PositiveFraction
@[expose] public section
namespace F4Unified.LightConstruction.ActualPositivity.E2_B_1_1_V0_0
noncomputable section
open F4U.Light.Linking
open F4U.Light.Linking.Generated.DAG_E2_B_01
open F4U.Light.Short3.DAG_E2_B_01_P10

def certificateInput (lam : ℝ) : ℝ := q lam

theorem certificate_interval {lam : ℝ} (hlam : InRow .E2 lam) :
    F4U.Light.ActivityInterval F4U.Light.Data.E2_B_1_1_V0_0.fn (certificateInput lam) := by
  have h := activity_q_coverage hlam
  norm_num [rowData,q,F4U.Light.ActivityInterval,F4U.Light.intervalLower,
    F4U.Light.intervalUpper,F4U.Light.Data.E2_B_1_1_V0_0.fn,certificateInput] at h ⊢
  exact h

theorem certificate_input_restored {lam : ℝ} (hlam : InRow .E2 lam) :
    F4U.Light.activityArg F4U.Light.Data.E2_B_1_1_V0_0.fn (certificateInput lam) = nativeInput .E2 lam := by
  simpa [F4U.Light.activityArg,F4U.Light.Data.E2_B_1_1_V0_0.fn,certificateInput,nativeInput] using inverse_q_of_activity hlam

theorem actual_denominator_nonzero {lam t : ℝ} (hlam : InRow .E2 lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.numeratorOrientation E2_B_1_1_V0_0_pair.denominator)
      (nativeInput .E2 lam) t ≠ 0 := by
  have h := (E2_B_1_1_V0_0_sound (GroupDomain_E2_B.input lam) t
    (GroupDomain_E2_B.original_DivisorsNonzero hlam ht0 ht1)).1
  have hn : Polynomial2.eval E2_B_1_1_V0_0_pair.denominator (nativeInput .E2 lam) t ≠ 0 := by
    simpa only [RationalPair.NonzeroDenominator,GroupDomain_E2_B.input,nativeInput] using h
  rw [Polynomial2.eval_pscale]
  exact mul_ne_zero (by norm_num [F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.numeratorOrientation]) hn

theorem denominator_base_positive :
    0 < Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.numeratorOrientation E2_B_1_1_V0_0_pair.denominator)
      (nativeLo .E2) 0 := by
  have hb := checkPositiveBase_sound F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.base_checked
  convert hb using 1 <;> norm_num [nativeLo,nativeInput,rowData,q,
    F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.baseActivityNumerator,F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.baseActivityDenominator]

theorem actual_denominator_positive {lam t : ℝ} (hlam : InRow .E2 lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.numeratorOrientation E2_B_1_1_V0_0_pair.denominator)
      (nativeInput .E2 lam) t :=
  denominator_positive_on_row .E2 _
    (fun lam t hlam ht0 ht1 => actual_denominator_nonzero hlam ht0 ht1)
    denominator_base_positive hlam ht0 ht1

/-- The named original function is positive on its full retained row/chart. -/
theorem actual_positive {lam t : ℝ} (hlam : InRow .E2 lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < actualFunctionValue .E2 .B .first .upper .V0 0 lam t := by
  have hd := actual_denominator_positive hlam ht0 ht1
  have hv := value_positive_of_numerator
    (F:=F4U.Light.Data.E2_B_1_1_V0_0.fn) (p:=E2_B_1_1_V0_0_pair)
    (sign:=F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.numeratorOrientation) (scale:=F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.primitiveScale)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) F4U.Light.Linking.CheckedNumerators.E2_B_1_1_V0_0.numerator_checked
    (F4U.Light.checkFn_sound F4U.Light.Data.E2_B_1_1_V0_0.checked)
    (x:=certificateInput lam) (t:=t) (certificate_interval hlam) ht0 ht1
    (by simpa only [certificate_input_restored hlam] using hd)
  rw [certificate_input_restored hlam] at hv
  have hs := (E2_B_1_1_V0_0_sound (GroupDomain_E2_B.input lam) t
    (GroupDomain_E2_B.original_DivisorsNonzero hlam ht0 ht1)).2
  have he : E2_B_1_1_V0_0_pair.value (nativeInput .E2 lam) t =
      n00682_expression (GroupDomain_E2_B.input lam) t := by
    simpa only [GroupDomain_E2_B.input,nativeInput,E2_B_1_1_V0_0_expression] using hs
  rw [he,F4Unified.LightConstruction.GeneratedBindings.E2_B.E2_B_1_1_V0_0_eq_actual hlam] at hv
  exact hv

#print axioms certificate_interval
#print axioms certificate_input_restored
#print axioms actual_denominator_nonzero
#print axioms denominator_base_positive
#print axioms actual_denominator_positive
#print axioms actual_positive
end
end F4Unified.LightConstruction.ActualPositivity.E2_B_1_1_V0_0
