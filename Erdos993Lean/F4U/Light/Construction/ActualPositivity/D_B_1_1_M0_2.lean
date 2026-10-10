module
public import Erdos993Lean.F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2
public import Erdos993Lean.F4U.Light.Construction.GeneratedBindings.D_B
public import Erdos993Lean.F4U.Light.Construction.NativeActivity
public import Erdos993Lean.F4U.Light.Linking.PositiveFraction
@[expose] public section
namespace F4Unified.LightConstruction.ActualPositivity.D_B_1_1_M0_2
noncomputable section
open F4U.Light.Linking
open F4U.Light.Linking.Generated.DAG_D_B_01
open F4U.Light.Short3.DAG_D_B_01_P10

def certificateInput (lam : ℝ) : ℝ := q lam

theorem certificate_interval {lam : ℝ} (hlam : InRow .D lam) :
    F4U.Light.ActivityInterval F4U.Light.Data.D_B_1_1_M0_2.fn (certificateInput lam) := by
  have h := activity_q_coverage hlam
  norm_num [rowData,q,F4U.Light.ActivityInterval,F4U.Light.intervalLower,
    F4U.Light.intervalUpper,F4U.Light.Data.D_B_1_1_M0_2.fn,certificateInput] at h ⊢
  exact h

theorem certificate_input_restored {lam : ℝ} (hlam : InRow .D lam) :
    F4U.Light.activityArg F4U.Light.Data.D_B_1_1_M0_2.fn (certificateInput lam) = nativeInput .D lam := by rfl

theorem actual_denominator_nonzero {lam t : ℝ} (hlam : InRow .D lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.numeratorOrientation D_B_1_1_M0_2_pair.denominator)
      (nativeInput .D lam) t ≠ 0 := by
  have h := (D_B_1_1_M0_2_sound (GroupDomain_D_B.input lam) t
    (GroupDomain_D_B.original_DivisorsNonzero hlam ht0 ht1)).1
  have hn : Polynomial2.eval D_B_1_1_M0_2_pair.denominator (nativeInput .D lam) t ≠ 0 := by
    simpa only [RationalPair.NonzeroDenominator,GroupDomain_D_B.input,nativeInput] using h
  rw [Polynomial2.eval_pscale]
  exact mul_ne_zero (by norm_num [F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.numeratorOrientation]) hn

theorem denominator_base_positive :
    0 < Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.numeratorOrientation D_B_1_1_M0_2_pair.denominator)
      (nativeLo .D) 0 := by
  have hb := checkPositiveBase_sound F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.base_checked
  convert hb using 1 <;> norm_num [nativeLo,nativeInput,rowData,q,
    F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.baseActivityNumerator,F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.baseActivityDenominator]

theorem actual_denominator_positive {lam t : ℝ} (hlam : InRow .D lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < Polynomial2.eval (Polynomial2.pscale F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.numeratorOrientation D_B_1_1_M0_2_pair.denominator)
      (nativeInput .D lam) t :=
  denominator_positive_on_row .D _
    (fun lam t hlam ht0 ht1 => actual_denominator_nonzero hlam ht0 ht1)
    denominator_base_positive hlam ht0 ht1

/-- The named original function is positive on its full retained row/chart. -/
theorem actual_positive {lam t : ℝ} (hlam : InRow .D lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < actualFunctionValue .D .B .first .upper .M0 2 lam t := by
  have hd := actual_denominator_positive hlam ht0 ht1
  have hv := value_positive_of_numerator
    (F:=F4U.Light.Data.D_B_1_1_M0_2.fn) (p:=D_B_1_1_M0_2_pair)
    (sign:=F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.numeratorOrientation) (scale:=F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.primitiveScale)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) F4U.Light.Linking.CheckedNumerators.D_B_1_1_M0_2.numerator_checked
    (F4U.Light.checkFn_sound F4U.Light.Data.D_B_1_1_M0_2.checked)
    (x:=certificateInput lam) (t:=t) (certificate_interval hlam) ht0 ht1
    (by simpa only [certificate_input_restored hlam] using hd)
  rw [certificate_input_restored hlam] at hv
  have hs := (D_B_1_1_M0_2_sound (GroupDomain_D_B.input lam) t
    (GroupDomain_D_B.original_DivisorsNonzero hlam ht0 ht1)).2
  have he : D_B_1_1_M0_2_pair.value (nativeInput .D lam) t =
      n00646_expression (GroupDomain_D_B.input lam) t := by
    simpa only [GroupDomain_D_B.input,nativeInput,D_B_1_1_M0_2_expression] using hs
  rw [he,F4Unified.LightConstruction.GeneratedBindings.D_B.D_B_1_1_M0_2_eq_actual hlam] at hv
  exact hv

#print axioms certificate_interval
#print axioms certificate_input_restored
#print axioms actual_denominator_nonzero
#print axioms denominator_base_positive
#print axioms actual_denominator_positive
#print axioms actual_positive
end
end F4Unified.LightConstruction.ActualPositivity.D_B_1_1_M0_2
