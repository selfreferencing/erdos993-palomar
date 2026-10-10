module

public import Erdos993Lean.F4U.Light.Construction.VacancyBernstein
public import Erdos993Lean.F4U.Light.Construction.SourceChords

/-!
The omitted second-phase native zero controls are equal to the first-phase
terminal controls as full rational functions, irrespective of clearing factors. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section
open scoped BigOperators

 theorem vacancyControl_at_zero (w : ℕ → ℝ) (r0 r1 : ℝ) (n : ℕ) :
    vacancyControl w r0 r1 n 0 = cubicValue w r0 := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  norm_num [vacancyControl, vacancyChartCoefficient, cubicValue, h03, Finset.sum_range_succ]
  <;> ring

 theorem vacancyControl_at_terminal (w : ℕ → ℝ) (r0 r1 : ℝ) {n : ℕ}
    (hn : n=3 ∨ n=4) : vacancyControl w r0 r1 n n = cubicValue w r1 := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2=6 := by decide
  rcases hn with rfl | rfl <;>
    norm_num [vacancyControl, vacancyChartCoefficient, cubicValue,
      h03,h13,h23,h33,h42,Finset.sum_range_succ] <;> ring

 theorem actual_second_control_zero (r : Row) (reg : Regime) (endpoint : LogEndpoint)
    (control : ChildControl) (lam H : ℝ) :
    actualVacancyControl r reg .second endpoint control 0 lam H =
      childControlValue r reg .second control lam H (vacancySwitch lam H) (logEndpoint endpoint H) := by
  unfold actualVacancyControl
  rw [vacancyControl_at_zero]
  rw [child_control_cubic_representation]
  rfl

 theorem actual_first_control_terminal (r : Row) (reg : Regime) (endpoint : LogEndpoint)
    (control : ChildControl) (lam H : ℝ) :
    actualVacancyControl r reg .first endpoint control (vacancyControlDegree reg .first) lam H =
      childControlValue r reg .first control lam H (vacancySwitch lam H) (logEndpoint endpoint H) := by
  unfold actualVacancyControl
  rw [vacancyControl_at_terminal _ _ _ (by cases reg <;> simp [vacancyControlDegree])]
  rw [child_control_cubic_representation]
  rfl

 theorem child_phase_face_identity (r : Row) (reg : Regime) (control : ChildControl)
    {lam H : ℝ} (hlam : InRow r lam) (hH0 : 0 < H) (hHq : H ≤ q lam) (z : ℝ) :
    childControlValue r reg .second control lam H (vacancySwitch lam H) z =
      childControlValue r reg .first control lam H (vacancySwitch lam H) z := by
  have hn : parentNHat r .second lam H (vacancySwitch lam H) =
      parentNHat r .first lam H (vacancySwitch lam H) := by
    unfold parentNHat
    rw [second_chord_at_switch hlam hH0.le hHq,first_chord_at_switch hlam hH0 hHq]
  have hW : ∀ h L, W r .second lam H (vacancySwitch lam H) z h L =
      W r .first lam H (vacancySwitch lam H) z h L := by
    intro h L
    unfold W
    rw [hn]
  cases control <;> cases reg <;>
    simp only [childControlValue,childV0,childV1,childM0,hW]

 theorem actual_second_phase_zero_alias (r : Row) (reg : Regime) (endpoint : LogEndpoint)
    (control : ChildControl) {lam H : ℝ} (hlam : InRow r lam) (hH0 : 0 < H)
    (hHq : H ≤ q lam) :
    actualVacancyControl r reg .second endpoint control 0 lam H =
      actualVacancyControl r reg .first endpoint control (vacancyControlDegree reg .first) lam H := by
  rw [actual_second_control_zero,actual_first_control_terminal]
  exact child_phase_face_identity r reg control hlam hH0 hHq (logEndpoint endpoint H)

 theorem actualFunctionValue_second_zero_alias (r : Row) (reg : Regime)
    (endpoint : LogEndpoint) (control : ChildControl) {lam t : ℝ}
    (hlam : InRow r lam) (hH0 : 0 < parentChart r reg lam t)
    (hHq : parentChart r reg lam t ≤ q lam) :
    actualFunctionValue r reg .second endpoint control 0 lam t =
      actualFunctionValue r reg .first endpoint control (vacancyControlDegree reg .first) lam t := by
  exact actual_second_phase_zero_alias r reg endpoint control hlam hH0 hHq

 /-- Restores the omitted native zero coefficient before the full cubic consumer.
 The premises name the first-phase controls and the retained second-phase controls,
 so no sign is projected away or independently postulated for the omitted face. -/
 theorem actual_second_controls_pos_of_retained (r : Row) (reg : Regime)
    (endpoint : LogEndpoint) (control : ChildControl) {lam H : ℝ}
    (hlam : InRow r lam) (hH0 : 0 < H) (hHq : H ≤ q lam)
    (hfirst : ∀ s ≤ vacancyControlDegree reg .first,
      0 < actualVacancyControl r reg .first endpoint control s lam H)
    (hsecond : ∀ s, 1 ≤ s → s ≤ vacancyControlDegree reg .second →
      0 < actualVacancyControl r reg .second endpoint control s lam H) :
    ∀ s ≤ vacancyControlDegree reg .second,
      0 < actualVacancyControl r reg .second endpoint control s lam H := by
  intro s hs
  cases s with
  | zero =>
      rw [actual_second_phase_zero_alias r reg endpoint control hlam hH0 hHq]
      exact hfirst _ le_rfl
  | succ s => exact hsecond (s+1) (by omega) hs

#print axioms vacancyControl_at_zero
#print axioms vacancyControl_at_terminal
#print axioms actual_second_control_zero
#print axioms actual_first_control_terminal
#print axioms child_phase_face_identity
#print axioms actual_second_phase_zero_alias
#print axioms actualFunctionValue_second_zero_alias
#print axioms actual_second_controls_pos_of_retained

end
end F4Unified.LightConstruction
