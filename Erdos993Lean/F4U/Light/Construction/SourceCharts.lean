module

public import Erdos993Lean.F4U.Light.Construction.Domain

/-! Exact q-coordinate charts of the original parent and vacancy endpoints.
The first phase has positive width; the second canceled slope remains defined
at H=q. No q-H denominator is introduced. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem pH_q_chart {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    pH lam H = q lam*(1-H)/(1-q lam*H) := by
  have hl := inRow_lambda_bounds hlam
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,hl1,_,_,_,_,hH1,_,hqH,_,_,_,_,_⟩
  have hpden : 1+lam*(1-H) ≠ 0 := by positivity
  have hcanon : 1+lam-lam*H ≠ 0 := by
    have hprod := mul_pos hl.1 hH1
    nlinarith
  unfold pH q
  field_simp [hl1.ne', hpden, hqH.ne', hcanon]
  <;> ring

 theorem vacancyLo_q_chart {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    vacancyLo lam H = (1-q lam*H)/(1+q lam-q lam*H) := by
  have hl := inRow_lambda_bounds hlam
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨hl0,hl1,_,_,_,_,hH1,_,hqH,hplus,_,_,hp1,_⟩
  have hpden : 1+lam*(1-H) ≠ 0 := by positivity
  have hvden : 1+lam*(1-pH lam H) ≠ 0 := by positivity
  unfold vacancyLo pH q
  field_simp [hl1.ne', hpden, hvden, hqH.ne', hplus.ne']
  <;> ring

 theorem vacancySwitch_q_chart {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    vacancySwitch lam H = (1-q lam*H)/((1+q lam)*(1-H)) := by
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨hl0,hl1,hq0,_,hqplus,_,hH1,_,hqH,_,_,hp,_,_⟩
  have hpden : 1+lam*(1-H) ≠ 0 := by positivity
  unfold vacancySwitch pH q
  field_simp [hl0.ne', hl1.ne', hq0.ne',
    hpden, hqplus.ne', hH1.ne', hqH.ne', hp.ne']
  <;> ring

 theorem vacancy_phase_width {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    vacancySwitch lam H-vacancyLo lam H =
      H*(1-q lam*H)/((1-H)*(1+q lam)*(1+q lam-q lam*H)) := by
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,_,_,_,hqplus,_,hH1,_,_,hplus,_,_,_,_⟩
  rw [vacancySwitch_q_chart hlam hH0 hHq, vacancyLo_q_chart hlam hH0 hHq]
  field_simp [hH1.ne', hqplus.ne', hplus.ne']
  <;> ring

 theorem vacancy_first_phase_positive {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 < H) (hHq : H ≤ q lam) :
    0 < vacancySwitch lam H-vacancyLo lam H := by
  have hd := light_rational_denominators hlam hH0.le hHq
  rcases hd with ⟨_,_,_,_,hqplus,_,hH1,_,hqH,hplus,_,_,_,_⟩
  rw [vacancy_phase_width hlam hH0.le hHq]
  positivity

 theorem second_chord_collapsed_slope {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    chordSlope .second lam (q lam) = ((q lam)^2+1)/(4*q lam) := by
  have hd := light_rational_denominators hlam (inRow_q_bounds hlam).1.le le_rfl
  rcases hd with ⟨_,_,hq0,hq1,_,hq2,_,_,hqH,_,_,_,_,_⟩
  have hqsq : 1-(q lam)^2 ≠ 0 := by nlinarith [hqH]
  simp only [chordSlope]
  field_simp [hq0.ne', hq1.ne', hq2.ne', hqH.ne',hqsq]
  <;> ring

 theorem first_chord_at_lo (lam H : ℝ) :
    sourceChord .first lam H (vacancyLo lam H) = sourceAtLo lam H := by
  unfold sourceChord chordIntercept
  ring

 theorem first_chord_at_switch {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 < H) (hHq : H ≤ q lam) :
    sourceChord .first lam H (vacancySwitch lam H) = sourceAtSwitchLower lam H := by
  have hwidth := vacancy_first_phase_positive hlam hH0 hHq
  unfold sourceChord chordIntercept chordSlope
  field_simp [hwidth.ne']
  <;> ring

 theorem second_chord_at_hi (lam H : ℝ) : sourceChord .second lam H 1 = sourceAtHi lam H := by
  unfold sourceChord chordIntercept
  ring

#print axioms pH_q_chart
#print axioms vacancyLo_q_chart
#print axioms vacancySwitch_q_chart
#print axioms vacancy_phase_width
#print axioms vacancy_first_phase_positive
#print axioms second_chord_collapsed_slope
#print axioms first_chord_at_lo
#print axioms first_chord_at_switch
#print axioms second_chord_at_hi

end
end F4Unified.LightConstruction
