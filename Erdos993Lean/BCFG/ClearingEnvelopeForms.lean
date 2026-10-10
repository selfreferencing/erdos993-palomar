module

public import Erdos993Lean.BCFG.ChartDefinitions

/-! Closed rational forms of the original logarithm envelopes. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

private theorem cayley_gap {w : ℝ} (hw : 0 < w) :
    1-((1-w)/(1+w))^2 = 4*w/(1+w)^2 := by
  have hd : 1+w ≠ 0 := ne_of_gt (by linarith)
  field_simp [hd]
  ring

theorem heavyUpper_closed_form (r : AnalyticRow) (lam : ℝ) {v : ℝ}
    (hv : 0 < v) :
    heavyUpper r lam v = ellUpper r lam + (heavyExponent r : ℝ)*
      ((1-v)*(v^2+10*v+1)/(6*v*(1+v))) := by
  have hd : 1+v ≠ 0 := ne_of_gt (by linarith)
  unfold heavyUpper heavyZ
  rw [cayley_gap hv]
  field_simp [hv.ne', hd]
  ring

theorem lightUpper_closed_form (lam x : ℝ) (hw : 0 < lightOmega lam x) :
    lightUpper lam x =
      (1-lightOmega lam x)*
        (3*(lightOmega lam x)^4+68*(lightOmega lam x)^3+
          98*(lightOmega lam x)^2+68*lightOmega lam x+3)/
        (30*lightOmega lam x*(1+lightOmega lam x)^3) := by
  have hd : 1+lightOmega lam x ≠ 0 := ne_of_gt (by linarith)
  unfold lightUpper lightZ
  rw [cayley_gap hw]
  field_simp [hw.ne', hd]
  ring

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavyUpper_closed_form
#print axioms Erdos993Lean.BCFG.Analytic.heavyUpper_closed_form
#check Erdos993Lean.BCFG.Analytic.lightUpper_closed_form
#print axioms Erdos993Lean.BCFG.Analytic.lightUpper_closed_form
