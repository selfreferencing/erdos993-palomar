module

public import Erdos993Lean.BCFG.ChartGeometry
public import Erdos993Lean.BCFG.TailScalar
public import Mathlib.Topology.Algebra.GroupWithZero

/-! Continuity of the actual rational chart diagonal. Denominator
nonvanishing is proved from the original positive activity and chart domains. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem occupation_continuousAt {lam omega : ℝ} (hl : 0 < lam) (hw : 0 < omega) :
    ContinuousAt (occupation lam) omega := by
  have hi : ContinuousAt (fun w : ℝ => w) omega := continuousAt_id
  have hm : ContinuousAt (fun w : ℝ => lam*w) omega := continuousAt_const.mul hi
  have hd : 0 < 1+lam*omega := by positivity
  exact hm.div (continuousAt_const.add hm) hd.ne'

theorem rhoZero_continuousAt {lam omega : ℝ} (hl : 0 < lam) (hw : 0 < omega) :
    ContinuousAt (rhoZero lam) omega := by
  have hi : ContinuousAt (fun w : ℝ => w) omega := continuousAt_id
  have hm : ContinuousAt (fun w : ℝ => lam*w) omega := continuousAt_const.mul hi
  have hd : 0 < 1+lam+lam*omega := by positivity
  exact (continuousAt_const.add hm).div (continuousAt_const.add hm) hd.ne'

/-- The generic composition lemma is discharged by the actual charts below. -/
theorem chart_diagonal_continuousAt {r : AnalyticRow} {lam a : ℝ}
    {omega rho U : ℝ → ℝ} (hl : 0 < lam) (hw : 0 < omega a)
    (hcw : ContinuousAt omega a) (hcr : ContinuousAt rho a) (hcU : ContinuousAt U a) :
    ContinuousAt (fun x => rCoeff r lam (omega x)-tailP r lam (omega x) (rho x)*U x) a := by
  have hp : ContinuousAt (fun x => occupation lam (omega x)) a :=
    (occupation_continuousAt hl hw).comp hcw
  have hpoly : ContinuousAt cubicEnvelope (occupation lam (omega a)) := by
    unfold cubicEnvelope
    fun_prop
  have hcp : ContinuousAt (fun x => cubicEnvelope (occupation lam (omega x))) a :=
    hpoly.comp (f := fun x => occupation lam (omega x)) hp
  have he : ContinuousAt (fun x => eCoeff r lam (omega x)) a := by
    convert (continuousAt_const (y := gamma r lam)).mul hcp using 1
    funext x
    simp only [eCoeff, Pi.mul_apply]
  have hd : ContinuousAt (fun x => dCoeff lam (omega x)) a := continuousAt_const.sub hp
  have hR : ContinuousAt (fun x => rCoeff r lam (omega x)) a :=
    continuousAt_const.div hp (occupation_bounds hl hw).1.ne'
  exact hR.sub ((he.add (hd.mul hcr)).mul hcU)

theorem heavyOmega_continuousAt (r : AnalyticRow) (lam v : ℝ) :
    ContinuousAt (heavyOmega r lam) v := by
  have hi : ContinuousAt (fun w : ℝ => w) v := continuousAt_id
  exact (hi.pow (heavyExponent r)).div_const (1+lam)

theorem lightOmega_continuousAt (lam x : ℝ) : ContinuousAt (lightOmega lam) x := by
  have hi : ContinuousAt (fun y : ℝ => y) x := continuousAt_id
  exact continuousAt_const.sub (continuousAt_const.mul hi)

theorem heavyUpper_continuousAt {r : AnalyticRow} {lam v : ℝ}
    (hv0 : 1/2 ≤ v) (hv1 : v ≤ 1) : ContinuousAt (heavyUpper r lam) v := by
  have hi : ContinuousAt (fun w : ℝ => w) v := continuousAt_id
  have hdv : 0 < 1+v := by linarith
  have hz : ContinuousAt heavyZ v :=
    (continuousAt_const.sub hi).div (continuousAt_const.add hi) hdv.ne'
  obtain ⟨hz0,hz1⟩ := heavyZ_bounds hv0 hv1
  have hd : 0 < 3*(1-(heavyZ v)^2) := by
    have hp : 0 < (1-heavyZ v)*(1+heavyZ v) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hquot : ContinuousAt (fun w => 2*(heavyZ w)^3/(3*(1-(heavyZ w)^2))) v :=
    (continuousAt_const.mul (hz.pow 3)).div
      (continuousAt_const.mul (continuousAt_const.sub (hz.pow 2))) hd.ne'
  exact continuousAt_const.add (continuousAt_const.mul
    ((continuousAt_const.mul hz).add hquot))

theorem lightUpper_continuousAt {lam x : ℝ} (hl : 0 < lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ContinuousAt (lightUpper lam) x := by
  have hw := lightOmega_pos hl hx0 hx1
  have hcw := lightOmega_continuousAt lam x
  have hdz : 0 < 1+lightOmega lam x := by linarith
  have hz : ContinuousAt (lightZ lam) x :=
    (continuousAt_const.sub hcw).div (continuousAt_const.add hcw) hdz.ne'
  obtain ⟨hz0,hz1⟩ := lightZ_bounds hl hx0 hx1
  have hd : 0 < 5*(1-(lightZ lam x)^2) := by
    have hp : 0 < (1-lightZ lam x)*(1+lightZ lam x) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hquot : ContinuousAt (fun y => 2*(lightZ lam y)^5/(5*(1-(lightZ lam y)^2))) x :=
    (continuousAt_const.mul (hz.pow 5)).div
      (continuousAt_const.mul (continuousAt_const.sub (hz.pow 2))) hd.ne'
  exact (continuousAt_const.mul (hz.add ((hz.pow 3).div_const 3))).add hquot

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.occupation_continuousAt
#print axioms Erdos993Lean.BCFG.Analytic.occupation_continuousAt
#check Erdos993Lean.BCFG.Analytic.rhoZero_continuousAt
#print axioms Erdos993Lean.BCFG.Analytic.rhoZero_continuousAt
#check Erdos993Lean.BCFG.Analytic.chart_diagonal_continuousAt
#print axioms Erdos993Lean.BCFG.Analytic.chart_diagonal_continuousAt
#check Erdos993Lean.BCFG.Analytic.heavyOmega_continuousAt
#print axioms Erdos993Lean.BCFG.Analytic.heavyOmega_continuousAt
#check Erdos993Lean.BCFG.Analytic.lightOmega_continuousAt
#print axioms Erdos993Lean.BCFG.Analytic.lightOmega_continuousAt
#check Erdos993Lean.BCFG.Analytic.heavyUpper_continuousAt
#print axioms Erdos993Lean.BCFG.Analytic.heavyUpper_continuousAt
#check Erdos993Lean.BCFG.Analytic.lightUpper_continuousAt
#print axioms Erdos993Lean.BCFG.Analytic.lightUpper_continuousAt
