module

public import Erdos993Lean.BCFG.RowLogEnvelopes
public import Erdos993Lean.BCFG.ChartGeometry
public import Erdos993Lean.BCFG.LogRemainder

/-! Closed heavy/light chart logarithm bounds. The heavy chart uses the literal
n=1 series bound and the light chart uses n=2. The x=0 endpoint is explicit. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem log_reciprocal_chart {w : ℝ} (hw : 0 < w) :
    Real.log ((1+(1-w)/(1+w))/(1-(1-w)/(1+w))) = -Real.log w := by
  have h1 : 0 < 1+w := by linarith
  have hz1 : (1-w)/(1+w) < 1 := (div_lt_one h1).2 (by linarith)
  have hd : 1-(1-w)/(1+w) ≠ 0 := (sub_pos.mpr hz1).ne'
  have he : (1+(1-w)/(1+w))/(1-(1-w)/(1+w)) = 1/w := by
    apply (div_eq_iff hd).2
    field_simp [hw.ne', h1.ne'] <;> ring
  rw [he, one_div, Real.log_inv]

theorem heavy_log_piece_bounds {v : ℝ} (hv0 : 1/2 ≤ v) (hv1 : v ≤ 1) :
    2*heavyZ v ≤ -Real.log v ∧
      -Real.log v ≤ 2*heavyZ v+2*(heavyZ v)^3/(3*(1-(heavyZ v)^2)) := by
  have hv : 0 < v := by linarith
  have hz := heavyZ_bounds hv0 hv1
  have hz1 : heavyZ v < 1 := by linarith [hz.2]
  have he : Real.log ((1+heavyZ v)/(1-heavyZ v)) = -Real.log v := by
    simpa only [heavyZ] using log_reciprocal_chart hv
  have hlo := logLower_le 1 hz.1 hz1
  have hhi := log_le_logUpper 1 hz.1 hz1
  rw [he] at hlo hhi
  constructor
  · simpa [logLower, Finset.sum_range_succ] using hlo
  · convert hhi using 1 <;> norm_num [logUpper, logLower, Finset.sum_range_succ]

theorem heavy_log_identity {r : AnalyticRow} {lam v : ℝ}
    (hl : 0 < lam) (hv : 0 < v) :
    -Real.log (heavyOmega r lam v) =
      Real.log (1+lam)+(heavyExponent r : ℝ)*(-Real.log v) := by
  have hd : 1+lam ≠ 0 := by linarith
  unfold heavyOmega
  rw [Real.log_div (pow_ne_zero _ hv.ne') hd, Real.log_pow]
  ring

theorem heavy_log_bounds {r : AnalyticRow} {lam v : ℝ} (h : HeavyDomain r lam v) :
    heavyLower r lam v ≤ -Real.log (heavyOmega r lam v) ∧
      -Real.log (heavyOmega r lam v) ≤ heavyUpper r lam v := by
  have hl := activity_pos h.1
  have hv : 0 < v := by linarith [h.2.1]
  have hell := ell_log_bounds h.1
  have hvlog := heavy_log_piece_bounds h.2.1 h.2.2
  have hk : 0 ≤ (heavyExponent r : ℝ) := by positivity
  have hlo := mul_le_mul_of_nonneg_left hvlog.1 hk
  have hhi := mul_le_mul_of_nonneg_left hvlog.2 hk
  rw [heavy_log_identity hl hv]
  unfold heavyLower heavyUpper
  constructor <;> linarith [hell.1, hell.2]

theorem heavy_logMass_bounds {r : AnalyticRow} {lam v : ℝ}
    (h : HeavyDomain r lam v) :
    heavyLower r lam v ≤ logMass (heavyOmega r lam v) ∧
      logMass (heavyOmega r lam v) ≤ heavyUpper r lam v :=
  heavy_log_bounds h

/-- The closed zero endpoint does not require lam>0 or division by x. -/
theorem light_log_zero (lam : ℝ) :
    lightOmega lam 0 = 1 ∧ -Real.log (lightOmega lam 0) = 0 ∧ lightUpper lam 0 = 0 := by
  simp [lightOmega, lightZ, lightUpper]

theorem light_log_bounds {lam x : ℝ} (hl : 0 < lam) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ -Real.log (lightOmega lam x) ∧
      -Real.log (lightOmega lam x) ≤ lightUpper lam x := by
  by_cases hx : x = 0
  · subst x
    simp [lightOmega, lightZ, lightUpper]
  · have hw := lightOmega_pos hl hx0 hx1
    have hw1 := (lightOmega_bounds hl hx0 hx1).2
    have hz := lightZ_bounds hl hx0 hx1
    have he : Real.log ((1+lightZ lam x)/(1-lightZ lam x)) =
        -Real.log (lightOmega lam x) := by
      simpa only [lightZ] using log_reciprocal_chart hw
    have hhi := log_le_logUpper 2 hz.1 hz.2
    rw [he] at hhi
    constructor
    · exact neg_nonneg.mpr (Real.log_nonpos hw.le hw1)
    · convert hhi using 1 <;>
        norm_num [lightUpper, logUpper, logLower, Finset.sum_range_succ]

theorem light_log_bounds_onRow {r : AnalyticRow} {lam x : ℝ}
    (h : LightDomain r lam x) :
    0 ≤ -Real.log (lightOmega lam x) ∧
      -Real.log (lightOmega lam x) ≤ lightUpper lam x :=
  light_log_bounds (activity_pos h.1) h.2.1 h.2.2

theorem light_logMass_bounds {r : AnalyticRow} {lam x : ℝ}
    (h : LightDomain r lam x) :
    0 ≤ logMass (lightOmega lam x) ∧ logMass (lightOmega lam x) ≤ lightUpper lam x :=
  light_log_bounds_onRow h

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.log_reciprocal_chart
#print axioms Erdos993Lean.BCFG.Analytic.log_reciprocal_chart
#check Erdos993Lean.BCFG.Analytic.heavy_log_piece_bounds
#print axioms Erdos993Lean.BCFG.Analytic.heavy_log_piece_bounds
#check Erdos993Lean.BCFG.Analytic.heavy_log_identity
#print axioms Erdos993Lean.BCFG.Analytic.heavy_log_identity
#check Erdos993Lean.BCFG.Analytic.heavy_log_bounds
#print axioms Erdos993Lean.BCFG.Analytic.heavy_log_bounds
#check Erdos993Lean.BCFG.Analytic.heavy_logMass_bounds
#print axioms Erdos993Lean.BCFG.Analytic.heavy_logMass_bounds
#check Erdos993Lean.BCFG.Analytic.light_log_zero
#print axioms Erdos993Lean.BCFG.Analytic.light_log_zero
#check Erdos993Lean.BCFG.Analytic.light_log_bounds
#print axioms Erdos993Lean.BCFG.Analytic.light_log_bounds
#check Erdos993Lean.BCFG.Analytic.light_log_bounds_onRow
#print axioms Erdos993Lean.BCFG.Analytic.light_log_bounds_onRow
#check Erdos993Lean.BCFG.Analytic.light_logMass_bounds
#print axioms Erdos993Lean.BCFG.Analytic.light_logMass_bounds
