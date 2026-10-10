module

public import Erdos993Lean.BCFG.LogQuadraticSupports
public import Erdos993Lean.BCFG.RowParameters
public import Erdos993Lean.BCFG.LogFixedInterpretation

/-! Exact printed ellLower/ellUpper bounds on all four closed activity rows. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem activityCenter_inRow (r : AnalyticRow) : InRow r (activityCenter r) := by
  cases r <;> norm_num [InRow, activityCenter, rowLow, rowHigh]

/-- These bounds consume the actual twelve integer series tests through
LogFixedInterpretation; no midpoint logarithm estimate is assumed. -/
theorem row_midpoint_log_bounds (r : AnalyticRow) :
    logCenterLower r ≤ Real.log (1+activityCenter r) ∧
      Real.log (1+activityCenter r) ≤ logCenterUpper r := by
  cases r with
  | B =>
    constructor
    · convert NatLog.midpoint_B_log.1.le using 1 <;>
        norm_num [logCenterLower, activityCenter, rowLow, rowHigh]
    · convert NatLog.midpoint_B_log.2.le using 1 <;>
        norm_num [logCenterUpper, activityCenter, rowLow, rowHigh]
  | C =>
    constructor
    · convert NatLog.midpoint_C_log.1.le using 1 <;>
        norm_num [logCenterLower, activityCenter, rowLow, rowHigh]
    · convert NatLog.midpoint_C_log.2.le using 1 <;>
        norm_num [logCenterUpper, activityCenter, rowLow, rowHigh]
  | F =>
    constructor
    · convert NatLog.midpoint_F_log.1.le using 1 <;>
        norm_num [logCenterLower, activityCenter, rowLow, rowHigh]
    · convert NatLog.midpoint_F_log.2.le using 1 <;>
        norm_num [logCenterUpper, activityCenter, rowLow, rowHigh]
  | G =>
    constructor
    · convert NatLog.midpoint_G_log.1.le using 1 <;>
        norm_num [logCenterLower, activityCenter, rowLow, rowHigh]
    · convert NatLog.midpoint_G_log.2.le using 1 <;>
        norm_num [logCenterUpper, activityCenter, rowLow, rowHigh]

theorem ell_log_bounds {r : AnalyticRow} {lam : ℝ} (hrow : InRow r lam) :
    ellLower r lam ≤ Real.log (1+lam) ∧ Real.log (1+lam) ≤ ellUpper r lam := by
  have hc := activityCenter_inRow r
  have hbase : 0 < 1+rowLow r := by linarith [rowLow_pos r]
  have hlo := log_quadratic_lower hbase hc hrow
  have hhi := log_quadratic_upper hbase hc hrow
  have hm := row_midpoint_log_bounds r
  unfold ellLower ellUpper
  constructor <;> linarith [hm.1, hm.2]

theorem ell_log_bounds_B {lam : ℝ} (hl : 3/5 ≤ lam) (hh : lam ≤ 39/50) :
    ellLower .B lam ≤ Real.log (1+lam) ∧ Real.log (1+lam) ≤ ellUpper .B lam :=
  ell_log_bounds (by simpa only [InRow, rowLow, rowHigh] using And.intro hl hh)

theorem ell_log_bounds_C {lam : ℝ} (hl : 39/50 ≤ lam) (hh : lam ≤ 4/5) :
    ellLower .C lam ≤ Real.log (1+lam) ∧ Real.log (1+lam) ≤ ellUpper .C lam :=
  ell_log_bounds (by simpa only [InRow, rowLow, rowHigh] using And.intro hl hh)

theorem ell_log_bounds_F {lam : ℝ} (hl : 8/5 ≤ lam) (hh : lam ≤ 33/20) :
    ellLower .F lam ≤ Real.log (1+lam) ∧ Real.log (1+lam) ≤ ellUpper .F lam :=
  ell_log_bounds (by simpa only [InRow, rowLow, rowHigh] using And.intro hl hh)

theorem ell_log_bounds_G {lam : ℝ} (hl : 33/20 ≤ lam) (hh : lam ≤ 7/4) :
    ellLower .G lam ≤ Real.log (1+lam) ∧ Real.log (1+lam) ≤ ellUpper .G lam :=
  ell_log_bounds (by simpa only [InRow, rowLow, rowHigh] using And.intro hl hh)

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.activityCenter_inRow
#print axioms Erdos993Lean.BCFG.Analytic.activityCenter_inRow
#check Erdos993Lean.BCFG.Analytic.row_midpoint_log_bounds
#print axioms Erdos993Lean.BCFG.Analytic.row_midpoint_log_bounds
#check Erdos993Lean.BCFG.Analytic.ell_log_bounds
#print axioms Erdos993Lean.BCFG.Analytic.ell_log_bounds
#check Erdos993Lean.BCFG.Analytic.ell_log_bounds_B
#print axioms Erdos993Lean.BCFG.Analytic.ell_log_bounds_B
#check Erdos993Lean.BCFG.Analytic.ell_log_bounds_C
#print axioms Erdos993Lean.BCFG.Analytic.ell_log_bounds_C
#check Erdos993Lean.BCFG.Analytic.ell_log_bounds_F
#print axioms Erdos993Lean.BCFG.Analytic.ell_log_bounds_F
#check Erdos993Lean.BCFG.Analytic.ell_log_bounds_G
#print axioms Erdos993Lean.BCFG.Analytic.ell_log_bounds_G
