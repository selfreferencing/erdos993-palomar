module

public import Erdos993Lean.BCFG.AnalyticTransfer
public import Mathlib

/-! Literal data and scalar domains from current T6b.
These definitions do not assert any logarithm, finite-gate or payment bound. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

def rowLow : AnalyticRow → ℝ
  | .B => 3/5 | .C => 39/50 | .F => 8/5 | .G => 33/20
def rowHigh : AnalyticRow → ℝ
  | .B => 39/50 | .C => 4/5 | .F => 33/20 | .G => 7/4
def theta : AnalyticRow → ℝ
  | .B => 17/10 | .C => 33/20 | .F => 19/10 | .G => 39/20
def alpha : AnalyticRow → ℝ
  | .B => 37/40 | .C => 37/40 | .F => 43/40 | .G => 11/10
def beta : AnalyticRow → ℝ
  | .B => 43/40 | .C => 43/40 | .F => 23/20 | .G => 8/7
def kappa : AnalyticRow → ℝ
  | .B => 8/25 | .C => 8/25 | .F => 3/10 | .G => 3/10
def heavyExponent : AnalyticRow → ℕ
  | .B => 4 | .C => 4 | .F => 6 | .G => 6
def massIntercept : AnalyticRow → ℝ
  | .B => 409/400 | .C => 409/400 | .F => 13/12 | .G => 13/12
def massSlope : AnalyticRow → ℝ
  | .B => 3/5 | .C => 3/5 | .F => 5/7 | .G => 5/7
def logCenterLower : AnalyticRow → ℝ
  | .B => 52472852/10^8 | .C => 58221561/10^8
  | .F => 96508089/10^8 | .G => 99325177/10^8
def logCenterUpper : AnalyticRow → ℝ
  | .B => 52472853/10^8 | .C => 58221562/10^8
  | .F => 96508090/10^8 | .G => 99325178/10^8

def epsilon : ℝ := 1/10000
def q (lam : ℝ) : ℝ := lam/(1+lam)
def occupation (lam omega : ℝ) : ℝ := lam*omega/(1+lam*omega)
noncomputable def logMass (omega : ℝ) : ℝ := -Real.log omega
def rhoZero (lam omega : ℝ) : ℝ := (1+lam*omega)/(1+lam+lam*omega)
def cubicEnvelope (p : ℝ) : ℝ := 1-p/2-p^2/12-p^3/24
def price (r : AnalyticRow) (lam : ℝ) : ℝ := theta r/(1+lam)
def gamma (r : AnalyticRow) (lam : ℝ) : ℝ := kappa r*lam
def centerResponse (r : AnalyticRow) : ℝ := (alpha r+beta r)/2
def activityCenter (r : AnalyticRow) : ℝ := (rowLow r+rowHigh r)/2
def massLine (r : AnalyticRow) (lam : ℝ) : ℝ := massIntercept r-massSlope r*q lam
def ellLower (r : AnalyticRow) (lam : ℝ) : ℝ :=
  logCenterLower r+(lam-activityCenter r)/(1+activityCenter r)-
    (lam-activityCenter r)^2/(2*(1+rowLow r)^2)
def ellUpper (r : AnalyticRow) (lam : ℝ) : ℝ :=
  logCenterUpper r+(lam-activityCenter r)/(1+activityCenter r)-
    (lam-activityCenter r)^2/(2*(1+rowHigh r)^2)

def InRow (r : AnalyticRow) (lam : ℝ) : Prop := rowLow r ≤ lam ∧ lam ≤ rowHigh r
def Feasible (r : AnalyticRow) (lam omega rho : ℝ) : Prop :=
  InRow r lam ∧ 0 < omega ∧ omega ≤ 1 ∧ rhoZero lam omega ≤ rho ∧ rho ≤ 1
def HeavyDomain (r : AnalyticRow) (lam v : ℝ) : Prop :=
  InRow r lam ∧ 1/2 ≤ v ∧ v ≤ 1
def LightDomain (r : AnalyticRow) (lam x : ℝ) : Prop :=
  InRow r lam ∧ 0 ≤ x ∧ x ≤ 1

/-- The row domain equals the finite packet's original closed domain. -/
theorem inRow_iff_packet (r : AnalyticRow) (lam : ℝ) :
    InRow r lam ↔ InAnalyticRow r lam := by
  cases r <;> norm_num [InRow, rowLow, rowHigh, InAnalyticRow, analyticPolynomialId,
    Packet.data, CertData.BHeavyB0.l, CertData.BHeavyB0.h,
    CertData.CHeavyB0.l, CertData.CHeavyB0.h, CertData.FHeavyB0.l,
    CertData.FHeavyB0.h, CertData.GHeavyB0.l, CertData.GHeavyB0.h]

theorem rowLow_pos (r : AnalyticRow) : 0 < rowLow r := by
  cases r <;> norm_num [rowLow]

theorem activity_pos {r : AnalyticRow} {lam : ℝ} (h : InRow r lam) : 0 < lam :=
  lt_of_lt_of_le (rowLow_pos r) h.1

theorem q_bounds {lam : ℝ} (hl : 0 < lam) : 0 < q lam ∧ q lam < 1 := by
  have hd : 0 < 1+lam := by linarith
  exact ⟨div_pos hl hd, (div_lt_one hd).2 (by linarith)⟩

/-- The two forms of R in the paper agree whenever the actual denominators are nonzero. -/
theorem rate_identity (kap lam omega : ℝ) (hl : lam ≠ 0) (hw : omega ≠ 0)
    (hd : 1+lam*omega ≠ 0) :
    kap*lam/occupation lam omega = kap*(1/omega+lam) := by
  unfold occupation
  field_simp [hl, hw, hd] <;> ring

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.rowLow
#print axioms Erdos993Lean.BCFG.Analytic.rowLow
#check Erdos993Lean.BCFG.Analytic.rowHigh
#print axioms Erdos993Lean.BCFG.Analytic.rowHigh
#check Erdos993Lean.BCFG.Analytic.theta
#print axioms Erdos993Lean.BCFG.Analytic.theta
#check Erdos993Lean.BCFG.Analytic.alpha
#print axioms Erdos993Lean.BCFG.Analytic.alpha
#check Erdos993Lean.BCFG.Analytic.beta
#print axioms Erdos993Lean.BCFG.Analytic.beta
#check Erdos993Lean.BCFG.Analytic.kappa
#print axioms Erdos993Lean.BCFG.Analytic.kappa
#check Erdos993Lean.BCFG.Analytic.heavyExponent
#print axioms Erdos993Lean.BCFG.Analytic.heavyExponent
#check Erdos993Lean.BCFG.Analytic.massIntercept
#print axioms Erdos993Lean.BCFG.Analytic.massIntercept
#check Erdos993Lean.BCFG.Analytic.massSlope
#print axioms Erdos993Lean.BCFG.Analytic.massSlope
#check Erdos993Lean.BCFG.Analytic.logCenterLower
#print axioms Erdos993Lean.BCFG.Analytic.logCenterLower
#check Erdos993Lean.BCFG.Analytic.logCenterUpper
#print axioms Erdos993Lean.BCFG.Analytic.logCenterUpper
#check Erdos993Lean.BCFG.Analytic.epsilon
#print axioms Erdos993Lean.BCFG.Analytic.epsilon
#check Erdos993Lean.BCFG.Analytic.q
#print axioms Erdos993Lean.BCFG.Analytic.q
#check Erdos993Lean.BCFG.Analytic.occupation
#print axioms Erdos993Lean.BCFG.Analytic.occupation
#check Erdos993Lean.BCFG.Analytic.logMass
#print axioms Erdos993Lean.BCFG.Analytic.logMass
#check Erdos993Lean.BCFG.Analytic.rhoZero
#print axioms Erdos993Lean.BCFG.Analytic.rhoZero
#check Erdos993Lean.BCFG.Analytic.cubicEnvelope
#print axioms Erdos993Lean.BCFG.Analytic.cubicEnvelope
#check Erdos993Lean.BCFG.Analytic.price
#print axioms Erdos993Lean.BCFG.Analytic.price
#check Erdos993Lean.BCFG.Analytic.gamma
#print axioms Erdos993Lean.BCFG.Analytic.gamma
#check Erdos993Lean.BCFG.Analytic.centerResponse
#print axioms Erdos993Lean.BCFG.Analytic.centerResponse
#check Erdos993Lean.BCFG.Analytic.activityCenter
#print axioms Erdos993Lean.BCFG.Analytic.activityCenter
#check Erdos993Lean.BCFG.Analytic.massLine
#print axioms Erdos993Lean.BCFG.Analytic.massLine
#check Erdos993Lean.BCFG.Analytic.ellLower
#print axioms Erdos993Lean.BCFG.Analytic.ellLower
#check Erdos993Lean.BCFG.Analytic.ellUpper
#print axioms Erdos993Lean.BCFG.Analytic.ellUpper
#check Erdos993Lean.BCFG.Analytic.InRow
#print axioms Erdos993Lean.BCFG.Analytic.InRow
#check Erdos993Lean.BCFG.Analytic.Feasible
#print axioms Erdos993Lean.BCFG.Analytic.Feasible
#check Erdos993Lean.BCFG.Analytic.HeavyDomain
#print axioms Erdos993Lean.BCFG.Analytic.HeavyDomain
#check Erdos993Lean.BCFG.Analytic.LightDomain
#print axioms Erdos993Lean.BCFG.Analytic.LightDomain
#check Erdos993Lean.BCFG.Analytic.inRow_iff_packet
#print axioms Erdos993Lean.BCFG.Analytic.inRow_iff_packet
#check Erdos993Lean.BCFG.Analytic.rowLow_pos
#print axioms Erdos993Lean.BCFG.Analytic.rowLow_pos
#check Erdos993Lean.BCFG.Analytic.activity_pos
#print axioms Erdos993Lean.BCFG.Analytic.activity_pos
#check Erdos993Lean.BCFG.Analytic.q_bounds
#print axioms Erdos993Lean.BCFG.Analytic.q_bounds
#check Erdos993Lean.BCFG.Analytic.rate_identity
#print axioms Erdos993Lean.BCFG.Analytic.rate_identity
