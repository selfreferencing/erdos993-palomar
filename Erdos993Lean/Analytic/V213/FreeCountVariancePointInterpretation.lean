module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceDefs
public import Erdos993Lean.Analytic.V213.FreeCountVarianceWorksheetCast
public import Erdos993Lean.Analytic.V213.FreeCountLogDispatch

/-!
Actual E/B/P checker premises imply Real point
enclosures.  The E000 endpoint is exact rather than a strict E comparison.
This file proves individual p and f bounds only.  It does NOT infer the
coupled p/f bounds by dividing these independent enclosures; that separate
monotonicity argument is necessary for the ell/rho/K worksheets.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

def ExpEnclosure (e : EPoint) : Prop :=
  (0 : ℝ) < e.lo ∧ (e.lo : ℝ) ≤ exp (e.y : ℝ) ∧ exp (e.y : ℝ) ≤ (e.hi : ℝ)

def BetaEnclosure (b : BPoint) : Prop :=
  (0 : ℝ) < b.lo ∧ (b.lo : ℝ) < logActivity (b.lam : ℝ) ∧
    logActivity (b.lam : ℝ) < (b.hi : ℝ)

theorem exp_enclosure_of_checks (e : EPoint) (hpos : 0 < e.lo)
    (huse : expUseOK e.y = true)
    (hl : (Comparison.ofRats e.lo (F3All.expLower e.y) .lt).check = true)
    (hu : (Comparison.ofRats (F3All.expUpper e.y) e.hi .lt).check = true) :
    ExpEnclosure e := by
  have hy : 0 ≤ e.y ∧ e.y ≤ 3 := of_decide_eq_true huse
  have h := exp_point_of_checks hy.1 hy.2 hl hu
  exact ⟨by exact_mod_cast hpos, h.1.le, h.2.le⟩

/-- No nonexistent strict comparison is required for the supplied E000 row. -/
theorem exp_zero_enclosure : ExpEnclosure ⟨0, 1, 1⟩ := by
  norm_num [ExpEnclosure]

theorem beta_enclosure_of_checks (b : BPoint) (hpos : 0 < b.lo)
    (huse : logUseOK (1+b.lam) = true)
    (hl : (Comparison.ofRats b.lo (logLower (1+b.lam)) .lt).check = true)
    (hu : (Comparison.ofRats (logUpper (1+b.lam)) b.hi .lt).check = true) :
    BetaEnclosure b := by
  have h := log_point_of_checks huse hl hu
  refine ⟨by exact_mod_cast hpos, ?_, ?_⟩
  · simpa [logActivity] using h.1
  · simpa [logActivity] using h.2

private theorem quotient_antitone_den {a x y : ℝ}
    (ha : 0 ≤ a) (hx : 0 < x) (hxy : x ≤ y) : a/y ≤ a/x := by
  have hy : 0 < y := hx.trans_le hxy
  apply (div_le_div_iff₀ hy hx).2
  exact mul_le_mul_of_nonneg_left hxy ha

theorem message_brackets_of_exp {lam y elo ehi : ℝ}
    (hlam : 0 < lam) (helo : 0 < elo)
    (hlo : elo ≤ exp y) (hhi : exp y ≤ ehi) :
    lam/(ehi+lam) ≤ message lam y ∧ message lam y ≤ lam/(elo+lam) := by
  rw [message_eq_exp_quotient hlam]
  constructor
  · exact quotient_antitone_den hlam.le (by positivity) (by linarith)
  · exact quotient_antitone_den hlam.le (by positivity) (by linarith)

theorem point_message_brackets (p : Point) (hlam : 0 < p.b.lam)
    (he : ExpEnclosure p.e) :
    pMinusR p ≤ message (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    message (p.b.lam : ℝ) (p.e.y : ℝ) ≤ pPlusR p := by
  have hlamR : (0 : ℝ) < p.b.lam := by exact_mod_cast hlam
  exact message_brackets_of_exp hlamR he.1 he.2.1 he.2.2

theorem logMass_eq_log_quotient (lam y : ℝ) :
    logMass lam y = log (1+lam/exp y) := by
  rw [logMass_eq_log, Real.exp_neg, div_eq_mul_inv]

/-- The two P endpoints deliberately use ehi for the lower and elo for the upper. -/
theorem parent_log_brackets {lam y elo ehi flo fhi : ℝ}
    (hlam : 0 < lam) (helo : 0 < elo)
    (hlo : elo ≤ exp y) (hhi : exp y ≤ ehi)
    (hflo : flo < log (1+lam/ehi)) (hfhi : log (1+lam/elo) < fhi) :
    flo < logMass lam y ∧ logMass lam y < fhi := by
  have hehi : 0 < ehi := (exp_pos y).trans_le hhi
  have hlfrac := quotient_antitone_den hlam.le (exp_pos y) hhi
  have hufrac := quotient_antitone_den hlam.le helo hlo
  have hllog : log (1+lam/ehi) ≤ log (1+lam/exp y) :=
    Real.log_le_log (by positivity) (by linarith)
  have hulog : log (1+lam/exp y) ≤ log (1+lam/elo) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [logMass_eq_log_quotient]
  exact ⟨hflo.trans_le hllog, hulog.trans_lt hfhi⟩

theorem point_parent_of_checks (p : Point) (hcoord : pointOK p = true)
    (hlam : 0 < p.b.lam) (he : ExpEnclosure p.e)
    (huseL : logUseOK (1+p.f.lam/p.e.hi) = true)
    (huseU : logUseOK (1+p.f.lam/p.e.lo) = true)
    (hl : (Comparison.ofRats p.f.lo (logLower (1+p.f.lam/p.e.hi)) .lt).check = true)
    (hu : (Comparison.ofRats (logUpper (1+p.f.lam/p.e.lo)) p.f.hi .lt).check = true) :
    (p.f.lo : ℝ) < logMass (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    logMass (p.b.lam : ℝ) (p.e.y : ℝ) < (p.f.hi : ℝ) := by
  have hc := pointOK_coordinates hcoord
  have hL := (ofRats_lt_real hl).trans_le (log_envelopes_of_useOK huseL).1
  have hU := (log_envelopes_of_useOK huseU).2.trans_lt (ofRats_lt_real hu)
  have hL' : (p.f.lo : ℝ) < log (1+(p.b.lam : ℝ)/p.e.hi) := by
    simpa only [hc.1, Rat.cast_add, Rat.cast_one, Rat.cast_div] using hL
  have hU' : log (1+(p.b.lam : ℝ)/p.e.lo) < (p.f.hi : ℝ) := by
    simpa only [hc.1, Rat.cast_add, Rat.cast_one, Rat.cast_div] using hU
  exact parent_log_brackets (by exact_mod_cast hlam) he.1 he.2.1 he.2.2 hL' hU'

/-- A zero-parent lookup copies the B endpoints; no P comparison at y=0 is added. -/
theorem zeroParent_enclosure (b : BPoint) (hb : BetaEnclosure b) :
    ((zeroParent b).lo : ℝ) < logMass (b.lam : ℝ) 0 ∧
    logMass (b.lam : ℝ) 0 < ((zeroParent b).hi : ℝ) := by
  simpa only [zeroParent, logMass_zero] using hb.2

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.exp_enclosure_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.exp_enclosure_of_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.exp_zero_enclosure
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.exp_zero_enclosure
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.beta_enclosure_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.beta_enclosure_of_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.message_brackets_of_exp
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.message_brackets_of_exp
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_message_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_message_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.logMass_eq_log_quotient
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.logMass_eq_log_quotient
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.parent_log_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.parent_log_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_parent_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_parent_of_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroParent_enclosure
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroParent_enclosure
