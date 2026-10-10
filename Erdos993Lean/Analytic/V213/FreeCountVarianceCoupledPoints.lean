module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointInterpretation
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds

/-!
The actual coupled bounds in T1 equation (21).
The lower P check is interpreted at pMinus, not just at the actual message.
The last wrapper requires all four literal parent-lookup equalities; pointOK
alone supplies neither an exp lookup nor a log-endpoint inequality.
No concrete record/check is discharged in this generic file.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

theorem fraction_message_domain {lam e : ℝ} (hlam : 0 < lam) (he : 0 < e) :
    0 < lam/(e+lam) ∧ lam/(e+lam) < 1 := by
  have hd : 0 < e+lam := add_pos he hlam
  exact ⟨div_pos hlam hd, (div_lt_one hd).2 (by linarith)⟩

theorem scalarLog_fraction {lam e : ℝ} (hlam : 0 < lam) (he : 0 < e) :
    scalarLog (lam/(e+lam)) = log (1+lam/e) := by
  have hp := fraction_message_domain hlam he
  have hd : e+lam ≠ 0 := ne_of_gt (add_pos he hlam)
  have hone : 1-lam/(e+lam) ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  rw [← log_odds_eq hp.2]
  congr 1
  field_simp [he.ne', hd, hone]
  ring

/-- The two actual strict log checks give bounds at the two *different* message endpoints. -/
theorem point_scalar_endpoint_brackets (p : Point) (hcoord : pointOK p = true)
    (hlam : 0 < p.b.lam) (he : ExpEnclosure p.e)
    (huseL : logUseOK (1+p.f.lam/p.e.hi) = true)
    (huseU : logUseOK (1+p.f.lam/p.e.lo) = true)
    (hl : (Comparison.ofRats p.f.lo (logLower (1+p.f.lam/p.e.hi)) .lt).check = true)
    (hu : (Comparison.ofRats (logUpper (1+p.f.lam/p.e.lo)) p.f.hi .lt).check = true) :
    (p.f.lo : ℝ) < scalarLog (pMinusR p) ∧ scalarLog (pPlusR p) < (p.f.hi : ℝ) := by
  have hc := pointOK_coordinates hcoord
  have hlamR : (0 : ℝ) < p.b.lam := by exact_mod_cast hlam
  have hehi : (0 : ℝ) < p.e.hi := (exp_pos (p.e.y : ℝ)).trans_le he.2.2
  have hL := (ofRats_lt_real hl).trans_le (log_envelopes_of_useOK huseL).1
  have hU := (log_envelopes_of_useOK huseU).2.trans_lt (ofRats_lt_real hu)
  constructor
  · rw [pMinusR, scalarLog_fraction hlamR hehi]
    simpa only [hc.1, Rat.cast_add, Rat.cast_one, Rat.cast_div] using hL
  · rw [pPlusR, scalarLog_fraction hlamR he.1]
    simpa only [hc.1, Rat.cast_add, Rat.cast_one, Rat.cast_div] using hU

/-- Antitonicity is applied before weakening the *coupled* log endpoints. -/
theorem point_coupled_ratio_bounds (p : Point) (hlam : 0 < p.b.lam)
    (he : ExpEnclosure p.e) (hflo : (0 : ℝ) < p.f.lo)
    (hlo : (p.f.lo : ℝ) ≤ scalarLog (pMinusR p))
    (hhi : scalarLog (pPlusR p) ≤ (p.f.hi : ℝ)) :
    pPlusR p/(p.f.hi : ℝ) ≤ message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ≤ pMinusR p/(p.f.lo : ℝ) := by
  have hlamR : (0 : ℝ) < p.b.lam := by exact_mod_cast hlam
  have hehi : (0 : ℝ) < p.e.hi := (exp_pos (p.e.y : ℝ)).trans_le he.2.2
  have hm : 0 < pMinusR p ∧ pMinusR p < 1 := fraction_message_domain hlamR hehi
  have hp : 0 < pPlusR p ∧ pPlusR p < 1 := fraction_message_domain hlamR he.1
  have ha := message_pos hlamR (p.e.y : ℝ)
  have ha1 := message_lt_one hlamR (p.e.y : ℝ)
  have hbr := point_message_brackets p hlam he
  have hslm := scalarLog_pos hm.1 hm.2
  have hslp := scalarLog_pos hp.1 hp.2
  have huf : (0 : ℝ) < p.f.hi := hslp.trans_le hhi
  have hmonL := scalarH_antitone ⟨ha, ha1⟩ hp hbr.2
  have hmonU := scalarH_antitone hm ⟨ha, ha1⟩ hbr.1
  have heq : scalarH (message (p.b.lam : ℝ) (p.e.y : ℝ)) =
      message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) := by
    simp only [scalarH, scalarLog, logMass_eq_neg_log hlamR]
  rw [heq] at hmonL hmonU
  constructor
  · apply le_trans ?_ hmonL
    unfold scalarH
    apply (div_le_div_iff₀ huf hslp).2
    exact mul_le_mul_of_nonneg_left hhi hp.1.le
  · apply le_trans hmonU
    unfold scalarH
    apply (div_le_div_iff₀ hslm hflo).2
    exact mul_le_mul_of_nonneg_left hlo hm.1.le

theorem point_coupled_ratio_of_checks (p : Point) (hcoord : pointOK p = true)
    (hlam : 0 < p.b.lam) (he : ExpEnclosure p.e) (hflo : 0 < p.f.lo)
    (huseL : logUseOK (1+p.f.lam/p.e.hi) = true)
    (huseU : logUseOK (1+p.f.lam/p.e.lo) = true)
    (hl : (Comparison.ofRats p.f.lo (logLower (1+p.f.lam/p.e.hi)) .lt).check = true)
    (hu : (Comparison.ofRats (logUpper (1+p.f.lam/p.e.lo)) p.f.hi .lt).check = true) :
    pPlusR p/(p.f.hi : ℝ) ≤ message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ≤ pMinusR p/(p.f.lo : ℝ) := by
  have hb := point_scalar_endpoint_brackets p hcoord hlam he huseL huseU hl hu
  exact point_coupled_ratio_bounds p hlam he (by exact_mod_cast hflo) hb.1.le hb.2.le

/-- The original P-side expressions quote their own rational lambda/e values.
Each quoted value must be identified with the appropriate point field using
the actual four ParentLookupEquality checks before the coupling theorem applies. -/
theorem point_coupled_ratio_of_quoted_checks (p : Point)
    (lamL expL lamU expU : Rat)
    (hcoord : pointOK p = true) (hlam : 0 < p.b.lam)
    (he : ExpEnclosure p.e) (hflo : 0 < p.f.lo)
    (hLamL : (Comparison.ofRats lamL p.f.lam .eq).check = true)
    (hExpL : (Comparison.ofRats expL p.e.hi .eq).check = true)
    (hLamU : (Comparison.ofRats lamU p.f.lam .eq).check = true)
    (hExpU : (Comparison.ofRats expU p.e.lo .eq).check = true)
    (huseL : logUseOK (1+lamL/expL) = true)
    (huseU : logUseOK (1+lamU/expU) = true)
    (hl : (Comparison.ofRats p.f.lo (logLower (1+lamL/expL)) .lt).check = true)
    (hu : (Comparison.ofRats (logUpper (1+lamU/expU)) p.f.hi .lt).check = true) :
    pPlusR p/(p.f.hi : ℝ) ≤ message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ≤ pMinusR p/(p.f.lo : ℝ) := by
  have h1 : lamL = p.f.lam := Comparison.ofRats_sound _ _ .eq hLamL
  have h2 : expL = p.e.hi := Comparison.ofRats_sound _ _ .eq hExpL
  have h3 : lamU = p.f.lam := Comparison.ofRats_sound _ _ .eq hLamU
  have h4 : expU = p.e.lo := Comparison.ofRats_sound _ _ .eq hExpU
  rw [h1, h2] at huseL hl
  rw [h3, h4] at huseU hu
  exact point_coupled_ratio_of_checks p hcoord hlam he hflo huseL huseU hl hu

/-- The y=0 branch uses the B bracket directly, with no artificial P-side check. -/
theorem zeroParent_coupled_ratio (b : BPoint) (hlam : 0 < b.lam)
    (hb : BetaEnclosure b) :
    q (b.lam : ℝ)/(b.hi : ℝ) ≤
      message (b.lam : ℝ) 0/logMass (b.lam : ℝ) 0 ∧
    message (b.lam : ℝ) 0/logMass (b.lam : ℝ) 0 ≤ q (b.lam : ℝ)/(b.lo : ℝ) := by
  have hlamR : (0 : ℝ) < b.lam := by exact_mod_cast hlam
  have hq := q_pos hlamR
  have hbeta := logActivity_pos hlamR
  have hhi : (0 : ℝ) < b.hi := hbeta.trans hb.2.2
  rw [message_zero, logMass_zero]
  constructor
  · apply (div_le_div_iff₀ hhi hbeta).2
    exact mul_le_mul_of_nonneg_left hb.2.2.le hq.le
  · apply (div_le_div_iff₀ hbeta hb.1).2
    exact mul_le_mul_of_nonneg_left hb.2.1.le hq.le

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.fraction_message_domain
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.fraction_message_domain
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.scalarLog_fraction
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.scalarLog_fraction
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_scalar_endpoint_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_scalar_endpoint_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_coupled_ratio_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_coupled_ratio_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_coupled_ratio_of_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_coupled_ratio_of_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_coupled_ratio_of_quoted_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_coupled_ratio_of_quoted_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroParent_coupled_ratio
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroParent_coupled_ratio
