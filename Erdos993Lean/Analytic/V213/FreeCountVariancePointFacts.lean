module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointBounds

/-!
Finite-family interface. PointFacts exposes precisely the point
enclosures needed by the worksheet interpretation, not CA/AC or a cell bound.
Positive-y P rows retain four checked literal lookups. The zero branch uses
the exact exponential and the B row without inventing P comparisons at zero.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All

structure PointFacts (p : Point) : Prop where
  activity_pos : 0 < p.b.lam
  parent_nonneg : 0 ≤ p.e.y
  exp_bounds : ExpEnclosure p.e
  beta_bounds : BetaEnclosure p.b
  parent_lower_pos : 0 < p.f.lo
  parent_upper_pos : (0 : ℝ) < p.f.hi
  coupled_ratio :
    pPlusR p/(p.f.hi : ℝ) ≤
      message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ≤
      pMinusR p/(p.f.lo : ℝ)

theorem pointFacts_of_quoted_checks (p : Point) (lamL expL lamU expU : Rat)
    (hcoord : pointOK p = true) (hlam : 0 < p.b.lam) (hy : 0 ≤ p.e.y)
    (he : ExpEnclosure p.e) (hb : BetaEnclosure p.b) (hflo : 0 < p.f.lo)
    (hLamL : (Comparison.ofRats lamL p.f.lam .eq).check = true)
    (hExpL : (Comparison.ofRats expL p.e.hi .eq).check = true)
    (hLamU : (Comparison.ofRats lamU p.f.lam .eq).check = true)
    (hExpU : (Comparison.ofRats expU p.e.lo .eq).check = true)
    (huseL : logUseOK (1+lamL/expL) = true)
    (huseU : logUseOK (1+lamU/expU) = true)
    (hl : (Comparison.ofRats p.f.lo (logLower (1+lamL/expL)) .lt).check = true)
    (hu : (Comparison.ofRats (logUpper (1+lamU/expU)) p.f.hi .lt).check = true) :
    PointFacts p := by
  have h1 : lamL = p.f.lam := Comparison.ofRats_sound _ _ .eq hLamL
  have h2 : expL = p.e.hi := Comparison.ofRats_sound _ _ .eq hExpL
  have h3 : lamU = p.f.lam := Comparison.ofRats_sound _ _ .eq hLamU
  have h4 : expU = p.e.lo := Comparison.ofRats_sound _ _ .eq hExpU
  rw [h1, h2] at huseL hl
  rw [h3, h4] at huseU hu
  have hp := point_parent_of_checks p hcoord hlam he huseL huseU hl hu
  have hf := logMass_pos (show (0 : ℝ) < p.b.lam by exact_mod_cast hlam) (p.e.y : ℝ)
  exact ⟨hlam, hy, he, hb, hflo, hf.trans hp.2,
    point_coupled_ratio_of_checks p hcoord hlam he hflo huseL huseU hl hu⟩

def zeroPoint (b : BPoint) : Point := ⟨⟨0, 1, 1⟩, b, zeroParent b⟩

theorem zeroPoint_facts (b : BPoint) (hlam : 0 < b.lam) (hb : BetaEnclosure b) :
    PointFacts (zeroPoint b) := by
  have hlR : (0 : ℝ) < b.lam := by exact_mod_cast hlam
  refine ⟨hlam, by norm_num [zeroPoint], exp_zero_enclosure, hb,
    ?_, ?_, ?_⟩
  · change 0 < b.lo
    exact_mod_cast hb.1
  · change (0 : ℝ) < b.hi
    exact (logActivity_pos hlR).trans hb.2.2
  · simpa [zeroPoint, pPlusR, pMinusR, zeroParent, q] using
      zeroParent_coupled_ratio b hlam hb

theorem PointFacts.ell_lower {p : Point} (hp : PointFacts p)
    (D : Rat) (hD : 0 < D) :
    ellMinusR D p ≤ ell (D : ℝ) (p.b.lam : ℝ) (p.e.y : ℝ) :=
  point_ell_lower D p hD hp.activity_pos hp.parent_nonneg hp.exp_bounds
    hp.beta_bounds hp.coupled_ratio.2

theorem PointFacts.rho_brackets {p : Point} (hp : PointFacts p) :
    rhoMinusR p ≤ rho (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    rho (p.b.lam : ℝ) (p.e.y : ℝ) ≤ rhoPlusR p :=
  point_rho_brackets p hp.activity_pos hp.parent_nonneg hp.exp_bounds
    hp.beta_bounds (by exact_mod_cast hp.parent_lower_pos) hp.parent_upper_pos hp.coupled_ratio

theorem PointFacts.K_upper {p : Point} (hp : PointFacts p)
    (D : Rat) (hD : 0 < D) :
    K (D : ℝ) (p.b.lam : ℝ) (p.e.y : ℝ) ≤ kPlusR D p :=
  point_K_upper D p hD hp.activity_pos hp.exp_bounds hp.beta_bounds hp.coupled_ratio.2

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pointFacts_of_quoted_checks
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pointFacts_of_quoted_checks
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.zeroPoint_facts
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.PointFacts.ell_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.PointFacts.ell_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.PointFacts.rho_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.PointFacts.rho_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.PointFacts.K_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.PointFacts.K_upper
