module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceCoupledPoints
public import Erdos993Lean.Analytic.V213.FreeCountACParentFunctions

/-!
Actual analytic values at a single worksheet point.
The coupled p/f inequalities are explicit inputs, supplied by CoupledPoints
from the actual E/B/P checks (or the separate zero-parent branch).
No continuous cell, curvature, concrete record or cover is proved here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Erdos993Lean.ExactComparisons.F3All

private theorem ratio_order {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) : a/d ≤ b/c := by
  apply (div_le_div_iff₀ (hc.trans_le hcd) hc).2
  exact (mul_le_mul_of_nonneg_right hab hc.le).trans
    (mul_le_mul_of_nonneg_left hcd (ha.trans hab))

theorem ell_eq_endpoint_expression {D lam : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    ell D lam y = exp y/lam - y*((1-message lam y)/gamma D lam +
      message lam y/logMass lam y) := by
  rw [ell_normalized hD hlam, h_normalized hlam]
  unfold ap B
  field_simp [(gamma_pos hD hlam).ne', (message_pos hlam y).ne',
    (logMass_pos hlam y).ne'] <;> ring

theorem K_eq_endpoint_expression {D lam : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    K D lam y = (1-message lam y)/D +
      (5/12)*logActivity lam*(message lam y/logMass lam y) := by
  unfold K
  rw [h_normalized hlam]
  unfold gamma B
  field_simp [hD.ne', (message_pos hlam y).ne', (logMass_pos hlam y).ne'] <;> ring

/-- Exact point ell lower bound, including the y=0 endpoint. -/
theorem point_ell_lower (D : Rat) (p : Point)
    (hD : 0 < D) (hlam : 0 < p.b.lam) (hy : 0 ≤ p.e.y)
    (he : ExpEnclosure p.e) (hb : BetaEnclosure p.b)
    (hpf : message (p.b.lam : ℝ) (p.e.y : ℝ)/
      logMass (p.b.lam : ℝ) (p.e.y : ℝ) ≤ pMinusR p/(p.f.lo : ℝ)) :
    ellMinusR D p ≤ ell (D : ℝ) (p.b.lam : ℝ) (p.e.y : ℝ) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hlR : (0 : ℝ) < p.b.lam := by exact_mod_cast hlam
  have hyR : (0 : ℝ) ≤ p.e.y := by exact_mod_cast hy
  have hpm := (point_message_brackets p hlam he).1
  have hn : 0 ≤ 1-message (p.b.lam : ℝ) (p.e.y : ℝ) :=
    (sub_pos.mpr (message_lt_one hlR _)).le
  have hblo : (0 : ℝ) < p.b.lo := hb.1
  have hdlo : 0 < (5*(D : ℝ)/12)*(p.b.lo : ℝ) := by positivity
  have hd : (5*(D : ℝ)/12)*(p.b.lo : ℝ) ≤ gamma (D : ℝ) (p.b.lam : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hb.2.1.le
      (show 0 ≤ 5*(D : ℝ)/12 by positivity)
    convert hh using 1 <;> unfold gamma <;> ring
  have hfrac := ratio_order hn (sub_le_sub_left hpm 1) hdlo hd
  have hsum := add_le_add hfrac hpf
  have hproduct := mul_le_mul_of_nonneg_left hsum hyR
  have hfirst := div_le_div_of_nonneg_right he.2.1 hlR.le
  rw [ell_eq_endpoint_expression hDR hlR]
  unfold ellMinusR
  exact sub_le_sub hfirst hproduct

/-- Invert the already coupled p/f bounds; independent p and f brackets are not used. -/
theorem point_B_brackets (p : Point) (hlam : 0 < p.b.lam)
    (he : ExpEnclosure p.e) (hflo : (0 : ℝ) < p.f.lo)
    (hfhi : (0 : ℝ) < p.f.hi)
    (hpf : pPlusR p/(p.f.hi : ℝ) ≤
      message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ∧
      message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ≤
        pMinusR p/(p.f.lo : ℝ)) :
    (p.f.lo : ℝ)/pMinusR p ≤ B (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    B (p.b.lam : ℝ) (p.e.y : ℝ) ≤ (p.f.hi : ℝ)/pPlusR p := by
  have hlR : (0 : ℝ) < p.b.lam := by exact_mod_cast hlam
  have hu := message_pos hlR (p.e.y : ℝ)
  have hf := logMass_pos hlR (p.e.y : ℝ)
  have hehi : (0 : ℝ) < p.e.hi := (exp_pos _).trans_le he.2.2
  have hpm := (fraction_message_domain hlR hehi).1
  have hpp := (fraction_message_domain hlR he.1).1
  change 0 < pMinusR p at hpm
  change 0 < pPlusR p at hpp
  constructor
  · unfold B
    apply (div_le_div_iff₀ hpm hu).2
    have hh := (div_le_div_iff₀ hf hflo).1 hpf.2
    simpa only [mul_comm] using hh
  · unfold B
    apply (div_le_div_iff₀ hu hpp).2
    have hh := (div_le_div_iff₀ hfhi hf).1 hpf.1
    simpa only [mul_comm] using hh

theorem point_rho_brackets (p : Point) (hlam : 0 < p.b.lam)
    (hy : 0 ≤ p.e.y) (he : ExpEnclosure p.e) (hb : BetaEnclosure p.b)
    (hflo : (0 : ℝ) < p.f.lo) (hfhi : (0 : ℝ) < p.f.hi)
    (hpf : pPlusR p/(p.f.hi : ℝ) ≤
      message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ∧
      message (p.b.lam : ℝ) (p.e.y : ℝ)/logMass (p.b.lam : ℝ) (p.e.y : ℝ) ≤
        pMinusR p/(p.f.lo : ℝ)) :
    rhoMinusR p ≤ rho (p.b.lam : ℝ) (p.e.y : ℝ) ∧
    rho (p.b.lam : ℝ) (p.e.y : ℝ) ≤ rhoPlusR p := by
  have hlR : (0 : ℝ) < p.b.lam := by exact_mod_cast hlam
  have hyR : (0 : ℝ) ≤ p.e.y := by exact_mod_cast hy
  have hB := point_B_brackets p hlam he hflo hfhi hpf
  have hbeta := logActivity_pos hlR
  have hq := q_pos hlR
  have hehi : (0 : ℝ) < p.e.hi := (exp_pos _).trans_le he.2.2
  have hpm : 0 < pMinusR p := (fraction_message_domain hlR hehi).1
  have hpp : 0 < pPlusR p := (fraction_message_domain hlR he.1).1
  have hlow := ratio_order (div_pos hflo hpm).le hB.1 hbeta hb.2.2.le
  have hupp := ratio_order (B_pos hlR _).le hB.2 hb.1 hb.2.1.le
  have hlq := mul_le_mul_of_nonneg_right hlow hq.le
  have huq := mul_le_mul_of_nonneg_right hupp hq.le
  constructor
  · convert hlq using 1 <;>
      simp only [rhoMinusR, rho, qAtR, q, div_eq_mul_inv, mul_inv_rev] <;> ring
  · apply le_min (rho_le_one hlR hyR)
    convert huq using 1 <;>
      simp only [rhoPlusR, rho, qAtR, q, div_eq_mul_inv, mul_inv_rev] <;> ring

theorem point_K_upper (D : Rat) (p : Point)
    (hD : 0 < D) (hlam : 0 < p.b.lam)
    (he : ExpEnclosure p.e) (hb : BetaEnclosure p.b)
    (hpf : message (p.b.lam : ℝ) (p.e.y : ℝ)/
      logMass (p.b.lam : ℝ) (p.e.y : ℝ) ≤ pMinusR p/(p.f.lo : ℝ)) :
    K (D : ℝ) (p.b.lam : ℝ) (p.e.y : ℝ) ≤ kPlusR D p := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hlR : (0 : ℝ) < p.b.lam := by exact_mod_cast hlam
  have hpm := (point_message_brackets p hlam he).1
  have hfirst := div_le_div_of_nonneg_right (sub_le_sub_left hpm 1) hDR.le
  have hbeta := logActivity_pos hlR
  have hbetahi : (0 : ℝ) < p.b.hi := hbeta.trans hb.2.2
  have hpfpos := div_pos (message_pos hlR (p.e.y : ℝ)) (logMass_pos hlR (p.e.y : ℝ))
  have hprod := mul_le_mul hb.2.2.le hpf hpfpos.le hbetahi.le
  have hterm := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 5/12 by norm_num)
  rw [K_eq_endpoint_expression hDR hlR]
  unfold kPlusR
  convert add_le_add hfirst hterm using 1 <;> ring

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ell_eq_endpoint_expression
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ell_eq_endpoint_expression
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.K_eq_endpoint_expression
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.K_eq_endpoint_expression
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_ell_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_ell_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_B_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_B_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_rho_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_rho_brackets
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_K_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.point_K_upper
