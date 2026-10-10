module

public import Erdos993Lean.Analytic.V213.FreeCountVariancePointFacts
public import Erdos993Lean.Analytic.V213.FreeCountACActivityCells

/-!
Interpretation of the C/A worksheet records. The record facts
contain the actual coordinate guards and the point enclosures separately.
They do not assume a continuous CA/AC conclusion. This file discharges the
rho, K and W rectangle bounds of an A row from those point facts. The extra
D >= 6/5 premise needed later for T curvature is not inferred from aRowOK.
No concrete list, numerical comparison, or cover is evaluated here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Set Erdos993Lean.ExactComparisons.F3All

structure CRowFacts (r : CRow) : Prop where
  checked : cRowOK r = true
  left : PointFacts r.left
  right : PointFacts r.right

structure ARowFacts (r : ARow) : Prop where
  checked : aRowOK r = true
  ac : PointFacts r.ac
  ad : PointFacts r.ad
  bd : PointFacts r.bd
  mid : ExpEnclosure r.mid

theorem ARowFacts.rho_bounds {r : ARow} (hr : ARowFacts r) {lam y : ℝ}
    (hlam : lam ∈ Icc (r.ac.b.lam : ℝ) (r.bd.b.lam : ℝ))
    (hy : y ∈ Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ)) :
    rhoMinusR r.bd ≤ rho lam y ∧ rho lam y ≤ rhoPlusR r.ac := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  have hh := rho_rectangle_bounds (by linarith : (0 : ℝ) < r.ac.b.lam)
    hb7 hc hlam hy
  exact ⟨hr.bd.rho_brackets.1.trans hh.1, hh.2.trans hr.ac.rho_brackets.2⟩

theorem ARowFacts.K_upper {r : ARow} (hr : ARowFacts r) {lam y : ℝ}
    (hlam : lam ∈ Icc (r.ac.b.lam : ℝ) (r.bd.b.lam : ℝ))
    (hy : y ∈ Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ)) :
    K (r.D : ℝ) lam y ≤ cellKR r := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  have hDR : 0 < r.D := by exact_mod_cast hD
  have hleft := hr.ad.K_upper r.D hDR
  rw [had, hyd] at hleft
  have hright := hr.bd.K_upper r.D hDR
  have hh := K_le_rectangle_endpoints hD ha hab hc hlam hy
  apply hh.trans
  unfold cellKR
  exact add_le_add (max_le_max hleft hright) le_rfl

theorem ARowFacts.K_positive {r : ARow} (hr : ARowFacts r) : 0 < cellKR r := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  have hp := K_pos hD (by linarith : (0 : ℝ) < r.ac.b.lam) (r.ac.e.y : ℝ)
  exact hp.trans_le (hr.K_upper ⟨le_rfl, hab.le⟩ ⟨le_rfl, hcd.le⟩)

/-- Lowering beta and exp is safe before the subtraction, because all
denominators and lower numerators are positive. -/
theorem ARowFacts.delta_le_analytic_lower {r : ARow} (hr : ARowFacts r) :
    cellDeltaR r ≤
      (5/12:ℝ) * (logActivity (r.bd.b.lam : ℝ) * exp (r.ac.e.y : ℝ) /
        (r.bd.b.lam : ℝ) + 2 * betaRatio (r.bd.b.lam : ℝ)) -
      (r.bd.e.y : ℝ) * cellKR r := by
  have hb : (0 : ℝ) < r.bd.b.lam := by exact_mod_cast hr.bd.activity_pos
  have hbeta := hr.bd.beta_bounds
  have he := hr.ac.exp_bounds
  have hprod := mul_le_mul hbeta.2.1.le he.2.1 he.1.le
    (logActivity_pos hb).le
  have hfirst := div_le_div_of_nonneg_right hprod hb.le
  have hq := q_pos hb
  have hlo : 0 ≤ (r.bd.b.lo : ℝ) / q (r.bd.b.lam : ℝ) :=
    (div_pos hbeta.1 hq).le
  have hquot := div_le_div_of_nonneg_right hbeta.2.1.le hq.le
  have hsq : ((r.bd.b.lo : ℝ) / q (r.bd.b.lam : ℝ))^2 ≤
      (logActivity (r.bd.b.lam : ℝ) / q (r.bd.b.lam : ℝ))^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hquot)
      (add_nonneg (hlo.trans hquot) hlo)
    nlinarith only [hh]
  have hsecond := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ)≤2))
    (show 0≤1+(r.bd.b.lam : ℝ) by linarith)
  unfold cellDeltaR betaRatio qAtR q at *
  simp only [mul_div_assoc] at hfirst hsecond ⊢
  linarith only [hfirst, hsecond]

theorem ARowFacts.W_lower {r : ARow} (hr : ARowFacts r) {lam y : ℝ}
    (hlam : lam ∈ Icc (r.ac.b.lam : ℝ) (r.bd.b.lam : ℝ))
    (hy : y ∈ Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ)) :
    cellDeltaR r ≤ W (r.D : ℝ) lam y := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  have hh := W_ge_rectangle_lower hD (by linarith [hlam.1] : 0<lam)
    hlam.2 hc hy (hr.K_upper hlam hy)
  exact hr.delta_le_analytic_lower.trans hh

/-- The lower rho endpoint used in the omega interpolation is positive;
positivity does not follow merely from being a lower bound. -/
theorem PointFacts.rho_lower_positive {p : Point} (hp : PointFacts p) :
    0 < rhoMinusR p := by
  have hl : (0:ℝ)<p.b.lam := by exact_mod_cast hp.activity_pos
  have hq := q_pos hl
  have hehi : (0:ℝ)<p.e.hi := (exp_pos _).trans_le hp.exp_bounds.2.2
  have hpm : 0<pMinusR p := (fraction_message_domain hl hehi).1
  have hf : (0:ℝ)<p.f.lo := by exact_mod_cast hp.parent_lower_pos
  have hb : (0:ℝ)<p.b.hi := (logActivity_pos hl).trans hp.beta_bounds.2.2
  change 0<q (p.b.lam : ℝ)*(p.f.lo : ℝ)/(pMinusR p*(p.b.hi : ℝ))
  positivity

theorem ARowFacts.midpoint_domain {r : ARow} (hr : ARowFacts r) :
    (r.mid.y : ℝ) ∈ Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ) ∧
    0 ≤ (r.mid.y : ℝ) ∧ 0 ≤ cellWidthR r := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  unfold cellWidthR
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

theorem ARowFacts.midpoint_distance {r : ARow} (hr : ARowFacts r) {y : ℝ}
    (hy : y ∈ Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ)) :
    |y-(r.mid.y : ℝ)| ≤ cellWidthR r := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  unfold cellWidthR
  apply abs_le.mpr
  constructor <;> linarith [hy.1, hy.2]

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.rho_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.rho_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.K_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.K_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.K_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.K_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.delta_le_analytic_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.delta_le_analytic_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.W_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.W_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.PointFacts.rho_lower_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.PointFacts.rho_lower_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.midpoint_domain
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.midpoint_domain
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.midpoint_distance
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.midpoint_distance
