module

public import Erdos993Lean.Analytic.V213.RowAActivity

/-! Actual Step 2 interpolation and Step 5 leaf positivity. No endpoint payment
positivity is hidden in a global hypothesis: only the final nonleaf corollary
explicitly waits for the two endpoint inequalities proved by the six quadratics. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

noncomputable def relaxedPsi (lam x r z : ℝ) : ℝ :=
  sigma lam*x*(1-r)^2-slopeCoefficient lam x r*z^2+
    (7*(1+lam)/(20*x*childMass lam x))*(1-z)^2+(z-(1-r))+
    (7/6)*(z-1+eta lam*(1-r)*childMass lam x)

theorem relaxedPsi_le_psi {lam x r z : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : relaxedPsi lam x r z ≤ psi lam x r z := by
  have hq := q_bounds (show 0 < lam by linarith)
  have hp0 : 0 ≤ q lam*x := mul_nonneg hq.1.le hx
  have hp1 : q lam*x < 1 := by nlinarith
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (messageRatio_weak_bounds hp0 hp1).2
      (show 0 ≤ 7*lam/20 by linarith)) (sq_nonneg z)
  unfold relaxedPsi psi slopeCoefficient
  linarith

theorem interpolation_difference {lam x r z : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 < x) (hx1 : x < 1) :
    relaxedPsi lam x r z -
      ((1-theta lam)*endpointPsi (1/3) (343/400) (15/16) x r z+
       theta lam*endpointPsi (3/5) (319/400) (55/64) x r z) =
    (sigma lam-((1-theta lam)*(15/16)+theta lam*(55/64)))*x*(1-r)^2+
    ((1-theta lam)*slopeCoefficient (1/3) x r+
      theta lam*slopeCoefficient (3/5) x r-slopeCoefficient lam x r)*z^2+
    (7/(20*x))*((1+lam)/childMass lam x-
      ((1-theta lam)*((1+1/3)/childMass (1/3) x)+
       theta lam*((1+3/5)/childMass (3/5) x)))*(1-z)^2+
    (7/6)*(1-r)*(eta lam*childMass lam x-
      ((1-theta lam)*(343/400)*childMass (1/3) x+
       theta lam*(319/400)*childMass (3/5) x)) := by
  have hY := childMass_pos (show 0 < lam by linarith) hx hx1
  have hM := childMass_pos (by norm_num : (0:ℝ)<1/3) hx hx1
  have hP := childMass_pos (by norm_num : (0:ℝ)<3/5) hx hx1
  unfold relaxedPsi endpointPsi slopeCoefficient
  field_simp [hx.ne',hY.ne',hM.ne',hP.ne'] <;> ring

theorem psi_ge_endpoint_chord {lam x r z : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 < x) (hx1 : x < 1) (hr : r ≤ 3/8) :
    (1-theta lam)*endpointPsi (1/3) (343/400) (15/16) x r z+
      theta lam*endpointPsi (3/5) (319/400) (55/64) x r z ≤ psi lam x r z := by
  apply le_trans _ (relaxedPsi_le_psi hl hu hx.le hx1.le)
  apply sub_nonneg.mp
  rw [interpolation_difference hl hu hx hx1]
  have hS := sub_nonneg.mpr (sigma_ge_chord hl)
  have hC := sub_nonneg.mpr (slope_le_chord hl hu hx.le hr)
  have hY := sub_nonneg.mpr (inverse_mass_ge_chord hl hu hx hx1)
  have hE := sub_nonneg.mpr (eta_mass_ge_chord hl hu hx hx1)
  have hr0 : 0 ≤ 1-r := by linarith
  positivity

theorem positive_chord {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 < (1-t)*a+t*b := by
  by_cases h : t=1
  · simpa [h] using hb
  have htp : 0 < 1-t := sub_pos.mpr (lt_of_le_of_ne ht1 h)
  exact add_pos_of_pos_of_nonneg (mul_pos htp ha) (mul_nonneg ht0 hb.le)

theorem psi_pos_of_endpoint_pos {lam x r z : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 < x) (hx1 : x < 1) (hr : r ≤ 3/8)
    (hminus : 0 < endpointPsi (1/3) (343/400) (15/16) x r z)
    (hplus : 0 < endpointPsi (3/5) (319/400) (55/64) x r z) : 0 < psi lam x r z :=
  (positive_chord (theta_bounds hl hu).1 (theta_bounds hl hu).2 hminus hplus).trans_le
    (psi_ge_endpoint_chord hl hu hx hx1 hr)

theorem leafPsi_ge_endpoint_chord {lam r : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hr : r ≤ 3/8) :
    (1-theta lam)*((15/16)*(r-1/15)^2+13/160)+
      theta lam*((55/64)*(r-3/55)^2+1077/17600) ≤ leafPsi lam r := by
  have hq := q_bounds (show 0 < lam by linarith)
  have hH := mul_le_mul_of_nonneg_left (messageRatio_weak_bounds hq.1.le hq.2).2
    (show 0 ≤ 7*lam/20 by linarith)
  have hS := mul_le_mul_of_nonneg_right (sigma_ge_chord hl) (sq_nonneg (1-r))
  have hC := slope_le_chord hl hu (by norm_num : (0:ℝ) ≤ 1) hr
  rw [← leaf_endpoint_minus r,← leaf_endpoint_plus r]
  unfold slopeCoefficient at hC
  norm_num only [q,one_mul,mul_one] at hC
  unfold leafPsi q
  dsimp only [q] at hH
  nlinarith

theorem leafPsi_pos {lam r : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5) (hr : r ≤ 3/8) :
    0 < leafPsi lam r :=
  (positive_chord (theta_bounds hl hu).1 (theta_bounds hl hu).2
    (leaf_endpoint_minus_pos r) (leaf_endpoint_plus_pos r)).trans_le
      (leafPsi_ge_endpoint_chord hl hu hr)

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.relaxedPsi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.relaxedPsi
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.relaxedPsi_le_psi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.relaxedPsi_le_psi
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.interpolation_difference
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.interpolation_difference
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.psi_ge_endpoint_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.psi_ge_endpoint_chord
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.positive_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.positive_chord
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.psi_pos_of_endpoint_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.psi_pos_of_endpoint_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leafPsi_ge_endpoint_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leafPsi_ge_endpoint_chord
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leafPsi_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leafPsi_pos
