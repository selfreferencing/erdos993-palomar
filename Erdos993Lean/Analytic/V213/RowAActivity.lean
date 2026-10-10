module

public import Erdos993Lean.Analytic.V213.RowADefinitions
public import Erdos993Lean.Analytic.V213.RowAEtaAffine
public import Mathlib.Analysis.Convex.Deriv

/-! The four actual activity comparisons in Row A Step 2. The eta lower bound
comes from the separately proved rational logarithm comparison; the other
three comparisons and the positive product chord are proved here. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

open Set

noncomputable def slopeCoefficient (lam x r : ℝ) : ℝ :=
  (1-r)*(1-q lam*x)+(7*lam/20)*(1-q lam*x/2)

theorem slope_chord_identity {lam : ℝ} (hl : 0 < lam) (x r : ℝ) :
    (1-theta lam)*slopeCoefficient (1/3) x r + theta lam*slopeCoefficient (3/5) x r -
      slopeCoefficient lam x r =
    x*((1-r)-7/40)*(lam-1/3)*(3/5-lam)/((4/3)*(8/5)*(1+lam)) := by
  have hd : 1+lam ≠ 0 := by positivity
  unfold theta slopeCoefficient q
  field_simp [hd] <;> ring

theorem slope_le_chord {lam x r : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 ≤ x) (hr : r ≤ 3/8) :
    slopeCoefficient lam x r ≤
      (1-theta lam)*slopeCoefficient (1/3) x r + theta lam*slopeCoefficient (3/5) x r := by
  apply sub_nonneg.mp
  rw [slope_chord_identity (by linarith) x r]
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg hx (by linarith)) (by linarith)) (by linarith)
  · positivity

theorem sigma_chord_identity {lam : ℝ} (hl : 0 < lam) :
    sigma lam-((1-theta lam)*(15/16)+theta lam*(55/64)) =
      (3*lam-1)*(5*lam-3)^2/(256*(1+lam)^2) := by
  have hd : 1+lam ≠ 0 := by positivity
  unfold sigma theta
  field_simp [hd] <;> ring

theorem sigma_ge_chord {lam : ℝ} (hl : 1/3 ≤ lam) :
    (1-theta lam)*(15/16)+theta lam*(55/64) ≤ sigma lam := by
  apply sub_nonneg.mp
  rw [sigma_chord_identity (by linarith)]
  exact div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)

noncomputable def logQuotient (c a : ℝ) : ℝ := a/Real.log (1+c*a)
noncomputable def logQuotientD1 (c a : ℝ) : ℝ :=
  1/Real.log (1+c*a)-a*c/((1+c*a)*Real.log (1+c*a)^2)
noncomputable def logQuotientD2 (c a : ℝ) : ℝ :=
  c*(2*c*a-(2+c*a)*Real.log (1+c*a))/((1+c*a)^2*Real.log (1+c*a)^3)

theorem logQuotient_hasDerivAt {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    HasDerivAt (logQuotient c) (logQuotientD1 c a) a := by
  have hA : 0 < 1+c*a := by positivity
  have hL : 0 < Real.log (1+c*a) := Real.log_pos (by nlinarith)
  have hlog := (((hasDerivAt_id a).const_mul c).const_add 1).log hA.ne'
  convert (hasDerivAt_id a).div hlog hL.ne' using 1 <;>
    first
    | (funext t <;> (try dsimp [logQuotient,logQuotientD1]) <;> ring)
    | (dsimp [logQuotient,logQuotientD1] <;> field_simp [hL.ne',hA.ne'] <;> ring)

theorem logQuotientD1_hasDerivAt {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    HasDerivAt (logQuotientD1 c) (logQuotientD2 c a) a := by
  have hA : 0 < 1+c*a := by positivity
  have hL : 0 < Real.log (1+c*a) := Real.log_pos (by nlinarith)
  have hA' := ((hasDerivAt_id a).const_mul c).const_add 1
  have hlog := hA'.log hA.ne'
  have hden := hA'.mul (hlog.pow 2)
  have h := ((hasDerivAt_const a (1:ℝ)).div hlog hL.ne').sub
    (((hasDerivAt_id a).mul_const c).div hden (by dsimp; positivity))
  convert h using 1 <;>
    first
    | (funext t <;> (try dsimp [logQuotientD1,logQuotientD2]) <;> ring)
    | (dsimp [logQuotientD1,logQuotientD2] <;> field_simp [hL.ne',hA.ne'] <;> ring)

theorem logQuotient_concave {c : ℝ} (hc : 0 < c) :
    ConcaveOn ℝ (Ioi 0) (logQuotient c) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
  · intro a ha
    exact (logQuotient_hasDerivAt hc ha).continuousAt.continuousWithinAt
  · intro a ha
    exact (logQuotient_hasDerivAt hc (interior_subset ha)).hasDerivWithinAt
  · intro a ha
    exact (logQuotientD1_hasDerivAt hc (interior_subset ha)).hasDerivWithinAt
  · intro a ha
    have hap : 0 < a := interior_subset ha
    have hca : 0 < c*a := mul_pos hc hap
    have h := (elementary_log_bounds hca.le).1
    have hcross := (div_le_iff₀ (show 0 < 2+c*a by positivity)).mp h
    unfold logQuotientD2
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc.le (by nlinarith))
      (by have : 0 < Real.log (1+c*a) := Real.log_pos (by linarith); positivity)

theorem logQuotient_childMass {x : ℝ} (hx : x ≠ 0) (lam : ℝ) :
    logQuotient ((1-x)/x) (1+lam) = (1+lam)/childMass lam x := by
  unfold logQuotient childMass
  congr 2
  field_simp [hx] <;> ring

theorem inverse_mass_ge_chord {lam x : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 < x) (hx1 : x < 1) :
    (1-theta lam)*((1+1/3)/childMass (1/3) x)+
      theta lam*((1+3/5)/childMass (3/5) x) ≤ (1+lam)/childMass lam x := by
  have ht := theta_bounds hl hu
  have hc : 0 < (1-x)/x := div_pos (by linarith) hx
  have h := (logQuotient_concave hc).2
    (show (1:ℝ)+1/3 ∈ Ioi 0 by norm_num)
    (show (1:ℝ)+3/5 ∈ Ioi 0 by norm_num)
    (show 0 ≤ 1-theta lam by linarith) ht.1 (by ring : (1-theta lam)+theta lam=1)
  simp only [smul_eq_mul] at h
  have hb : (1-theta lam)*(1+1/3)+theta lam*(1+3/5)=1+lam := by
    unfold theta
    ring
  rw [hb,logQuotient_childMass hx.ne',logQuotient_childMass hx.ne',
    logQuotient_childMass hx.ne'] at h
  exact h

theorem childMass_hasDerivAt {lam x : ℝ} (hl : 0 < lam) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t => childMass t x) ((1-x)/(1+lam*(1-x))) lam := by
  have hxm : 0 < 1-x := sub_pos.mpr hx1
  have hA : 0 < 1+lam*(1-x) := by positivity
  have h := ((((hasDerivAt_id lam).mul_const (1-x)).const_add 1).div_const x).log
    (div_ne_zero hA.ne' hx.ne')
  convert h using 1 <;>
    dsimp [childMass] <;> field_simp [hx.ne',hA.ne'] <;> ring

theorem childMass_concave {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ConcaveOn ℝ (Ioi 0) (fun lam => childMass lam x) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
    (f' := fun lam => (1-x)/(1+lam*(1-x)))
    (f'' := fun lam => -(1-x)^2/(1+lam*(1-x))^2)
  · intro lam hl
    exact (childMass_hasDerivAt hl hx hx1).continuousAt.continuousWithinAt
  · intro lam hl
    exact (childMass_hasDerivAt (interior_subset hl) hx hx1).hasDerivWithinAt
  · intro lam hl
    have hlp : 0 < lam := interior_subset hl
    have hxm : 0 < 1-x := sub_pos.mpr hx1
    have hA : 0 < 1+lam*(1-x) := by positivity
    have h := (hasDerivAt_const lam (1-x)).div
      (((hasDerivAt_id lam).mul_const (1-x)).const_add 1) hA.ne'
    convert h.hasDerivWithinAt using 1 <;>
      first
      | (funext t <;> (try dsimp) <;> ring)
      | (dsimp <;> field_simp [hA.ne'] <;> ring)
  · intro lam hl
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)

theorem childMass_ge_chord {lam x : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 < x) (hx1 : x < 1) :
    (1-theta lam)*childMass (1/3) x+theta lam*childMass (3/5) x ≤ childMass lam x := by
  have ht := theta_bounds hl hu
  have h := (childMass_concave hx hx1).2
    (show (1/3:ℝ) ∈ Ioi 0 by norm_num) (show (3/5:ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ 1-theta lam by linarith) ht.1 (by ring : (1-theta lam)+theta lam=1)
  simpa only [smul_eq_mul,theta_affine] using h

theorem childMass_endpoints_order {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    childMass (1/3) x ≤ childMass (3/5) x := by
  apply Real.log_le_log
  · exact div_pos (by nlinarith) hx
  · apply (div_le_div_iff_of_pos_right hx).2
    nlinarith

theorem eta_mass_ge_chord {lam x : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 < x) (hx1 : x < 1) :
    (1-theta lam)*(343/400)*childMass (1/3) x+
      theta lam*(319/400)*childMass (3/5) x ≤ eta lam*childMass lam x := by
  have ht := theta_bounds hl hu
  have hY := childMass_pos (by linarith : 0 < lam) hx hx1
  have hE : 0 ≤ (373-90*lam)/400 := by linarith
  have h1 := mul_le_mul_of_nonneg_right (eta_lower hl hu) hY.le
  have h2 := mul_le_mul_of_nonneg_left (childMass_ge_chord hl hu hx hx1) hE
  have h3 := mul_nonneg (mul_nonneg ht.1 (show 0 ≤ 1-theta lam by linarith))
    (sub_nonneg.mpr (childMass_endpoints_order hx hx1))
  have he : (373-90*lam)/400 = (1-theta lam)*(343/400)+theta lam*(319/400) := by
    unfold theta
    ring
  rw [he] at h1 h2
  nlinarith

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.slopeCoefficient
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.slopeCoefficient
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotient
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotient
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotientD1
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotientD1
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotientD2
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotientD2
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.slope_chord_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.slope_chord_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.slope_le_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.slope_le_chord
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.sigma_chord_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.sigma_chord_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.sigma_ge_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.sigma_ge_chord
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotient_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotient_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotientD1_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotientD1_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotient_concave
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotient_concave
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotient_childMass
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.logQuotient_childMass
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.inverse_mass_ge_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.inverse_mass_ge_chord
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_concave
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_concave
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_ge_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_ge_chord
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_endpoints_order
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_endpoints_order
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_mass_ge_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_mass_ge_chord
