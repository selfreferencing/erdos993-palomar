module

public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds
public import Mathlib.Analysis.Convex.Deriv

/-!
Analytic proof of the actual lambda/log (1+lambda) tangent used in
T1 Lemma 3.2. Concavity follows from the proved log-star inequality.
The rounded coefficients use the already proved current log2 brackets.
No cap theorem, numerical row or implicit unproved analytic premise is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform

open Real Set Envelopes

noncomputable def activityRatio (x : ℝ) : ℝ := x/log (1+x)
noncomputable def activityRatioSlope (x : ℝ) : ℝ :=
  (log (1+x)-x/(1+x))/(log (1+x))^2

theorem hasDerivAt_activityRatio {x : ℝ} (hx : 0 < x) :
    HasDerivAt activityRatio (activityRatioSlope x) x := by
  have hb : 0 < log (1+x) := log_pos (by linarith)
  have hd : 1+x ≠ 0 := by positivity
  have hl : HasDerivAt (fun x : ℝ => log (1+x)) (1/(1+x)) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hd using 1 <;> simp
  change HasDerivAt (fun z : ℝ => z/log (1+z)) _ x
  apply ((hasDerivAt_id x).div hl hb.ne').congr_deriv
  dsimp [activityRatioSlope]
  (try simp only [id_eq, Pi.pow_apply]) <;> ring

theorem hasDerivAt_activityRatioSlope {x : ℝ} (hx : 0 < x) :
    HasDerivAt activityRatioSlope
      ((2*x-(x+2)*log (1+x))/((1+x)^2*(log (1+x))^3)) x := by
  have hb : 0 < log (1+x) := log_pos (by linarith)
  have hd : 1+x ≠ 0 := by positivity
  have hi := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hl : HasDerivAt (fun x : ℝ => log (1+x)) (1/(1+x)) x := by
    convert hi.log hd using 1 <;> simp
  have hq := (hasDerivAt_id x).div hi hd
  change HasDerivAt (fun z : ℝ => (log (1+z)-z/(1+z))/(log (1+z))^2) _ x
  apply ((hl.sub hq).div (hl.pow 2) (pow_ne_zero 2 hb.ne')).congr_deriv
  (try dsimp) <;> (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply]) <;> field_simp [hd, hb.ne'] <;> ring

theorem activityRatioSlope_antitone : AntitoneOn activityRatioSlope (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (f' := fun x => (2*x-(x+2)*log (1+x))/((1+x)^2*(log (1+x))^3))
  · intro x hx
    exact (hasDerivAt_activityRatioSlope hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_activityRatioSlope (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 < x := interior_subset hx
    have hb : 0 < log (1+x) := log_pos (by linarith)
    have hl := (log_star hx0.le).1
    have hnum : 2*x-(x+2)*log (1+x) ≤ 0 := by
      have hc := (div_le_iff₀ (show 0 < 2+x by linarith)).mp hl
      nlinarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)

theorem activityRatio_concave : ConcaveOn ℝ (Ioi 0) activityRatio := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_activityRatio hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_activityRatio (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(hasDerivAt_activityRatio (interior_subset hx)).deriv,
      (hasDerivAt_activityRatio (interior_subset hy)).deriv]
    exact activityRatioSlope_antitone (interior_subset hx) (interior_subset hy) hxy

theorem activityRatio_tangent_one {x : ℝ} (hx : 0 < x) :
    activityRatio x ≤ activityRatio 1+activityRatioSlope 1*(x-1) := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hh := activityRatio_concave.le_slope_of_hasDerivAt hx (by norm_num) hlt
      (hasDerivAt_activityRatio (by norm_num : (0 : ℝ) < 1))
    have hc : activityRatioSlope 1*(1-x) ≤ activityRatio 1-activityRatio x := by
      apply (le_div_iff₀ (by linarith : 0 < 1-x)).mp
      simpa only [slope_def_field] using hh
    nlinarith
  · subst x
    simp
  · have hh := activityRatio_concave.slope_le_of_hasDerivAt (by norm_num) hx hgt
      (hasDerivAt_activityRatio (by norm_num : (0 : ℝ) < 1))
    have hc : activityRatio x-activityRatio 1 ≤ activityRatioSlope 1*(x-1) := by
      apply (div_le_iff₀ (by linarith : 0 < x-1)).mp
      simpa only [slope_def_field] using hh
    linarith

theorem log_two_tangent_coefficients :
    1/(2*(log 2)^2) ≤ (25/24 : ℝ) ∧
      (log 2-1/2)/(log 2)^2 ≤ (81/200 : ℝ) := by
  have hl := log_two_brackets.1
  have hu := log_two_brackets.2
  have hb : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hsq : (693/1000 : ℝ)^2 ≤ (log 2)^2 := by nlinarith
  constructor
  · apply (div_le_iff₀ (by positivity)).2
    nlinarith
  · apply (div_le_iff₀ (by positivity)).2
    nlinarith

theorem activityRatio_le_printed_line {lam : ℝ} (hlam : 0 < lam) :
    lam/log (1+lam) ≤ 25/24+(81/200)*lam := by
  have ht := activityRatio_tangent_one hlam
  have hb : log (2 : ℝ) ≠ 0 := ne_of_gt (log_pos (by norm_num))
  have hid : activityRatio 1+activityRatioSlope 1*(lam-1) =
      1/(2*(log 2)^2)+((log 2-1/2)/(log 2)^2)*lam := by
    norm_num [activityRatio, activityRatioSlope]
    field_simp [hb] <;> ring
  rw [hid] at ht
  have hcoeff := log_two_tangent_coefficients
  have hs := mul_le_mul_of_nonneg_right hcoeff.2 hlam.le
  exact ht.trans (add_le_add hcoeff.1 hs)

/-- These two outputs use only the actual printed finite cap comparisons. -/
theorem rate_bounds_of_printed_endpoints {D lam u : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hlu : lam ≤ u)
    (hK : (25/24+(81/200)*u)/(5*D/12) < 10/3)
    (huK : u+(25/24+(81/200)*u)/(5*D/12) < 14/3) :
    lam/gamma D lam < 10/3 ∧ lam*(1+1/gamma D lam) < 14/3 := by
  have hg : 0 < 5*D/12 := by positivity
  have hb : 0 < logActivity lam := logActivity_pos hlam
  have ht := activityRatio_le_printed_line hlam
  have h1 : lam/gamma D lam ≤ (25/24+(81/200)*lam)/(5*D/12) := by
    have hdiv := div_le_div_of_nonneg_right ht hg.le
    convert hdiv using 1 <;> dsimp [gamma, logActivity] <;>
      field_simp [hD.ne', show log (1+lam) ≠ 0 from hb.ne'] <;> ring
  have h2 : (25/24+(81/200)*lam)/(5*D/12) ≤
      (25/24+(81/200)*u)/(5*D/12) := by
    exact div_le_div_of_nonneg_right (by linarith) hg.le
  have hlK := h1.trans h2
  constructor
  · exact hlK.trans_lt hK
  · have hid : lam*(1+1/gamma D lam)=lam+lam/gamma D lam := by ring
    rw [hid]
    exact (add_le_add hlu hlK).trans_lt huK

end Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.hasDerivAt_activityRatio
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.hasDerivAt_activityRatio
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.hasDerivAt_activityRatioSlope
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.hasDerivAt_activityRatioSlope
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.activityRatioSlope_antitone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.activityRatioSlope_antitone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.activityRatio_concave
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.activityRatio_concave
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.activityRatio_tangent_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.activityRatio_tangent_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.log_two_tangent_coefficients
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.log_two_tangent_coefficients
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.activityRatio_le_printed_line
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.activityRatio_le_printed_line
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.rate_bounds_of_printed_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.rate_bounds_of_printed_endpoints
