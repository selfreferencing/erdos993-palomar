module

public import Erdos993Lean.Analytic.V213.FreeCountACH0
public import Erdos993Lean.Analytic.V213.FreeCountACParentFunctions

/-! Actual AC (28) activity curvature, with fixed D and parent y. The scalar
argument is z=lambda*exp (-y). It proves the printed -15/32 uniformly, rather
than assuming a curvature premise under a paper-lemma name. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set Filter
open scoped Topology

noncomputable def KActivityModel (D s lam : ℝ) : ℝ :=
  1/(D*(1+s*lam)) + (5/12:ℝ)*logActivity lam*activityH0 (s*lam)
noncomputable def KActivitySlope (D s lam : ℝ) : ℝ :=
  -s/(D*(1+s*lam)^2) + (5/12:ℝ)*
    (activityH0 (s*lam)/(1+lam)+logActivity lam*s*activityH0Slope (s*lam))
noncomputable def KActivityCurvature (D s lam : ℝ) : ℝ :=
  2*s^2/(D*(1+s*lam)^3) + (5/12:ℝ)*
    (-activityH0 (s*lam)/(1+lam)^2+
      2*s*activityH0Slope (s*lam)/(1+lam)+
      logActivity lam*s^2*activityH0Curvature (s*lam))

theorem K_eq_activityModel {D lam : ℝ} (hD : 0<D) (hlam : 0<lam) (y : ℝ) :
    K D lam y = KActivityModel D (exp (-y)) lam := by
  have hs := Real.exp_pos (-y)
  have hz : 0<lam*exp (-y) := mul_pos hlam hs
  have hz1 : 1+lam*exp (-y) ≠ 0 := ne_of_gt (by linarith)
  have hf : log (1+lam*exp (-y)) ≠ 0 :=
    (Real.log_pos (by linarith : 1<1+lam*exp (-y))).ne'
  rw [K, h_normalized hlam]
  unfold KActivityModel activityH0 gamma B message logMass Reserve.msg Reserve.lmass
  simp only [mul_comm (exp (-y)) lam]
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', hlam.ne', hs.ne', hz1, hf] <;> ring

theorem KActivityModel_hasDerivAt {D s lam : ℝ}
    (hD : 0<D) (hs : 0<s) (hlam : 0<lam) :
    HasDerivAt (KActivityModel D s) (KActivitySlope D s lam) lam := by
  have hz : 0<s*lam := mul_pos hs hlam
  have hd : D*(1+s*lam) ≠ 0 := ne_of_gt (by positivity)
  have hh := (activityH0_hasDerivAt hz).comp lam ((hasDerivAt_id lam).const_mul s)
  change HasDerivAt
    (fun a => 1/(D*(1+s*a))+(5/12:ℝ)*logActivity a*activityH0 (s*a)) _ lam
  apply (((hasDerivAt_const lam (1:ℝ)).div
    ((((hasDerivAt_id lam).const_mul s).const_add 1).const_mul D) hd).add
    (((logActivity_hasDerivAt hlam).const_mul (5/12:ℝ)).mul hh)).congr_deriv
  unfold KActivitySlope
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', ne_of_gt (show 0<1+s*lam by positivity),
    ne_of_gt (show 0<1+lam by linarith)] <;> ring

theorem KActivitySlope_hasDerivAt {D s lam : ℝ}
    (hD : 0<D) (hs : 0<s) (hlam : 0<lam) :
    HasDerivAt (KActivitySlope D s) (KActivityCurvature D s lam) lam := by
  have hz : 0<s*lam := mul_pos hs hlam
  have hd : D*(1+s*lam)^2 ≠ 0 := ne_of_gt (by positivity)
  have hl : 1+lam ≠ 0 := ne_of_gt (by linarith)
  have hh := (activityH0_hasDerivAt hz).comp lam ((hasDerivAt_id lam).const_mul s)
  have hh' := (activityH0Slope_hasDerivAt hz).comp lam ((hasDerivAt_id lam).const_mul s)
  unfold KActivitySlope
  apply (((hasDerivAt_const lam (-s)).div
    (((((hasDerivAt_id lam).const_mul s).const_add 1).pow 2).const_mul D) hd).add
    (((hh.div ((hasDerivAt_id lam).const_add 1) hl).add
      (((logActivity_hasDerivAt hlam).mul_const s).mul hh')).const_mul (5/12:ℝ))).congr_deriv
  unfold KActivityCurvature
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', hl, ne_of_gt (show 0<1+s*lam by positivity)] <;> ring

/-- HasDerivAt for the actual printed K, not merely its auxiliary model. -/
theorem K_hasDerivAt_activity {D lam : ℝ} (hD : 0<D) (hlam : 0<lam) (y : ℝ) :
    HasDerivAt (fun a => K D a y) (KActivitySlope D (exp (-y)) lam) lam := by
  apply (KActivityModel_hasDerivAt hD (Real.exp_pos (-y)) hlam).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hlam] with a ha
  exact K_eq_activityModel hD ha y

theorem KActivityCurvature_lower {D s lam : ℝ} (hD : 0<D)
    (hs : 0<s) (hs1 : s≤1) (hlam : 0<lam) :
    -5/(6*(1+lam)^2) ≤ KActivityCurvature D s lam := by
  have hz : 0<s*lam := mul_pos hs hlam
  have h1 : 0<1+lam := by linarith
  have hz1 : 0<1+s*lam := by positivity
  have hh := activityH0_le_one hz
  have hfirst : -1/(1+lam)^2 ≤ -activityH0 (s*lam)/(1+lam)^2 :=
    div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hratio : s/(1+s*lam) ≤ 1/(1+lam) := by
    apply (div_le_div_iff₀ hz1 h1).2
    nlinarith
  have hsl := activityH0Slope_lower hz
  have hmul := mul_le_mul_of_nonneg_left hsl
    (show 0≤2*s/(1+lam) by positivity)
  have hmid : -1/(1+lam)^2 ≤ 2*s*activityH0Slope (s*lam)/(1+lam) := by
    have hc := div_le_div_of_nonneg_right hratio h1.le
    have hi : (2*s/(1+lam))*(-1/(2*(1+s*lam))) =
        -(s/(1+s*lam)/(1+lam)) := by
      field_simp [h1.ne', hz1.ne'] <;> ring
    rw [hi] at hmul
    have hi2 : (1/(1+lam))/(1+lam) = 1/(1+lam)^2 := by
      field_simp [h1.ne'] <;> ring
    rw [hi2] at hc
    have hi3 : (2*s/(1+lam))*activityH0Slope (s*lam) =
        2*s*activityH0Slope (s*lam)/(1+lam) := by ring
    rw [hi3] at hmul
    simpa only [neg_div] using (neg_le_neg hc).trans hmul
  have hlast : 0≤logActivity lam*s^2*activityH0Curvature (s*lam) :=
    mul_nonneg (mul_nonneg (logActivity_pos hlam).le (sq_nonneg _))
      (activityH0Curvature_nonneg hz)
  have hconv : 0≤2*s^2/(D*(1+s*lam)^3) := by positivity
  unfold KActivityCurvature
  have hi : -5/(6*(1+lam)^2) = (5/12:ℝ)*(-1/(1+lam)^2-1/(1+lam)^2) := by
    field_simp [h1.ne'] <;> ring
  rw [hi]
  ring_nf at hfirst hmid hlast hconv ⊢
  linarith only [hfirst, hmid, hlast, hconv]

/-- The precise closed lower-activity endpoint used by every printed A cell. -/
theorem KActivityCurvature_lower_fifteen_thirtytwo {D lam y : ℝ}
    (hD : 0<D) (hlam : (1/3:ℝ)≤lam) (hy : 0≤y) :
    -(15/32:ℝ) ≤ KActivityCurvature D (exp (-y)) lam := by
  have hl : 0<lam := by linarith
  have hs1 : exp (-y)≤1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hy)
  have hh := KActivityCurvature_lower hD (Real.exp_pos (-y)) hs1 hl
  have hden : 0<(1+lam)^2 := sq_pos_of_pos (by linarith)
  have hb : -(15/32:ℝ)≤ -5/(6*(1+lam)^2) := by
    apply (le_div_iff₀ (by positivity : 0<6*(1+lam)^2)).2
    nlinarith [sq_nonneg (lam-1/3)]
  exact hb.trans hh

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.K_eq_activityModel
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.K_eq_activityModel
#check Erdos993Lean.Analytic.V213.FreeCountVariance.KActivityModel_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.KActivityModel_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.KActivitySlope_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.KActivitySlope_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.K_hasDerivAt_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.K_hasDerivAt_activity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.KActivityCurvature_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.KActivityCurvature_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.KActivityCurvature_lower_fifteen_thirtytwo
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.KActivityCurvature_lower_fifteen_thirtytwo
