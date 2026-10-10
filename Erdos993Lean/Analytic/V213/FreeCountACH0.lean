module

public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds
public import Erdos993Lean.Analytic.V213.FreeCountRealExpEnvelopes

/-! AC (28) scalar kernel. All claims have z>0. No value of the
raw quotient at z=0 is identified with its continuous extension. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real

noncomputable def activityH0 (z : ℝ) : ℝ := z / ((1+z)*log (1+z))
noncomputable def activityH0Slope (z : ℝ) : ℝ :=
  (log (1+z)-z)/((1+z)^2*log (1+z)^2)
noncomputable def activityH0Curvature (z : ℝ) : ℝ :=
  (z*(log (1+z)+2)-2*log (1+z)*(log (1+z)+1)) /
    ((1+z)^3*log (1+z)^3)

theorem activityH0_pos {z : ℝ} (hz : 0<z) : 0<activityH0 z := by
  have hf : 0<log (1+z) := Real.log_pos (by linarith)
  unfold activityH0
  positivity

theorem activityH0_le_one {z : ℝ} (hz : 0<z) : activityH0 z ≤ 1 := by
  have h1 : 0<1+z := by linarith
  have h2 : 0<2+z := by linarith
  have hf : 0<log (1+z) := Real.log_pos (by linarith)
  have hl := (Envelopes.log_star hz.le).1
  have hl' := (div_le_iff₀ h2).mp hl
  have hnon := mul_nonneg hz.le hf.le
  unfold activityH0
  apply (div_le_one (mul_pos h1 hf)).2
  nlinarith

theorem activityH0_hasDerivAt {z : ℝ} (hz : 0<z) :
    HasDerivAt activityH0 (activityH0Slope z) z := by
  have h1 : 1+z ≠ 0 := ne_of_gt (by linarith)
  have hf : log (1+z) ≠ 0 := (Real.log_pos (by linarith : 1<1+z)).ne'
  change HasDerivAt (fun x : ℝ => x/((1+x)*log (1+x))) _ z
  apply ((hasDerivAt_id z).div
    (((hasDerivAt_id z).const_add 1).mul
      (((hasDerivAt_id z).const_add 1).log h1)) (mul_ne_zero h1 hf)).congr_deriv
  unfold activityH0Slope
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [h1, hf] <;> ring

theorem activityH0Slope_hasDerivAt {z : ℝ} (hz : 0<z) :
    HasDerivAt activityH0Slope (activityH0Curvature z) z := by
  have h1 : 1+z ≠ 0 := ne_of_gt (by linarith)
  have hf : log (1+z) ≠ 0 := (Real.log_pos (by linarith : 1<1+z)).ne'
  have hd := ((hasDerivAt_id z).const_add 1).log h1
  change HasDerivAt
    (fun x : ℝ => (log (1+x)-x)/((1+x)^2*log (1+x)^2)) _ z
  apply ((hd.sub (hasDerivAt_id z)).div
    ((((hasDerivAt_id z).const_add 1).pow 2).mul (hd.pow 2))
      (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ hf))).congr_deriv
  unfold activityH0Curvature
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [h1, hf] <;> ring

theorem activityH0Slope_nonpos {z : ℝ} (hz : 0<z) : activityH0Slope z ≤ 0 := by
  have hl := Real.log_le_sub_one_of_pos (show 0<1+z by linarith)
  unfold activityH0Slope
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- A rational consequence of the lower log-star bound; no numerical premise. -/
theorem activityH0Slope_lower {z : ℝ} (hz : 0<z) :
    -1/(2*(1+z)) ≤ activityH0Slope z := by
  have h1 : 0<1+z := by linarith
  have h2 : 0<2+z := by linarith
  have hf : 0<log (1+z) := Real.log_pos (by linarith)
  let b := 2*z/(2+z)
  have hb : 0≤b := by dsimp [b]; positivity
  have hbf : b≤log (1+z) := (Envelopes.log_star hz.le).1
  have hsq := pow_le_pow_left₀ hb hbf 2
  have hsq' := mul_le_mul_of_nonneg_left hsq h1.le
  have hi : (1+z)*b^2+2*b-2*z = 2*z^3/(2+z)^2 := by
    dsimp [b]
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [h2.ne'] <;> ring
  have hb0 : 0≤(1+z)*b^2+2*b-2*z := by rw [hi]; positivity
  have hn : 0≤(1+z)*log (1+z)^2+2*log (1+z)-2*z := by linarith
  unfold activityH0Slope
  apply (div_le_div_iff₀ (by positivity : 0<2*(1+z))
    (by positivity : 0<(1+z)^2*log (1+z)^2)).2
  nlinarith [mul_nonneg h1.le hn]

theorem activityH0Curvature_nonneg {z : ℝ} (hz : 0<z) :
    0≤activityH0Curvature z := by
  have hf : 0<log (1+z) := Real.log_pos (by linarith)
  have he := Envelopes.expPartial_le_exp 2 hf.le
  rw [Real.exp_log (show 0<1+z by linarith)] at he
  norm_num [Envelopes.expPartial, Finset.sum_range_succ, Nat.factorial] at he
  have hm := mul_nonneg
    (show 0≤z-log (1+z)-log (1+z)^2/2 by linarith)
    (show 0≤log (1+z)+2 by linarith)
  have hn : 0≤z*(log (1+z)+2)-2*log (1+z)*(log (1+z)+1) := by
    nlinarith [pow_nonneg hf.le 3]
  unfold activityH0Curvature
  exact div_nonneg hn (by positivity)

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0_le_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0_le_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0Slope_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0Slope_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0Slope_nonpos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0Slope_nonpos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0Slope_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0Slope_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0Curvature_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.activityH0Curvature_nonneg
