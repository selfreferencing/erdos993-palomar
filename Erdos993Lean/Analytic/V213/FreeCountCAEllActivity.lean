module

public import Erdos993Lean.Analytic.V213.FreeCountCAChildlessSlope
public import Erdos993Lean.Analytic.V213.FreeCountActivityTangent
public import Erdos993Lean.Analytic.V213.FreeCountACParentFunctions
public import Erdos993Lean.Analytic.V213.FreeCountVarianceCaps

/-! Actual activity reduction preceding (22). Only the printed quadratic
vertex comparison is a finite premise. The differentiated function is the
actual ell at fixed D,y; no cap selection is differentiated at a seam.
Closed activity intervals and y=0 are included in the analytic helper.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set Filter
open scoped Topology

noncomputable def ellActivitySlope (D lam y : ℝ) : ℝ :=
  (-exp y+y*((lam/gamma D lam)*(1-message lam y)*
    (message lam y+q lam/logActivity lam)+lam*varpi lam y/B lam y^2))/lam^2

theorem ell_hasDerivAt_activity {D lam : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (fun a => ell D a y) (ellActivitySlope D lam y) lam := by
  let f := fun a : ℝ => exp y/a-y*((1-message a y)/gamma D a+message a y/logMass a y)
  have hf : (fun a => ell D a y) =ᶠ[𝓝 lam] f := by
    filter_upwards [isOpen_Ioi.mem_nhds hlam] with a ha
    rw [ell_normalized hD ha,h_normalized ha]
    unfold f ap B
    field_simp [(gamma_pos hD ha).ne', (message_pos ha y).ne', (logMass_pos ha y).ne'] <;> ring
  have hg := (gamma_pos hD hlam).ne'
  have hm := (logMass_pos hlam y).ne'
  have hb := (logActivity_pos hlam).ne'
  have hp := (message_pos hlam y).ne'
  have hgamma : HasDerivAt (gamma D) (5*D/(12*(1+lam))) lam := by
    convert ((logActivity_hasDerivAt hlam).const_mul (5*D)).div_const 12 using 1 <;>
      (try unfold gamma) <;> (try simp only [id_eq, Pi.pow_apply]) <;>
      field_simp [show 1+lam ≠ 0 by positivity] <;> ring
  have hd := ((hasDerivAt_const lam (exp y)).div (hasDerivAt_id lam) hlam.ne').sub
    (((((message_hasDerivAt_activity hlam y).const_sub 1).div hgamma hg).add
      ((message_hasDerivAt_activity hlam y).div (logMass_hasDerivAt_activity hlam y) hm)).const_mul y)
  have hd' : HasDerivAt f (ellActivitySlope D lam y) lam := by
    apply hd.congr_deriv
    unfold ellActivitySlope varpi B q gamma
    (try simp only [id_eq, Pi.pow_apply]) <;>
      field_simp [hlam.ne',hg,hm,hb,hp,show 1+lam ≠ 0 by positivity] <;> ring
  exact hd'.congr_of_eventuallyEq hf

/-- Unrounded version of the paper's varpi/B^2 bound. -/
theorem varpi_over_B_sq_le_parent {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    varpi lam y/B lam y^2 ≤ message lam y*(1-message lam y/2)/2 := by
  have hp := message_pos hlam y
  have hB := B_pos hlam y
  have hh := childless_inverse_B_bounds hlam y
  have hu : 0 ≤ 1/B lam y := (one_div_pos.mpr hB).le
  have h1 := mul_le_mul_of_nonneg_left
    (show 1/B lam y-(1-message lam y) ≤ message lam y/2 by linarith) hu
  have h2 := mul_le_mul_of_nonneg_right hh.2 (by positivity : 0 ≤ message lam y/2)
  have hid : varpi lam y/B lam y^2 =
      (1/B lam y)*(1/B lam y-(1-message lam y)) := by
    unfold varpi
    field_simp [hB.ne'] <;> ring
  rw [hid]
  nlinarith only [h1,h2]

theorem ell_activity_brace_bound {D lam y b K H : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hy : 0 ≤ y)
    (hlb : lam ≤ b) (hK : 0 ≤ K)
    (hRate : lam/gamma D lam ≤ K) (hH : q lam/logActivity lam ≤ H) :
    lam^2*deriv (fun a => ell D a y) lam ≤
      -exp y+y*(K*(1-message lam y)*(message lam y+H)+
        (b/2)*message lam y*(1-message lam y/2)) := by
  have hp := message_pos hlam y
  have hp1 := message_lt_one hlam y
  have hq := q_pos hlam
  have hb := logActivity_pos hlam
  have hg := gamma_pos hD hlam
  have hB := B_pos hlam y
  have hv := varpi_nonneg hlam y
  have hfirst := mul_le_mul hRate
    (mul_le_mul_of_nonneg_left
      (add_le_add (le_rfl : message lam y ≤ message lam y) hH)
      (show 0 ≤ 1-message lam y by linarith))
    (mul_nonneg (show 0 ≤ 1-message lam y by linarith)
      (add_nonneg hp.le (div_nonneg hq.le hb.le))) hK
  have hlast := mul_le_mul hlb (varpi_over_B_sq_le_parent hlam y)
    (by positivity : 0 ≤ varpi lam y/B lam y^2) (by linarith : 0 ≤ b)
  have hsum : (lam/gamma D lam)*(1-message lam y)*
      (message lam y+q lam/logActivity lam)+lam*varpi lam y/B lam y^2 ≤
      K*(1-message lam y)*(message lam y+H)+
        (b/2)*message lam y*(1-message lam y/2) := by
    simp only [mul_div_assoc] at hlast ⊢
    nlinarith only [hfirst,hlast]
  have hmul := mul_le_mul_of_nonneg_left hsum hy
  rw [(ell_hasDerivAt_activity hD hlam y).deriv]
  unfold ellActivitySlope
  have hid : lam^2*((-exp y+y*((lam/gamma D lam)*(1-message lam y)*
      (message lam y+q lam/logActivity lam)+lam*varpi lam y/B lam y^2))/lam^2) =
      -exp y+y*((lam/gamma D lam)*(1-message lam y)*
      (message lam y+q lam/logActivity lam)+lam*varpi lam y/B lam y^2) := by
    field_simp [hlam.ne']
  rw [hid]
  linarith

theorem ell_activity_quadratic_bound {K b H p : ℝ} (hK : 0 < K) (hb : 0 ≤ b) :
    K*(1-p)*(p+H)+(b/2)*p*(1-p/2) ≤
      K*H+(K*(1-H)+b/2)^2/(4*(K+b/4)) := by
  have hd : 0 < 4*(K+b/4) := by positivity
  have hid : (K*H+(K*(1-H)+b/2)^2/(4*(K+b/4))-
      (K*(1-p)*(p+H)+(b/2)*p*(1-p/2)))*(4*(K+b/4)) =
      (2*(K+b/4)*p-(K*(1-H)+b/2))^2 := by
    field_simp [hd.ne'] <;> ring
  have hh : 0 ≤ (K*H+(K*(1-H)+b/2)^2/(4*(K+b/4))-
      (K*(1-p)*(p+H)+(b/2)*p*(1-p/2)))*(4*(K+b/4)) := by
    rw [hid]
    exact sq_nonneg _
  have hgap := (mul_nonneg_iff_of_pos_right hd).1 hh
  linarith

theorem eight_thirds_mul_parent_lt_exp {y : ℝ} (hy : 0 ≤ y) :
    (8/3)*y < exp y := by
  by_cases hy0 : y = 0
  · subst y
    norm_num
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have htan := Real.add_one_le_exp (y-1)
  have hm := mul_le_mul_of_nonneg_right htan (exp_pos 1).le
  have he : exp (y-1)*exp 1 = exp y := by rw [← exp_add]; congr 1; ring
  rw [he] at hm
  have hs := mul_lt_mul_of_pos_right Envelopes.exp_one_gt_eight_thirds hyp
  nlinarith

/-- The finite premise is precisely the displayed quadratic-vertex test. -/
theorem ell_activity_deriv_neg_of_vertex {D lam y b K H : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hy : 0 ≤ y)
    (hlb : lam ≤ b) (hK : 0 < K)
    (hRate : lam/gamma D lam ≤ K) (hH : q lam/logActivity lam ≤ H)
    (hvertex : K*H+(K*(1-H)+b/2)^2/(4*(K+b/4)) < 8/3) :
    deriv (fun a => ell D a y) lam < 0 := by
  have hb : 0 ≤ b := by linarith
  have hbrace := ell_activity_quadratic_bound (H := H) (p := message lam y) hK hb
  have hscaled := ell_activity_brace_bound hD hlam hy hlb hK.le hRate hH
  have hm := mul_le_mul_of_nonneg_left (hbrace.trans hvertex.le) hy
  have hexp := eight_thirds_mul_parent_lt_exp hy
  have hneg : lam^2*deriv (fun a => ell D a y) lam < 0 := by nlinarith
  by_contra hn
  have hd0 : 0 ≤ deriv (fun a => ell D a y) lam := le_of_not_gt hn
  have hm0 := mul_nonneg (sq_nonneg lam) hd0
  exact (not_lt_of_ge hm0) hneg

noncomputable def ellIntervalH (a : ℝ) : ℝ := 1-q a/2
noncomputable def ellIntervalK (D b : ℝ) : ℝ := (25/24+(81/200)*b)/(5*D/12)

theorem ell_interval_parameter_bounds {D a b lam : ℝ} (hD : 0 < D)
    (ha : 0 < a) (hal : a ≤ lam) (hlb : lam ≤ b) :
    0 < ellIntervalK D b ∧ lam/gamma D lam ≤ ellIntervalK D b ∧
      q lam/logActivity lam ≤ ellIntervalH a := by
  have hlam : 0 < lam := ha.trans_le hal
  have hb : 0 < b := hlam.trans_le hlb
  have hg : 0 < 5*D/12 := by positivity
  have hbeta := logActivity_pos hlam
  have ht := Uniform.activityRatio_le_printed_line hlam
  have hd := div_le_div_of_nonneg_right ht hg.le
  have hid : (lam/log (1+lam))/(5*D/12) = lam/gamma D lam := by
    unfold gamma logActivity
    field_simp [hD.ne',show log (1+lam) ≠ 0 from hbeta.ne'] <;> ring
  rw [hid] at hd
  have hu : (25/24+(81/200)*lam)/(5*D/12) ≤ ellIntervalK D b := by
    unfold ellIntervalK
    exact div_le_div_of_nonneg_right (by linarith) hg.le
  have hq := q_le_q ha.le hal
  have hh := (Envelopes.message_scalarH_bounds hlam 0).2
  simp only [message_zero,logMass_zero] at hh
  refine ⟨?_,hd.trans hu,?_⟩
  · unfold ellIntervalK
    positivity
  · unfold ellIntervalH
    linarith

theorem ell_antitone_on_activity_interval {D a b y : ℝ}
    (hD : 0 < D) (ha : 0 < a) (hy : 0 ≤ y)
    (hvertex : ellIntervalK D b*ellIntervalH a+
      (ellIntervalK D b*(1-ellIntervalH a)+b/2)^2/(4*(ellIntervalK D b+b/4)) < 8/3) :
    AntitoneOn (fun lam => ell D lam y) (Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (f' := fun lam => deriv (fun z => ell D z y) lam)
  · intro lam hl
    exact (ell_hasDerivAt_activity hD (ha.trans_le hl.1) y).continuousAt.continuousWithinAt
  · intro lam hl
    have hh := interior_subset hl
    have hd := ell_hasDerivAt_activity hD (ha.trans_le hh.1) y
    rw [hd.deriv]
    exact hd.hasDerivWithinAt
  · intro lam hl
    have hh := interior_subset hl
    have hpars := ell_interval_parameter_bounds hD ha hh.1 hh.2
    exact (ell_activity_deriv_neg_of_vertex hD (ha.trans_le hh.1) hy hh.2
      hpars.1 hpars.2.1 hpars.2.2 hvertex).le

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_hasDerivAt_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_hasDerivAt_activity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.varpi_over_B_sq_le_parent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.varpi_over_B_sq_le_parent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_activity_brace_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_activity_brace_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_activity_quadratic_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_activity_quadratic_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.eight_thirds_mul_parent_lt_exp
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.eight_thirds_mul_parent_lt_exp
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_activity_deriv_neg_of_vertex
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_activity_deriv_neg_of_vertex
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_interval_parameter_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_interval_parameter_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_antitone_on_activity_interval
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_antitone_on_activity_interval
