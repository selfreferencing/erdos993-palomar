module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceDerivatives
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds
public import Erdos993Lean.Analytic.V213.FreeCountRealExpEnvelopes

/-!
The current Section 3 childless-child face.
The derivative is the paper's actual derivative. A global square bound
replaces its two-piece K (y) estimate; the resulting lower bound is affine
in activity and its two endpoints have elementary square proofs.
The printed scalar premise lambda/gamma <= 10/3 is explicit; it is supplied by the
current-cap scalar layer. No finite endpoint value or global CA claim is
assumed. No differentiation across a cap seam is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set

noncomputable def childlessC0 (D lam y : ℝ) : ℝ := bp lam y + (5/7)*ell D lam y

/-- A single global substitute for the printed piecewise K (y). -/
theorem childless_parent_product_bound {p y : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p)*(1+y*p) ≤ 1+y^2/10 := by
  have hk : 0 ≤ 1-p := by linarith
  have hpk : p*(1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p-1/2)]
  have hpk0 : 0 ≤ p*(1-p) := mul_nonneg hp hk
  have hpk2 : p*(1-p)^2 ≤ 1/4 := by
    have hh := mul_le_mul_of_nonneg_left (show 1-p ≤ 1 by linarith) hpk0
    nlinarith
  have hrem : 0 ≤ p*(1-(5/2)*p*(1-p)^2) := by
    apply mul_nonneg hp
    nlinarith
  have hid : 1+y^2/10-(1-p)*(1+y*p) =
      (y-5*p*(1-p))^2/10 + p*(1-(5/2)*p*(1-p)^2) := by ring
  rw [← sub_nonneg]
  rw [hid]
  positivity

theorem childless_inverse_B_bounds {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    1-message lam y ≤ 1/B lam y ∧ 1/B lam y ≤ 1-message lam y/2 := by
  have hh := Envelopes.message_scalarH_bounds hlam y
  simpa only [B, one_div_div] using hh

theorem childless_varpi_bound {lam y : ℝ} (hlam : 0 < lam)
    (hlam7 : lam ≤ 7/3) (hy : 0 ≤ y) :
    varpi lam y / B lam y^2 ≤ (91/400 : ℝ) := by
  let p := message lam y
  let u := 1/B lam y
  have hp : 0 < p := message_pos hlam y
  have hp1 : p < 1 := message_lt_one hlam y
  have hB := B_pos hlam y
  have hu : 0 < u := one_div_pos.mpr hB
  have hh := childless_inverse_B_bounds hlam y
  have huk : 0 ≤ u-(1-p) := by dsimp [u,p]; linarith [hh.1]
  have hup : u-(1-p) ≤ p/2 := by dsimp [u,p]; linarith [hh.2]
  have huupper : u ≤ 1-p/2 := hh.2
  have hpq := Envelopes.message_le_q hlam hy
  have hq7 : q lam ≤ 7/10 := by
    unfold q
    apply (div_le_iff₀ (by linarith : 0 < 1+lam)).2
    linarith
  have hp7 : p ≤ 7/10 := hpq.trans hq7
  have hid : varpi lam y/B lam y^2 = u*(u-(1-p)) := by
    dsimp [u,p]
    unfold varpi
    field_simp [hB.ne'] <;> ring
  have hfirst := mul_le_mul_of_nonneg_left hup hu.le
  have hsecond := mul_le_mul_of_nonneg_right huupper (by positivity : 0 ≤ p/2)
  have hlast : (1-p/2)*(p/2) ≤ 91/400 := by
    have hprod := mul_nonneg (show 0 ≤ 7/10-p by linarith)
      (show 0 ≤ 13/10-p by linarith)
    nlinarith
  rw [hid]
  exact hfirst.trans (hsecond.trans hlast)

theorem childlessC0_hasDerivAt {D lam y : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (hy : y ≠ 0) :
    HasDerivAt (childlessC0 D lam)
      ((12/7)*ap lam y + varpi lam y/y + B lam y/y^2 -
        (5/(7*gamma D lam))*(1-message lam y)*(1+y*message lam y) -
        5/(7*B lam y) - 5*y*varpi lam y/(7*B lam y^2)) y := by
  have hd := childless_expression_hasDerivAt hD hlam hy
  change HasDerivAt (childlessC0 D lam) _ y at hd
  apply hd.congr_deriv
  rw [h_normalized hlam y]
  have hg := (gamma_pos hD hlam).ne'
  have hB := (B_pos hlam y).ne'
  (try simp only [id_eq, Pi.pow_apply]) <;> field_simp [hg,hB] <;> ring

noncomputable def childlessSlopeLower (lam y : ℝ) : ℝ :=
  -2/3-5*lam/7+(12/7-91*lam/560)*y+13*y^2/21+lam/y^2

theorem childlessSlopeLower_left {y : ℝ} (hy : 0 < y) :
    0 < childlessSlopeLower (1/3) y := by
  have hsq := mul_nonneg (sq_nonneg (y-1)) (by positivity : 0 ≤ 2*y+1)
  have ham : 3 ≤ 2*y+1/y^2 := by
    have hid : 2*y+1/y^2 = (2*y^3+1)/y^2 := by
      field_simp [hy.ne'] <;> ring
    rw [hid]
    apply (le_div_iff₀ (sq_pos_of_pos hy)).2
    nlinarith
  have hid : childlessSlopeLower (1/3) y =
      (2*y+1/y^2)/3-19/21+(1669/1680)*y+13*y^2/21 := by
    unfold childlessSlopeLower
    ring
  rw [hid]
  nlinarith [sq_nonneg y]

theorem childlessSlopeLower_right {y : ℝ} (hy : 0 < y) :
    0 < childlessSlopeLower (7/3) y := by
  have hid : childlessSlopeLower (7/3) y =
      (7/12)*(y-2/y)^2+y^2/28+(2243/1680)*y := by
    unfold childlessSlopeLower
    field_simp [hy.ne'] <;> ring
  rw [hid]
  positivity

theorem childlessSlopeLower_pos {lam y : ℝ} (hl : 1/3 ≤ lam)
    (hu : lam ≤ 7/3) (hy : 0 < y) : 0 < childlessSlopeLower lam y := by
  have ha := childlessSlopeLower_left hy
  have hb := childlessSlopeLower_right hy
  have hid : childlessSlopeLower lam y =
      ((7/3-lam)*childlessSlopeLower (1/3) y +
        (lam-1/3)*childlessSlopeLower (7/3) y)/2 := by
    unfold childlessSlopeLower
    ring
  rw [hid]
  have hla : 0 ≤ 7/3-lam := by linarith
  have hlb : 0 ≤ lam-1/3 := by linarith
  have hh : 0 < (7/3-lam)*childlessSlopeLower (1/3) y +
      (lam-1/3)*childlessSlopeLower (7/3) y := by
    by_cases hla0 : 7/3-lam = 0
    · have hlb0 : 0 < lam-1/3 := by linarith
      rw [hla0,zero_mul,zero_add]
      exact mul_pos hlb0 hb
    · have hla' : 0 < 7/3-lam := by rcases eq_or_lt_of_le hla with h | h; exact False.elim (hla0 h.symm); exact h
      exact add_pos_of_pos_of_nonneg (mul_pos hla' ha)
        (mul_nonneg hlb hb.le)
  positivity

/-- The only cap-specific premise here is the printed lambda/gamma budget. -/
theorem childlessC0_deriv_lower {D lam y : ℝ} (hD : 0 < D)
    (hl : 1/3 ≤ lam) (hu : lam ≤ 7/3) (hy : 0 < y)
    (hbudget : lam/gamma D lam ≤ 10/3) :
    childlessSlopeLower lam y ≤ lam*deriv (childlessC0 D lam) y := by
  have hlam : 0 < lam := by linarith
  have hg := gamma_pos hD hlam
  have hp := message_pos hlam y
  have hp1 := message_lt_one hlam y
  have hB := B_pos hlam y
  have hv := varpi_nonneg hlam y
  have hh := childless_inverse_B_bounds hlam y
  have hi : 1/B lam y ≤ 1 := by linarith [hh.2]
  have hB1 : 1 ≤ B lam y := by
    have hh' := (div_le_iff₀ hB).1 hi
    simpa only [one_mul] using hh'
  have hbterm : lam/y^2 ≤ lam*B lam y/y^2 := by
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg y)
  have hvterm : 0 ≤ lam*varpi lam y/y := by positivity
  have hiv : lam*(1/B lam y) ≤ lam := by nlinarith
  have hvB := childless_varpi_bound hlam hu hy.le
  have hvlast : lam*y*(varpi lam y/B lam y^2) ≤ lam*y*(91/400) :=
    mul_le_mul_of_nonneg_left hvB (by positivity)
  have hk := childless_parent_product_bound (y := y) hp.le hp1.le
  have hprod : (lam/gamma D lam)*((1-message lam y)*(1+y*message lam y)) ≤
      (10/3)*(1+y^2/10) := by
    exact mul_le_mul hbudget hk
      (mul_nonneg (by linarith) (by positivity)) (by norm_num)
  have he := Envelopes.expPartial_le_exp 2 hy.le
  norm_num [Envelopes.expPartial,Finset.sum_range_succ,Nat.factorial] at he
  have hid : lam*deriv (childlessC0 D lam) y =
      (12/7)*exp y + lam*varpi lam y/y + lam*B lam y/y^2 -
      (5/7)*((lam/gamma D lam)*((1-message lam y)*(1+y*message lam y))) -
      (5/7)*(lam*(1/B lam y)) -
      (5/7)*(lam*y*(varpi lam y/B lam y^2)) := by
    rw [(childlessC0_hasDerivAt hD hlam hy.ne').deriv]
    unfold ap
    field_simp [hlam.ne',hg.ne',hB.ne',hy.ne'] <;> ring
  rw [hid]
  unfold childlessSlopeLower
  nlinarith only [hbterm,hvterm,hiv,hvlast,hprod,he]

theorem childlessC0_deriv_pos {D lam y : ℝ} (hD : 0 < D)
    (hl : 1/3 ≤ lam) (hu : lam ≤ 7/3) (hy : 0 < y)
    (hbudget : lam/gamma D lam ≤ 10/3) :
    0 < deriv (childlessC0 D lam) y := by
  have hlo := childlessSlopeLower_pos hl hu hy
  have hbound := childlessC0_deriv_lower hD hl hu hy hbudget
  have hlam : 0 < lam := by linarith
  exact (mul_pos_iff_of_pos_left hlam).1 (hlo.trans_le hbound)

theorem childlessC0_strictMono {D lam : ℝ} (hD : 0 < D)
    (hl : 1/3 ≤ lam) (hu : lam ≤ 7/3)
    (hbudget : lam/gamma D lam ≤ 10/3) :
    StrictMonoOn (childlessC0 D lam) (Ioi 0) := by
  have hlam : 0 < lam := by linarith
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi 0)
    (f' := fun y => deriv (childlessC0 D lam) y)
  · intro y hy
    exact (childlessC0_hasDerivAt hD hlam hy.ne').continuousAt.continuousWithinAt
  · intro y hy
    have hh : 0 < y := interior_subset hy
    have hd := childlessC0_hasDerivAt hD hlam hh.ne'
    rw [hd.deriv]
    exact hd.hasDerivWithinAt
  · intro y hy
    exact childlessC0_deriv_pos hD hl hu (interior_subset hy) hbudget

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.childless_parent_product_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childless_parent_product_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childless_inverse_B_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childless_inverse_B_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childless_varpi_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childless_varpi_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessSlopeLower_left
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessSlopeLower_left
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessSlopeLower_right
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessSlopeLower_right
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessSlopeLower_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessSlopeLower_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_deriv_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_deriv_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_deriv_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_deriv_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_strictMono
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_strictMono
