module

public import Erdos993Lean.Analytic.V213.FreeCountACChildEnvelope

/-!+Current (24)--(25), with actual AC and a square-completion minimization.
The working version uses nonnegative square roots a,c directly, because in
the application they are D*m and h and no radicals remain. Positivity of the
actual reserve denominator remains an explicit scalar premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

theorem ratio_child_monotone {x z ellValue : ℝ} (hxz : x ≤ z)
    (hx : 0 < 1 + ellValue * x) (hz : 0 < 1 + ellValue * z) :
    x / (1 + ellValue * x) ≤ z / (1 + ellValue * z) := by
  apply (div_le_div_iff₀ hx hz).2
  nlinarith only [hxz]

theorem AC_div_message {D lam y : ℝ} (hD : 0 < D) (hlam : 0 < lam)
    (hy : 0 < y) (t : ℝ) :
    AC D lam t y / message lam y =
      alpha D lam * (childRatio lam t + bp lam y) + (capA D lam - h D lam y) / y -
        (h D lam y ^ 2 / gamma D lam) * J lam t / (1 + ell D lam y * J lam t) := by
  have hp := (message_pos hlam y).ne'
  have hg := (gamma_pos hD hlam).ne'
  have hH : H D lam y = message lam y * h D lam y := by
    unfold h
    field_simp [hp]
  unfold AC
  rw [E_normalized hlam hy, Z_normalized hD hlam, hH]
  by_cases hz : 1 + ell D lam y * J lam t = 0
  · simp only [hz, mul_zero, div_zero, sub_zero]
    unfold childRatio
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hp, hy.ne'] <;> ring
  · unfold childRatio
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hp, hg, hy.ne', hz] <;> ring

/-- Substitution of the proved rational child envelope, without sampling a
child point. The physical denominator is explicit. -/
theorem AC_rational_child_lower {D lam t y : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hlam7 : lam ≤ 7 / 3)
    (ht : 0 ≤ t) (hy : 0 < y)
    (hell : -(3 / 4 : ℝ) < ell D lam y)
    (hden : 0 < 1 + ell D lam y * J lam t) :
    alpha D lam * bp lam y + (capA D lam - h D lam y) / y +
      alpha D lam * childRatio lam t -
        (h D lam y ^ 2 * q lam ^ 2 / gamma D lam) * childRatio lam t /
          (1 + (cStar lam + ell D lam y * q lam ^ 2) * childRatio lam t) ≤
      AC D lam t y / message lam y := by
  let r := childRatio lam t
  let v := q lam ^ 2 * r / (1 + cStar lam * r)
  have hr : 0 ≤ r := childRatio_nonneg hlam ht
  have hc := cStar_pos hlam
  have hb := child_correction_den_pos hlam hlam7 hell
  have hs : 0 < 1 + cStar lam * r := by positivity
  have hbr : 0 < 1 + (cStar lam + ell D lam y * q lam ^ 2) * r := by positivity
  have hid : 1 + ell D lam y * v =
      (1 + (cStar lam + ell D lam y * q lam ^ 2) * r) / (1 + cStar lam * r) := by
    dsimp [v]
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hs.ne'] <;> ring
  have hvden : 0 < 1 + ell D lam y * v := by rw [hid]; exact div_pos hbr hs
  have hJ : J lam t ≤ v := J_le_rational_child hlam ht
  have hratio := ratio_child_monotone hJ hden hvden
  have hcancel : v / (1 + ell D lam y * v) =
      q lam ^ 2 * r / (1 + (cStar lam + ell D lam y * q lam ^ 2) * r) := by
    rw [hid]
    dsimp [v]
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hs.ne', hbr.ne'] <;> ring
  rw [hcancel] at hratio
  have hm := mul_le_mul_of_nonneg_left hratio
    (div_nonneg (sq_nonneg (h D lam y)) (gamma_pos hD hlam).le)
  rw [AC_div_message hD hlam hy]
  change _ ≤ alpha D lam * (r + bp lam y) + (capA D lam - h D lam y) / y - _
  dsimp only [r] at hm ⊢
  ring_nf at hm ⊢
  linarith only [hm]

/-- The exact square-completion lower rule used in (25). No assumption of an
attained infimum at infinity is made (notably when a=0). -/
theorem square_rational_lower {a c b r : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 < b) (hr : 0 ≤ r) :
    -(max 0 (c - a)) ^ 2 / b ≤ a ^ 2 * r - c ^ 2 * r / (1 + b * r) := by
  have hs : 0 < 1 + b * r := by positivity
  by_cases hca : c ≤ a
  · rw [max_eq_left (by linarith : c - a ≤ 0)]
    norm_num only [zero_pow, neg_zero, zero_div]
    have hsq : c ^ 2 ≤ a ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsq hr
    have hnonneg : 0 ≤ a ^ 2 * b * r ^ 2 := by positivity
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hs).2
    nlinarith only [hmul, hnonneg]
  · have hac : 0 ≤ c - a := by linarith
    rw [max_eq_right hac]
    have hid : a ^ 2 * r - c ^ 2 * r / (1 + b * r) + (c - a) ^ 2 / b =
        (a * (1 + b * r) - c) ^ 2 / (b * (1 + b * r)) := by
      (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hb.ne', hs.ne'] <;> ring
    have hnonneg : 0 ≤ (a * (1 + b * r) - c) ^ 2 / (b * (1 + b * r)) := by positivity
    rw [← hid] at hnonneg
    simp only [neg_div] at ⊢
    linarith

/-- Actual AC after minimization in r. The remaining nonnegative part of
alpha is deliberately retained for the feasibility improvement in (27). -/
theorem AC_minimized_child_lower {D lam t y m : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hlam7 : lam ≤ 7 / 3)
    (ht : 0 ≤ t) (hy : 0 < y) (hm : 0 ≤ m)
    (hell : -(3 / 4 : ℝ) < ell D lam y)
    (hden : 0 < 1 + ell D lam y * J lam t) :
    alpha D lam * bp lam y + (capA D lam - h D lam y) / y +
      (D * q lam ^ 2 / logActivity lam * epsilon m) * childRatio lam t -
        (q lam ^ 2 / gamma D lam) * (max 0 (h D lam y - D * m)) ^ 2 /
          (cStar lam + ell D lam y * q lam ^ 2) ≤ AC D lam t y / message lam y := by
  have hb := child_correction_den_pos hlam hlam7 hell
  have hr := childRatio_nonneg hlam ht
  have hh : 0 ≤ h D lam y := by
    unfold h
    exact (div_pos (H_pos hD hlam y) (message_pos hlam y)).le
  have hmin := square_rational_lower (mul_nonneg hD.le hm) hh hb hr
  have hscaled := mul_le_mul_of_nonneg_left hmin
    (div_nonneg (sq_nonneg (q lam)) (gamma_pos hD hlam).le)
  have hAC := AC_rational_child_lower hD hlam hlam7 ht hy hell hden
  have hsplit := alpha_split (m := m) hD hlam
  have hsplitr := congrArg (fun z : ℝ => z * childRatio lam t) hsplit
  try dsimp only at hsplitr
  ring_nf at hscaled hAC hsplitr ⊢
  linarith only [hscaled, hAC, hsplitr]

theorem scaled_feasibility_lower {lam t y : ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t) (hy : 0 < y)
    (hfeasible : logMass lam t ≤ y) :
    max 0 (1 - y / logActivity lam) ≤
      (y * q lam / logActivity lam) * childRatio lam t := by
  have hb := logActivity_pos hlam
  have hq := q_pos hlam
  have hr := childRatio_feasible_lower hlam ht hy hfeasible
  have hm := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ y * q lam / logActivity lam by positivity)
  have hid : (y * q lam / logActivity lam) *
      (max 0 (logActivity lam / y - 1) / q lam) = max 0 (1 - y / logActivity lam) := by
    calc
      _ = (y / logActivity lam) * max 0 (logActivity lam / y - 1) := by
        (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hb.ne', hq.ne'] <;> ring
      _ = max 0 (1 - y / logActivity lam) := by
        rw [mul_max_of_nonneg _ _ (div_nonneg hy.le hb.le), mul_zero]
        congr 1
        (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hb.ne', hy.ne'] <;> ring
  rwa [hid] at hm

/-- The exact current child-free inequality (27). It consumes only the
explicit reserve-denominator and ell bounds; no finite row is presumed. -/
theorem AC_child_free_lower {D lam t y m : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hlam7 : lam ≤ 7 / 3)
    (ht : 0 ≤ t) (hy : 0 < y) (hfeasible : logMass lam t ≤ y)
    (hm0 : 0 ≤ m) (hm49 : m ≤ 49 / 100)
    (hell : -(3 / 4 : ℝ) < ell D lam y)
    (hden : 0 < 1 + ell D lam y * J lam t) :
    omega (rho lam y) + T0 D lam y + epsilon m * max 0 (1 - y / logActivity lam) -
      (y / q lam) * (max 0 (K D lam y - m)) ^ 2 / W D lam y ≤
        y * AC D lam t y / (D * message lam y * q lam) := by
  have hq := q_pos hlam
  have hp := message_pos hlam y
  have hg := gamma_pos hD hlam
  have hb := logActivity_pos hlam
  have hbden := child_correction_den_pos hlam hlam7 hell
  have he := epsilon_pos hm0 hm49
  have hmax : max 0 (h D lam y - D * m) = D * max 0 (K D lam y - m) := by
    rw [mul_max_of_nonneg _ _ hD.le, mul_zero]
    congr 1
    unfold K
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne'] <;> ring
  have hpenalty : y / (D * q lam) *
      ((q lam ^ 2 / gamma D lam) * (max 0 (h D lam y - D * m)) ^ 2 /
        (cStar lam + ell D lam y * q lam ^ 2)) =
      (y / q lam) * (max 0 (K D lam y - m)) ^ 2 / W D lam y := by
    rw [hmax, W_eq_child_denominator hD hlam]
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', hq.ne', hg.ne', hbden.ne'] <;> ring
  have hgain := mul_le_mul_of_nonneg_left
    (scaled_feasibility_lower hlam ht hy hfeasible) he.le
  have hgainEq : epsilon m * ((y * q lam / logActivity lam) * childRatio lam t) =
      y / (D * q lam) *
        ((D * q lam ^ 2 / logActivity lam * epsilon m) * childRatio lam t) := by
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', hq.ne', hb.ne'] <;> ring
  rw [hgainEq] at hgain
  have hm := mul_le_mul_of_nonneg_left
    (AC_minimized_child_lower hD hlam hlam7 ht hy hm0 hell hden)
    (show 0 ≤ y / (D * q lam) by positivity)
  rw [mul_sub, mul_add, AC_parent_normalization hD hlam hy, hpenalty] at hm
  have hscale : y / (D * q lam) * (AC D lam t y / message lam y) =
      y * AC D lam t y / (D * message lam y * q lam) := by
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', hq.ne', hp.ne'] <;> ring
  rw [hscale] at hm
  linarith only [hm, hgain]

theorem W_pos_of_ell_bound {D lam y : ℝ} (hD : 0 < D) (hlam : 0 < lam)
    (hlam7 : lam ≤ 7 / 3) (hell : -(3 / 4 : ℝ) < ell D lam y) : 0 < W D lam y := by
  rw [W_eq_child_denominator hD hlam]
  exact div_pos (mul_pos (gamma_pos hD hlam) (child_correction_den_pos hlam hlam7 hell))
    (mul_pos hD (sq_pos_of_pos (q_pos hlam)))

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.ratio_child_monotone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ratio_child_monotone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.AC_div_message
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.AC_div_message
#check Erdos993Lean.Analytic.V213.FreeCountVariance.AC_rational_child_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.AC_rational_child_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.square_rational_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.square_rational_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.AC_minimized_child_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.AC_minimized_child_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.scaled_feasibility_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.scaled_feasibility_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.AC_child_free_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.AC_child_free_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.W_pos_of_ell_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.W_pos_of_ell_bound
