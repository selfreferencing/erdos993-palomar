module

public import Erdos993Lean.Analytic.V213.FreeCountACRationalReduction
public import Erdos993Lean.Analytic.V213.FreeCountACCellCalculus

/-!+Pointwise Real implication of the current A-row formula, after analytic
estimates and rational-to-Real transfer. Every needed estimate is an explicit
inequality. The theorem applies at closed cell endpoints with y>0; y=0 is not
interpreted by total division. It contains no assumption named after the
unproved final paper claim and no finite family is silently imported.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real

theorem omega_interval_lower {lo hi x : ℝ} (hlo : 0 < lo) (hlx : lo ≤ x) (hxh : x ≤ hi) :
    min (omega lo) (omega hi) ≤ omega x := by
  have hx : 0 < x := lt_of_lt_of_le hlo hlx
  have hhi : 0 < hi := lt_of_lt_of_le hx hxh
  by_cases hh : lo < hi
  · let u := (hi - x) / (hi - lo)
    let v := (x - lo) / (hi - lo)
    have hd : 0 < hi - lo := sub_pos.mpr hh
    have hu : 0 ≤ u := div_nonneg (by linarith) hd.le
    have hv : 0 ≤ v := div_nonneg (by linarith) hd.le
    have huv : u + v = 1 := by dsimp [u, v]; field_simp [hd.ne'] <;> ring
    have hends := add_le_add
      (mul_le_mul_of_nonneg_left (min_le_left (omega lo) (omega hi)) hu)
      (mul_le_mul_of_nonneg_left (min_le_right (omega lo) (omega hi)) hv)
    have he : min (omega lo) (omega hi) ≤ u * omega lo + v * omega hi := by
      have hs : u * min (omega lo) (omega hi) + v * min (omega lo) (omega hi) =
          min (omega lo) (omega hi) := by rw [← add_mul, huv, one_mul]
      linarith only [hends, hs]
    have hid : omega x - (u * omega lo + v * omega hi) =
        5 * (x - lo) * (hi - x) / (12 * lo * hi * x) := by
      unfold omega
      dsimp [u, v]
      (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hlo.ne', hhi.ne', hx.ne', hd.ne'] <;> ring
    have hg : 0 ≤ 5 * (x - lo) * (hi - x) / (12 * lo * hi * x) := by
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
      · positivity
    rw [← hid] at hg
    linarith only [he, hg]
  · have hxlo : x = lo := by linarith
    have hhlo : hi = lo := by linarith
    simp [hxlo, hhlo]

/-- Literal A-row implication. Scalar denominator bounds and pointwise cell
estimates remain visible premises until their separate analytic proofs and
record consumers are supplied. -/
theorem AC_positive_of_cell_bounds {D lam t y m d qa betaLo rlo rhi kbar dw tLower psi : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hlam7 : lam ≤ 7 / 3)
    (ht : 0 ≤ t) (hy : 0 < y) (hfeasible : logMass lam t ≤ y)
    (hm0 : 0 ≤ m) (hm49 : m ≤ 49 / 100)
    (hell : -(3 / 4 : ℝ) < ell D lam y)
    (hden : 0 < 1 + ell D lam y * J lam t)
    (hrlo : 0 < rlo) (hrl : rlo ≤ rho lam y) (hru : rho lam y ≤ rhi)
    (hK : K D lam y ≤ kbar) (hdw : 0 < dw) (hW : dw ≤ W D lam y)
    (hT : tLower - psi ≤ T0 D lam y)
    (hbeta : 0 < betaLo) (hbetal : betaLo ≤ logActivity lam)
    (hqa : 0 < qa) (hq : qa ≤ q lam) (hyd : y ≤ d)
    (hrow : 0 < min (omega rlo) (omega rhi) + tLower - psi +
      epsilon m * max 0 (1 - d / betaLo) -
        (d / qa) * (max 0 (kbar - m)) ^ 2 / dw) :
    0 < AC D lam t y := by
  have hb := logActivity_pos hlam
  have hq0 := q_pos hlam
  have hd : 0 < d := lt_of_lt_of_le hy hyd
  have hW0 : 0 < W D lam y := lt_of_lt_of_le hdw hW
  have he := epsilon_pos hm0 hm49
  have homega := omega_interval_lower hrlo hrl hru
  have hbetaRatio : y / logActivity lam ≤ d / betaLo := by
    apply (div_le_div_iff₀ hb hbeta).2
    exact mul_le_mul hyd hbetal hbeta.le hd.le
  have hfeas : max 0 (1 - d / betaLo) ≤ max 0 (1 - y / logActivity lam) :=
    max_le_max le_rfl (by linarith)
  have hfeasScaled := mul_le_mul_of_nonneg_left hfeas he.le
  have hqRatio : y / q lam ≤ d / qa := by
    apply (div_le_div_iff₀ hq0 hqa).2
    exact mul_le_mul hyd hq hqa.le hd.le
  have hmax : max 0 (K D lam y - m) ≤ max 0 (kbar - m) :=
    max_le_max le_rfl (by linarith)
  have hmax0 : 0 ≤ max 0 (K D lam y - m) := le_max_left _ _
  have hbar0 : 0 ≤ max 0 (kbar - m) := le_max_left _ _
  have hmaxSq : (max 0 (K D lam y - m)) ^ 2 ≤ (max 0 (kbar - m)) ^ 2 := by
    nlinarith
  have hnum := mul_le_mul hqRatio hmaxSq (sq_nonneg _)
    (show 0 ≤ d / qa by positivity)
  have hpen : (y / q lam) * (max 0 (K D lam y - m)) ^ 2 / W D lam y ≤
      (d / qa) * (max 0 (kbar - m)) ^ 2 / dw := by
    apply (div_le_div_iff₀ hW0 hdw).2
    calc
      _ ≤ ((d / qa) * (max 0 (kbar - m)) ^ 2) * dw :=
        mul_le_mul_of_nonneg_right hnum hdw.le
      _ ≤ ((d / qa) * (max 0 (kbar - m)) ^ 2) * W D lam y :=
        mul_le_mul_of_nonneg_left hW (by positivity)
  have hchild := AC_child_free_lower hD hlam hlam7 ht hy hfeasible hm0 hm49 hell hden
  have hscaled : 0 < y * AC D lam t y / (D * message lam y * q lam) := by
    linarith only [hrow, homega, hT, hfeasScaled, hpen, hchild]
  have hpositiveDen : 0 < D * message lam y * q lam := by
    exact mul_pos (mul_pos hD (message_pos hlam y)) hq0
  have hnumpos := (lt_div_iff₀ hpositiveDen).mp hscaled
  nlinarith only [hy, hnumpos]

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.omega_interval_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.omega_interval_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.AC_positive_of_cell_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.AC_positive_of_cell_bounds
