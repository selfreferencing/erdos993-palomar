module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceChildDerivatives

/-!+Current Section 3, equations (24) and (26). These are the actual Real parent
quantities, not rational worksheet surrogates. All activity derivatives keep
D fixed. No activity curvature, cell positivity or completed AC claim is
assumed under a named contract.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real

noncomputable def cStar (lam : ℝ) : ℝ := 2 * logActivity lam * (1 - q lam)
noncomputable def rho (lam y : ℝ) : ℝ := B lam y * q lam / logActivity lam
noncomputable def K (D lam y : ℝ) : ℝ := h D lam y / D
noncomputable def omega (r : ℝ) : ℝ := 1 - (7 * r + 5 / r) / 12
noncomputable def T0 (D lam y : ℝ) : ℝ :=
  (message lam y / q lam - 1) / D +
    (7 / 12 : ℝ) * (y * exp y) / ((1 + lam) * logActivity lam)
noncomputable def W (D lam y : ℝ) : ℝ :=
  (5 / 12 : ℝ) * (logActivity lam * exp y / lam +
    2 * (logActivity lam / q lam) ^ 2 / (1 + lam)) - y * K D lam y
noncomputable def epsilon (m : ℝ) : ℝ := 7 / 12 - 12 * m ^ 2 / 5

theorem cStar_pos {lam : ℝ} (hlam : 0 < lam) : 0 < cStar lam := by
  have hb := logActivity_pos hlam
  have hq := sub_pos.mpr (q_lt_one hlam)
  unfold cStar
  positivity

/-- Used by the coupled endpoint ratio interpretation, without independently
replacing numerator and denominator by unrelated brackets. -/
theorem B_antitone {lam : ℝ} (hlam : 0 < lam) : Antitone (B lam) := by
  apply antitone_of_deriv_nonpos (fun y => (B_hasDerivAt hlam y).differentiableAt)
  intro y
  rw [(B_hasDerivAt hlam y).deriv]
  exact neg_nonpos.mpr (varpi_nonneg hlam y)

theorem rho_pos {lam : ℝ} (hlam : 0 < lam) (y : ℝ) : 0 < rho lam y := by
  unfold rho
  exact div_pos (mul_pos (B_pos hlam y) (q_pos hlam)) (logActivity_pos hlam)

@[simp] theorem rho_zero {lam : ℝ} (hlam : 0 < lam) : rho lam 0 = 1 := by
  have hq := (q_pos hlam).ne'
  have hb := (logActivity_pos hlam).ne'
  simp only [rho, B, logMass_zero, message_zero]
  field_simp [hq, hb]

theorem rho_antitone_parent {lam : ℝ} (hlam : 0 < lam) : Antitone (rho lam) := by
  intro x y hxy
  unfold rho
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (B_antitone hlam hxy) (q_pos hlam).le)
    (logActivity_pos hlam).le

theorem rho_le_one {lam y : ℝ} (hlam : 0 < lam) (hy : 0 ≤ y) : rho lam y ≤ 1 := by
  have hh := rho_antitone_parent hlam hy
  simpa only [rho_zero hlam] using hh

theorem rho_hasDerivAt_parent {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (rho lam) (-varpi lam y * q lam / logActivity lam) y := by
  exact ((B_hasDerivAt hlam y).mul_const (q lam)).div_const (logActivity lam)

theorem K_hasDerivAt_parent {D lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (K D lam)
      ((message lam y * (1 - message lam y) +
        gamma D lam * varpi lam y / B lam y ^ 2) / D) y :=
  (h_hasDerivAt hlam y).div_const D

theorem K_deriv_pos_parent {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    0 < deriv (K D lam) y := by
  rw [(K_hasDerivAt_parent (D := D) hlam y).deriv]
  have hh := h_deriv_pos hD hlam y
  rw [(h_hasDerivAt (D := D) hlam y).deriv] at hh
  exact div_pos hh hD

theorem q_hasDerivAt {lam : ℝ} (hlam : 0 < lam) :
    HasDerivAt q (1 / (1 + lam) ^ 2) lam := by
  change HasDerivAt (fun a : ℝ => a / (1 + a)) _ lam
  apply ((hasDerivAt_id lam).div ((hasDerivAt_id lam).const_add 1)
    (ne_of_gt (show 0 < 1 + lam by linarith))).congr_deriv
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> ring

theorem logActivity_hasDerivAt {lam : ℝ} (hlam : 0 < lam) :
    HasDerivAt logActivity (1 / (1 + lam)) lam := by
  unfold logActivity
  exact ((hasDerivAt_id lam).const_add 1).log
    (ne_of_gt (show 0 < 1 + lam by linarith))

theorem B_hasDerivAt_activity {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (fun a => B a y) (varpi lam y / lam) lam := by
  have hp := (message_pos hlam y).ne'
  change HasDerivAt (fun a => logMass a y / message a y) _ lam
  apply ((logMass_hasDerivAt_activity hlam y).div
    (message_hasDerivAt_activity hlam y) hp).congr_deriv
  unfold varpi B
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hlam.ne', hp] <;> ring

/-- Exact activity logarithmic derivative, before the h0 monotonicity sign. -/
theorem rho_hasDerivAt_activity {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (fun a => rho a y)
      (rho lam y / lam *
        (1 / B lam y + message lam y - q lam - q lam / logActivity lam)) lam := by
  have hb := (logActivity_pos hlam).ne'
  have hB := (B_pos hlam y).ne'
  have hd : 1 + lam ≠ 0 := ne_of_gt (by linarith)
  change HasDerivAt (fun a => B a y * q a / logActivity a) _ lam
  apply (((B_hasDerivAt_activity hlam y).mul (q_hasDerivAt hlam)).div
    (logActivity_hasDerivAt hlam) hb).congr_deriv
  unfold rho varpi q
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hlam.ne', hb, hB, hd] <;> ring

theorem W_eq_child_denominator {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    W D lam y = gamma D lam * (cStar lam + ell D lam y * q lam ^ 2) /
      (D * q lam ^ 2) := by
  have hd := hD.ne'
  have hl := hlam.ne'
  have hq := (q_pos hlam).ne'
  have hg := (gamma_pos hD hlam).ne'
  have h1 : 1 + lam ≠ 0 := ne_of_gt (by linarith)
  rw [ell_normalized hD hlam]
  unfold W K cStar ap gamma q
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hd, hl, h1, (logActivity_pos hlam).ne'] <;> ring

theorem epsilon_pos {m : ℝ} (hm0 : 0 ≤ m) (hm49 : m ≤ 49 / 100) : 0 < epsilon m := by
  have hs : m ^ 2 ≤ (49 / 100 : ℝ) ^ 2 := by nlinarith
  unfold epsilon
  nlinarith

theorem alpha_split {D lam m : ℝ} (hD : 0 < D) (hlam : 0 < lam) :
    alpha D lam - D ^ 2 * m ^ 2 * q lam ^ 2 / gamma D lam =
      D * q lam ^ 2 / logActivity lam * epsilon m := by
  have hd := hD.ne'
  have hb := (logActivity_pos hlam).ne'
  unfold alpha gamma epsilon
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hd, hb] <;> ring

/-- Exact parent part of (27), with no child or cell bound. -/
theorem AC_parent_normalization {D lam y : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hy : 0 < y) :
    y / (D * q lam) * (alpha D lam * bp lam y + (capA D lam - h D lam y) / y) =
      omega (rho lam y) + T0 D lam y := by
  have hd := hD.ne'
  have hl := hlam.ne'
  have hb := (logActivity_pos hlam).ne'
  have hq := (q_pos hlam).ne'
  have hB := (B_pos hlam y).ne'
  have hp := (message_pos hlam y).ne'
  have h1 : 1 + lam ≠ 0 := ne_of_gt (by linarith)
  rw [h_normalized hlam]
  unfold omega rho T0 bp ap capA alpha gamma q
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hd, hl, hb, hB, hp, h1, hy.ne'] <;> ring

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.cStar_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.cStar_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.B_antitone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.B_antitone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_antitone_parent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_antitone_parent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_le_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_le_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_hasDerivAt_parent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_hasDerivAt_parent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.K_hasDerivAt_parent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.K_hasDerivAt_parent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.K_deriv_pos_parent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.K_deriv_pos_parent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.q_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logActivity_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logActivity_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.B_hasDerivAt_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.B_hasDerivAt_activity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_hasDerivAt_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_hasDerivAt_activity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.W_eq_child_denominator
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.W_eq_child_denominator
#check Erdos993Lean.Analytic.V213.FreeCountVariance.epsilon_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.epsilon_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_split
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_split
#check Erdos993Lean.Analytic.V213.FreeCountVariance.AC_parent_normalization
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.AC_parent_normalization
