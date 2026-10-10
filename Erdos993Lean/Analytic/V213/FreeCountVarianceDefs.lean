module

public import Erdos993Lean.Analytic.Reserve.Step

/-!
# The free-count reserve of version 2.13 of the manuscript: definitions and exact identities

Source: Section 3, equations (13), (15), (17).
This is the five-cap curve of that section, not the older `Reserve.Band` curve.
`logActivity` is the paper's beta; the signed linear coefficient of the generic
reserve is zero. No numerical comparison, derivative estimate, or graph bound
is asserted here. In particular, positivity of `Z`, `CA`, and `AC` is not assumed
silently or asserted as an unproved named result.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real

noncomputable def q (lam : ℝ) : ℝ := lam / (1 + lam)
noncomputable def logActivity (lam : ℝ) : ℝ := log (1 + lam)
noncomputable def alpha (D lam : ℝ) : ℝ := 7 * D * q lam ^ 2 / (12 * logActivity lam)
noncomputable def gamma (D lam : ℝ) : ℝ := 5 * D * logActivity lam / 12
noncomputable def capA (D lam : ℝ) : ℝ := 1 + (D - 1) * q lam
noncomputable def reserve (D lam phi chi : ℝ) : ℝ :=
  alpha D lam * phi + gamma D lam * chi ^ 2 / phi

noncomputable def message (lam x : ℝ) : ℝ := Reserve.msg lam x
noncomputable def logMass (lam x : ℝ) : ℝ := Reserve.lmass lam x

theorem q_pos {lam : ℝ} (hlam : 0 < lam) : 0 < q lam := by
  unfold q
  positivity

theorem q_lt_one {lam : ℝ} (hlam : 0 < lam) : q lam < 1 := by
  unfold q
  apply (div_lt_one (by positivity)).2
  linarith

theorem logActivity_pos {lam : ℝ} (hlam : 0 < lam) : 0 < logActivity lam := by
  apply Real.log_pos
  linarith

theorem alpha_pos {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) : 0 < alpha D lam := by
  unfold alpha
  have := q_pos hlam
  have := logActivity_pos hlam
  positivity

theorem gamma_pos {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) : 0 < gamma D lam := by
  unfold gamma
  have := logActivity_pos hlam
  positivity

theorem reserve_nonneg {D lam phi chi : ℝ} (hD : 0 < D) (hlam : 0 < lam)
    (hphi : 0 < phi) : 0 ≤ reserve D lam phi chi := by
  unfold reserve
  have := alpha_pos hD hlam
  have := gamma_pos hD hlam
  positivity

theorem alpha_mul_gamma {D lam : ℝ} (hlam : 0 < lam) :
    alpha D lam * gamma D lam = 35 * D ^ 2 * q lam ^ 2 / 144 := by
  have hb := (logActivity_pos hlam).ne'
  unfold alpha gamma
  field_simp <;> ring

theorem selected_leaf_identity {D lam : ℝ} (hlam : 0 < lam) :
    D * q lam ^ 2 - alpha D lam * logActivity lam -
      gamma D lam * q lam ^ 2 / logActivity lam = 0 := by
  have hb := (logActivity_pos hlam).ne'
  unfold alpha gamma
  field_simp <;> ring

theorem selected_leaf_reserve {D lam : ℝ} (hlam : 0 < lam) :
    reserve D lam (logActivity lam) (q lam) =
      capA D lam * q lam - q lam * (1 - q lam) := by
  have hid := selected_leaf_identity (D := D) hlam
  unfold reserve capA
  nlinarith

theorem message_pos {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    0 < message lam x := Reserve.msg_pos hlam x

theorem message_lt_one {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    message lam x < 1 := Reserve.msg_lt_one hlam x

theorem logMass_pos {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    0 < logMass lam x := Reserve.lmass_pos hlam x

/-- Literal message expression in the printed parent/child definitions. -/
theorem message_eq_exp_quotient {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    message lam x = lam / (exp x + lam) := by
  have hx := (Real.exp_pos x).ne'
  have hd : exp x + lam ≠ 0 := ne_of_gt (by positivity)
  have hd0 : 1 + lam * (exp x)⁻¹ ≠ 0 := ne_of_gt (by positivity)
  unfold message Reserve.msg
  rw [Real.exp_neg]
  field_simp [hx, hd, hd0] <;> ring

theorem logMass_eq_log (lam x : ℝ) :
    logMass lam x = log (1 + lam * exp (-x)) := rfl

theorem logMass_eq_neg_log {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    logMass lam x = -log (1 - message lam x) := Reserve.lmass_eq_neg_log hlam x

@[simp] theorem message_zero (lam : ℝ) : message lam 0 = q lam := by
  simp [message, Reserve.msg, q]

@[simp] theorem logMass_zero (lam : ℝ) : logMass lam 0 = logActivity lam := by
  simp [logMass, Reserve.lmass, logActivity]

theorem one_sub_message {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    1 - message lam x = message lam x * (exp x / lam) := by
  rw [message_eq_exp_quotient hlam]
  have hl := hlam.ne'
  have hd : exp x + lam ≠ 0 := ne_of_gt (by positivity)
  field_simp <;> ring

/-- Arguments are activity, child log-mass sum `t`, parent log-mass sum `y`. -/
noncomputable def E (lam t y : ℝ) : ℝ :=
  1 - message lam y + message lam y * t / logMass lam t - logMass lam y / y
noncomputable def H (D lam y : ℝ) : ℝ :=
  message lam y * (1 - message lam y) + gamma D lam * message lam y ^ 2 / logMass lam y
noncomputable def J (lam t : ℝ) : ℝ := message lam t ^ 2 * t / logMass lam t
noncomputable def L (D lam y : ℝ) : ℝ := gamma D lam * (1 - message lam y) - H D lam y * y
noncomputable def Z (D lam t y : ℝ) : ℝ := message lam y * gamma D lam + L D lam y * J lam t
noncomputable def CC (D lam t y : ℝ) : ℝ := alpha D lam * E lam t y
noncomputable def CA (D lam t y : ℝ) : ℝ :=
  alpha D lam * E lam t y +
    message lam y * gamma D lam * L D lam y * (message lam t / logMass lam t) ^ 2 / Z D lam t y
noncomputable def AC (D lam t y : ℝ) : ℝ :=
  alpha D lam * E lam t y + (capA D lam * message lam y - H D lam y) / y -
    H D lam y ^ 2 * J lam t / Z D lam t y

theorem H_pos {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) : 0 < H D lam y := by
  have hp := message_pos hlam y
  have hp1 := message_lt_one hlam y
  have hf := logMass_pos hlam y
  have hg := gamma_pos hD hlam
  unfold H
  have : 0 < 1 - message lam y := sub_pos.mpr hp1
  positivity

theorem J_nonneg {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) : 0 ≤ J lam t := by
  have hf := logMass_pos hlam t
  unfold J
  positivity

theorem E_eq_coefE (lam t y : ℝ) : E lam t y = Reserve.coefE lam t y := rfl
theorem J_eq_coefJ (lam t : ℝ) : J lam t = Reserve.coefJ lam t := rfl
theorem H_eq_cH (D lam y : ℝ) : H D lam y = Reserve.cH (gamma D lam) lam y := rfl
theorem L_eq_cL (D lam y : ℝ) : L D lam y = Reserve.cL (gamma D lam) lam y := rfl
theorem Z_eq_cZ (D lam t y : ℝ) : Z D lam t y = Reserve.cZ (gamma D lam) lam t y := rfl

theorem CC_eq_compCC (D lam t y : ℝ) :
    CC D lam t y = Reserve.compCC (gamma D lam) lam (alpha D lam) 0 t y := by
  simp [CC, E_eq_coefE, Reserve.compCC]

theorem CA_eq_compCB (D lam t y : ℝ) :
    CA D lam t y = Reserve.compCB (gamma D lam) lam (alpha D lam) 0 t y := by
  simp [CA, E_eq_coefE, L_eq_cL, Z_eq_cZ, message, logMass, Reserve.compCB]

theorem AC_eq_compBC (D lam t y : ℝ) :
    AC D lam t y = Reserve.compBC (gamma D lam) lam (alpha D lam) 0 (capA D lam) t y := by
  simp only [AC, E_eq_coefE, H_eq_cH, J_eq_coefJ, Z_eq_cZ, Reserve.compBC,
    zero_mul, zero_div, add_zero, sub_zero]
  unfold Reserve.coefJ message
  ring

noncomputable def B (lam y : ℝ) : ℝ := logMass lam y / message lam y
noncomputable def ap (lam y : ℝ) : ℝ := exp y / lam
noncomputable def h (D lam y : ℝ) : ℝ := H D lam y / message lam y
noncomputable def ell (D lam y : ℝ) : ℝ := L D lam y / (message lam y * gamma D lam)
noncomputable def bp (lam y : ℝ) : ℝ := ap lam y - B lam y / y

theorem B_pos {lam : ℝ} (hlam : 0 < lam) (y : ℝ) : 0 < B lam y := by
  exact div_pos (logMass_pos hlam y) (message_pos hlam y)

theorem h_normalized {D lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    h D lam y = 1 - message lam y + gamma D lam / B lam y := by
  have hp := (message_pos hlam y).ne'
  have hf := (logMass_pos hlam y).ne'
  unfold h H B
  field_simp <;> ring

theorem ell_normalized {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    ell D lam y = ap lam y - y * h D lam y / gamma D lam := by
  have hp := (message_pos hlam y).ne'
  have hg := (gamma_pos hD hlam).ne'
  unfold ell L h ap
  rw [one_sub_message hlam y]
  field_simp <;> ring

theorem E_normalized {lam : ℝ} (hlam : 0 < lam) {t y : ℝ} (hy : 0 < y) :
    E lam t y = message lam y * (t / logMass lam t + bp lam y) := by
  have hp := (message_pos hlam y).ne'
  have ht := (logMass_pos hlam t).ne'
  have hy' := hy.ne'
  unfold E bp B ap
  rw [one_sub_message hlam y]
  field_simp <;> ring

theorem Z_normalized {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (t y : ℝ) :
    Z D lam t y = message lam y * gamma D lam * (1 + ell D lam y * J lam t) := by
  have hp := (message_pos hlam y).ne'
  have hg := (gamma_pos hD hlam).ne'
  unfold Z ell
  field_simp <;> ring

@[simp] theorem J_zero (lam : ℝ) : J lam 0 = 0 := by simp [J]

theorem Z_zero (D lam y : ℝ) : Z D lam 0 y = message lam y * gamma D lam := by
  simp [Z]

/-- The actual denominator bound follows from the two independently required scalar bounds.
This reduction does not assert either of those analytic/numerical premises. -/
theorem Z_gt_three_quarters_of_bounds {D lam t y eta j : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (ht : 0 ≤ t)
    (heta : 0 < eta) (hj : 0 < j) (hprod : eta * j = (1 / 4 : ℝ))
    (hJ : J lam t < j) (hell : -eta < ell D lam y) :
    (3 / 4 : ℝ) * message lam y * gamma D lam < Z D lam t y := by
  have hJ0 := J_nonneg hlam ht
  have hprod1 : -eta * J lam t ≤ ell D lam y * J lam t :=
    mul_le_mul_of_nonneg_right hell.le hJ0
  have hprod2 : -eta * j < -eta * J lam t :=
    mul_lt_mul_of_neg_left hJ (by linarith)
  have hfac : (3 / 4 : ℝ) < 1 + ell D lam y * J lam t := by nlinarith
  have hpg : 0 < message lam y * gamma D lam :=
    mul_pos (message_pos hlam y) (gamma_pos hD hlam)
  rw [Z_normalized hD hlam]
  calc
    (3 / 4 : ℝ) * message lam y * gamma D lam =
        (message lam y * gamma D lam) * (3 / 4) := by ring
    _ < (message lam y * gamma D lam) * (1 + ell D lam y * J lam t) :=
      mul_lt_mul_of_pos_left hfac hpg

end Erdos993Lean.Analytic.V213.FreeCountVariance

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.q_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.q_lt_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_lt_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logActivity_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logActivity_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.gamma_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.gamma_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.reserve_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.reserve_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_mul_gamma
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_mul_gamma
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_leaf_identity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_leaf_identity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_leaf_reserve
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_leaf_reserve
#check Erdos993Lean.Analytic.V213.FreeCountVariance.message_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.message_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.message_lt_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.message_lt_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.message_eq_exp_quotient
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.message_eq_exp_quotient
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_eq_log
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_eq_log
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_eq_neg_log
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_eq_neg_log
#check Erdos993Lean.Analytic.V213.FreeCountVariance.message_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.message_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.one_sub_message
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.one_sub_message
#check Erdos993Lean.Analytic.V213.FreeCountVariance.H_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.H_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.J_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.J_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.E_eq_coefE
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.E_eq_coefE
#check Erdos993Lean.Analytic.V213.FreeCountVariance.J_eq_coefJ
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.J_eq_coefJ
#check Erdos993Lean.Analytic.V213.FreeCountVariance.H_eq_cH
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.H_eq_cH
#check Erdos993Lean.Analytic.V213.FreeCountVariance.L_eq_cL
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.L_eq_cL
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Z_eq_cZ
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Z_eq_cZ
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CC_eq_compCC
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CC_eq_compCC
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_eq_compCB
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_eq_compCB
#check Erdos993Lean.Analytic.V213.FreeCountVariance.AC_eq_compBC
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.AC_eq_compBC
#check Erdos993Lean.Analytic.V213.FreeCountVariance.B_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.B_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.h_normalized
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.h_normalized
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_normalized
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_normalized
#check Erdos993Lean.Analytic.V213.FreeCountVariance.E_normalized
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.E_normalized
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Z_normalized
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Z_normalized
#check Erdos993Lean.Analytic.V213.FreeCountVariance.J_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.J_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Z_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Z_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Z_gt_three_quarters_of_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Z_gt_three_quarters_of_bounds
