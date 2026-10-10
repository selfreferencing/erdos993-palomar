module

public import Erdos993Lean.BCFG.HeavyBaseGates
public import Erdos993Lean.BCFG.TailScalar
public import Erdos993Lean.BCFG.ChartLogEnvelopes

/-! Actual heavy-chart base v=1/2, with only original row/feasible-rho premises.
The positive margins are the printed ones. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem heavy_base_ell_affine {r : AnalyticRow} {lam : ℝ} (hr : InRow r lam) :
    ellUpper r lam ≤ logCenterUpper r+
      (rowHigh r-activityCenter r)/(1+activityCenter r) := by
  have hc := activity_pos (activityCenter_inRow r)
  have hlin := div_le_div_of_nonneg_right
    (sub_le_sub_right hr.2 (activityCenter r)) (show 0 ≤ 1+activityCenter r by linarith)
  have hs : 0 ≤ (lam-activityCenter r)^2/(2*(1+rowHigh r)^2) := by positivity
  unfold ellUpper
  linarith only [hlin,hs]

theorem heavy_base_ell_BC {r : AnalyticRow} {lam : ℝ}
    (hr : InRow r lam) (hrow : r = .B ∨ r = .C) : ellUpper r lam < 2/3 := by
  have h := heavy_base_ell_affine hr
  rcases hrow with rfl | rfl
  · have hgate : logCenterUpper .B+
        (rowHigh .B-activityCenter .B)/(1+activityCenter .B) < (2 : ℝ)/3 := by
      convert heavy_base_B_ell_gate using 1 <;>
        norm_num [logCenterUpper,rowHigh,activityCenter,rowLow]
    exact h.trans_lt hgate
  · have hgate : logCenterUpper .C+
        (rowHigh .C-activityCenter .C)/(1+activityCenter .C) < (2 : ℝ)/3 := by
      convert heavy_base_C_ell_gate using 1 <;>
        norm_num [logCenterUpper,rowHigh,activityCenter,rowLow]
    exact h.trans_lt hgate

theorem heavy_base_ell_FG {r : AnalyticRow} {lam : ℝ}
    (hr : InRow r lam) (hrow : r = .F ∨ r = .G) : ellUpper r lam < 4/3 := by
  have h := heavy_base_ell_affine hr
  rcases hrow with rfl | rfl
  · have hgate : logCenterUpper .F+
        (rowHigh .F-activityCenter .F)/(1+activityCenter .F) < (4 : ℝ)/3 := by
      convert heavy_base_F_ell_gate using 1 <;>
        norm_num [logCenterUpper,rowHigh,activityCenter,rowLow]
    exact h.trans_lt hgate
  · have hgate : logCenterUpper .G+
        (rowHigh .G-activityCenter .G)/(1+activityCenter .G) < (4 : ℝ)/3 := by
      convert heavy_base_G_ell_gate using 1 <;>
        norm_num [logCenterUpper,rowHigh,activityCenter,rowLow]
    exact h.trans_lt hgate

theorem heavy_base_upper_identity (r : AnalyticRow) (lam : ℝ) :
    heavyUpper r lam (1/2) = ellUpper r lam+(heavyExponent r : ℝ)*(25/36) := by
  norm_num [heavyUpper,heavyZ]

theorem heavy_base_upper_BC {r : AnalyticRow} {lam : ℝ}
    (hr : InRow r lam) (hrow : r = .B ∨ r = .C) : heavyUpper r lam (1/2) < 31/9 := by
  have hell := heavy_base_ell_BC hr hrow
  have hm : heavyExponent r = 4 := by rcases hrow with rfl | rfl <;> rfl
  rw [heavy_base_upper_identity,hm]
  norm_num only [Nat.cast_ofNat]
  linarith only [hell]

theorem heavy_base_upper_FG {r : AnalyticRow} {lam : ℝ}
    (hr : InRow r lam) (hrow : r = .F ∨ r = .G) : heavyUpper r lam (1/2) < 11/2 := by
  have hell := heavy_base_ell_FG hr hrow
  have hm : heavyExponent r = 6 := by rcases hrow with rfl | rfl <;> rfl
  rw [heavy_base_upper_identity,hm]
  norm_num only [Nat.cast_ofNat]
  linarith only [hell]

theorem heavy_base_upper_pos {r : AnalyticRow} {lam : ℝ} (hr : InRow r lam) :
    0 < heavyUpper r lam (1/2) := by
  have hl := activity_pos hr
  have hh : (0 : ℝ) < 1/2 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*2 < 1*1))
  have hh1 : (1 : ℝ)/2 ≤ 1 := by
    simpa only [Nat.cast_one,Nat.cast_ofNat,div_one] using
      (tail_fraction_le (by decide +kernel) (by decide +kernel)
        (by decide +kernel : (1 : ℕ)*1 ≤ 1*2))
  have hw := heavyOmega_pos (r := r) hl hh
  have hw1 : heavyOmega r lam (1/2) < 1 := by
    unfold heavyOmega
    apply (div_lt_one (show 0 < 1+lam by linarith)).2
    exact (pow_le_one₀ hh.le hh1).trans_lt (show (1 : ℝ) < 1+lam by linarith)
  have hY : 0 < logMass (heavyOmega r lam (1/2)) :=
    neg_pos.mpr (Real.log_neg hw hw1)
  exact hY.trans_le (heavy_logMass_bounds ⟨hr,le_rfl,hh1⟩).2

theorem heavy_base_rate_identity {r : AnalyticRow} {lam : ℝ} (hl : 0 < lam) :
    rCoeff r lam (heavyOmega r lam (1/2)) =
      kappa r*((1+lam)*(2 : ℝ)^(heavyExponent r)+lam) := by
  have hh : (0 : ℝ) < 1/2 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*2 < 1*1))
  have hw := heavyOmega_pos (r := r) hl hh
  unfold rCoeff gamma
  rw [rate_identity _ _ _ hl.ne' hw.ne' (by positivity)]
  unfold heavyOmega
  rw [one_div_pow]
  field_simp [show (1+lam : ℝ) ≠ 0 by linarith,
    pow_ne_zero (heavyExponent r) (show (2 : ℝ) ≠ 0 by
      exact_mod_cast (by decide +kernel : (2 : ℕ) ≠ 0))] <;> ring

theorem heavy_base_rate_BC {r : AnalyticRow} {lam : ℝ}
    (hr : InRow r lam) (hrow : r = .B ∨ r = .C) :
    (1024 : ℝ)/125 ≤ rCoeff r lam (heavyOmega r lam (1/2)) := by
  have hl := activity_pos hr
  have hlo : (3 : ℝ)/5 ≤ lam := by
    rcases hrow with rfl | rfl
    · exact hr.1
    · exact heavy_base_C_low_gate.trans hr.1
  have hkap := (tail_BC_row_data hr hrow).2.1
  have hm : heavyExponent r = 4 := by rcases hrow with rfl | rfl <;> rfl
  rw [heavy_base_rate_identity hl,hkap,hm]
  norm_num only [Nat.cast_ofNat,pow_succ,pow_zero,mul_one]
  linarith only [hlo,hl]

theorem heavy_base_rate_FG {r : AnalyticRow} {lam : ℝ}
    (hr : InRow r lam) (hrow : r = .F ∨ r = .G) :
    (1248 : ℝ)/25 ≤ rCoeff r lam (heavyOmega r lam (1/2)) := by
  have hl := activity_pos hr
  have hlo : (8 : ℝ)/5 ≤ lam := by
    rcases hrow with rfl | rfl
    · exact hr.1
    · exact heavy_base_G_low_gate.trans hr.1
  have hkap := (tail_FG_row_data hr hrow).2.1
  have hm : heavyExponent r = 6 := by rcases hrow with rfl | rfl <;> rfl
  rw [heavy_base_rate_identity hl,hkap,hm]
  norm_num only [Nat.cast_ofNat,pow_succ,pow_zero,mul_one]
  linarith only [hlo,hl]

theorem heavy_base_P_upper {r : AnalyticRow} {lam omega rho gammaHi : ℝ}
    (hl : 0 < lam) (hw : 0 < omega) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1)
    (hg : gamma r lam ≤ gammaHi) : tailP r lam omega rho ≤ gammaHi+1 := by
  have hp := (occupation_bounds hl hw).1.le
  have he : eCoeff r lam omega ≤ gamma r lam :=
    (mul_le_mul_of_nonneg_left (cubicEnvelope_le_one hp) (gamma_pos hl).le).trans_eq
      (mul_one _)
  have hd : dCoeff lam omega*rho ≤ rho := by
    simpa only [dCoeff, one_mul] using
      (mul_le_mul_of_nonneg_right (sub_le_self (1 : ℝ) hp) hr0)
  unfold tailP
  linarith only [he,hd,hg,hr1]

theorem heavy_base_BC_diagonal {r : AnalyticRow} {lam rho : ℝ}
    (hr : InRow r lam) (hrow : r = .B ∨ r = .C)
    (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) :
    (4349 : ℝ)/1125 < rCoeff r lam (heavyOmega r lam (1/2))-
      tailP r lam (heavyOmega r lam (1/2)) rho*heavyUpper r lam (1/2) := by
  have hl := activity_pos hr
  have hh : (0 : ℝ) < 1/2 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*2 < 1*1))
  have hw := heavyOmega_pos (r := r) hl hh
  obtain ⟨hlhi,hkap,_,_,_,_⟩ := tail_BC_row_data hr hrow
  have hg : gamma r lam ≤ 32/125 := by
    unfold gamma
    rw [hkap]
    have h := mul_le_mul_of_nonneg_left hlhi (tail_fraction_pos (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*25 < 8*1)).le
    convert h using 1 <;> norm_num
  have hP : tailP r lam (heavyOmega r lam (1/2)) rho ≤ (157 : ℝ)/125 := by
    convert heavy_base_P_upper hl hw hr0 hr1 hg using 1 <;> norm_num
  have hU := heavy_base_upper_BC hr hrow
  have hU0 := heavy_base_upper_pos hr
  have hm := mul_le_mul_of_nonneg_right hP hU0.le
  have hs := mul_lt_mul_of_pos_left hU (tail_fraction_pos (by decide +kernel)
    (by decide +kernel : (0 : ℕ)*125 < 157*1))
  have hR := heavy_base_rate_BC hr hrow
  have hid : (1024 : ℝ)/125-(157/125)*(31/9) = 4349/1125 := by norm_num
  linarith only [hm,hs,hR,hid]

theorem heavy_base_FG_diagonal {r : AnalyticRow} {lam rho : ℝ}
    (hr : InRow r lam) (hrow : r = .F ∨ r = .G)
    (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) :
    (16613 : ℝ)/400 < rCoeff r lam (heavyOmega r lam (1/2))-
      tailP r lam (heavyOmega r lam (1/2)) rho*heavyUpper r lam (1/2) := by
  have hl := activity_pos hr
  have hh : (0 : ℝ) < 1/2 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*2 < 1*1))
  have hw := heavyOmega_pos (r := r) hl hh
  obtain ⟨hlhi,hkap,_,_,_,_,_⟩ := tail_FG_row_data hr hrow
  have hg : gamma r lam ≤ 21/40 := by
    unfold gamma
    rw [hkap]
    have h := mul_le_mul_of_nonneg_left hlhi (tail_fraction_pos (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*10 < 3*1)).le
    convert h using 1 <;> norm_num
  have hP : tailP r lam (heavyOmega r lam (1/2)) rho ≤ (61 : ℝ)/40 := by
    convert heavy_base_P_upper hl hw hr0 hr1 hg using 1 <;> norm_num
  have hU := heavy_base_upper_FG hr hrow
  have hU0 := heavy_base_upper_pos hr
  have hm := mul_le_mul_of_nonneg_right hP hU0.le
  have hs := mul_lt_mul_of_pos_left hU (tail_fraction_pos (by decide +kernel)
    (by decide +kernel : (0 : ℕ)*40 < 61*1))
  have hR := heavy_base_rate_FG hr hrow
  have hid : (1248 : ℝ)/25-(61/40)*(11/2) = 16613/400 := by norm_num
  linarith only [hm,hs,hR,hid]

/-- The actual heavy base diagonal is positive for every allowed row and rho. -/
theorem heavy_base_diagonal_pos {r : AnalyticRow} {lam rho : ℝ}
    (hr : InRow r lam) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) :
    0 < rCoeff r lam (heavyOmega r lam (1/2))-
      tailP r lam (heavyOmega r lam (1/2)) rho*heavyUpper r lam (1/2) := by
  cases r with
  | B =>
    exact heavy_base_BC_margin_pos_gate.trans
      (heavy_base_BC_diagonal hr (Or.inl rfl) hr0 hr1)
  | C =>
    exact heavy_base_BC_margin_pos_gate.trans
      (heavy_base_BC_diagonal hr (Or.inr rfl) hr0 hr1)
  | F =>
    exact heavy_base_FG_margin_pos_gate.trans
      (heavy_base_FG_diagonal hr (Or.inl rfl) hr0 hr1)
  | G =>
    exact heavy_base_FG_margin_pos_gate.trans
      (heavy_base_FG_diagonal hr (Or.inr rfl) hr0 hr1)

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavy_base_ell_affine
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_ell_affine
#check Erdos993Lean.BCFG.Analytic.heavy_base_ell_BC
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_ell_BC
#check Erdos993Lean.BCFG.Analytic.heavy_base_ell_FG
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_ell_FG
#check Erdos993Lean.BCFG.Analytic.heavy_base_upper_identity
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_upper_identity
#check Erdos993Lean.BCFG.Analytic.heavy_base_upper_BC
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_upper_BC
#check Erdos993Lean.BCFG.Analytic.heavy_base_upper_FG
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_upper_FG
#check Erdos993Lean.BCFG.Analytic.heavy_base_upper_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_upper_pos
#check Erdos993Lean.BCFG.Analytic.heavy_base_rate_identity
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_rate_identity
#check Erdos993Lean.BCFG.Analytic.heavy_base_rate_BC
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_rate_BC
#check Erdos993Lean.BCFG.Analytic.heavy_base_rate_FG
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_rate_FG
#check Erdos993Lean.BCFG.Analytic.heavy_base_P_upper
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_P_upper
#check Erdos993Lean.BCFG.Analytic.heavy_base_BC_diagonal
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_BC_diagonal
#check Erdos993Lean.BCFG.Analytic.heavy_base_FG_diagonal
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_FG_diagonal
#check Erdos993Lean.BCFG.Analytic.heavy_base_diagonal_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_diagonal_pos
