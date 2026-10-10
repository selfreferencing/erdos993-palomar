module

public import Erdos993Lean.BCFG.TailLogMass
public import Erdos993Lean.BCFG.TailSquareMinimum
public import Erdos993Lean.BCFG.ChartGeometry
public import Erdos993Lean.Analytic.V213.ResponseOneVertex

/-! Literal small-omega scalar theorem. Final hypotheses are only the original
closed row, positive tail omega, and feasible rho. No K, P, eta, source, mass,
or square-minimum inequality is assumed by the final scalar theorem. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

def tailCutoff : AnalyticRow → ℝ
  | .B | .C => 1/16
  | .F | .G => 1/64
def tailH : AnalyticRow → ℝ
  | .B | .C => 3/4
  | .F | .G => 5/8
def tailP (r : AnalyticRow) (lam omega rho : ℝ) : ℝ :=
  eCoeff r lam omega+dCoeff lam omega*rho
def tailK (r : AnalyticRow) (omega rho : ℝ) : ℝ :=
  alpha r*(1-rho)+beta r*rho*tailH r*logMass omega
def tailEta (r : AnalyticRow) (lam omega : ℝ) : ℝ :=
  rCoeff r lam omega/logMass omega
def tailPsi (r : AnalyticRow) (lam omega rho z : ℝ) : ℝ :=
  tailK r omega rho-tailP r lam omega rho+
    2*(tailP r lam omega rho-centerResponse r)*(1-z)+
    (tailEta r lam omega-tailP r lam omega rho)*(1-z)^2

theorem tail_rhoZero_gt_inverse {lam omega : ℝ} (hl : 0 < lam) (hw : 0 < omega) :
    1/(1+lam) < rhoZero lam omega := by
  have h1 : 0 < 1+lam := by linarith
  have h2 : 0 < 1+lam+lam*omega := by positivity
  unfold rhoZero
  apply (div_lt_div_iff₀ h1 h2).2
  have hpos := mul_pos (mul_pos hl hl) hw
  nlinarith only [hpos]

theorem tail_occupation_cap {lam omega cap : ℝ}
    (hl : 0 < lam) (hw : 0 < omega) (hcap : 0 ≤ cap) (hx : lam*omega ≤ cap) :
    occupation lam omega ≤ cap/(1+cap) := by
  have h1 : 0 < 1+lam*omega := by positivity
  have h2 : 0 < 1+cap := by linarith
  unfold occupation
  apply (div_le_div_iff₀ h1 h2).2
  nlinarith only [hx]

theorem tail_P_bounds {r : AnalyticRow} {lam omega rho rhoLo pHi gammaHi : ℝ}
    (hl : 0 < lam) (hw : 0 < omega) (hr0 : 0 ≤ rho)
    (hr : rhoLo ≤ rho) (hpHi : occupation lam omega ≤ pHi)
    (hpOne : 0 ≤ 1-pHi) (hp23 : occupation lam omega ≤ 2/3)
    (hg : gamma r lam ≤ gammaHi) :
    rhoLo*(1-pHi) ≤ tailP r lam omega rho ∧ tailP r lam omega rho ≤ gammaHi+rho := by
  have hp := (occupation_bounds hl hw).1.le
  have hT := cubicEnvelope_ge_fifty_over_eighty_one hp hp23
  have he0 : 0 ≤ eCoeff r lam omega :=
    mul_nonneg (gamma_pos hl).le (tail_cubic_positive_gate.le.trans hT)
  have he1 : eCoeff r lam omega ≤ gamma r lam := by
    exact (mul_le_mul_of_nonneg_left (cubicEnvelope_le_one hp) (gamma_pos hl).le).trans_eq
      (mul_one _)
  have hd : 1-pHi ≤ dCoeff lam omega := by
    exact sub_le_sub_left hpHi 1
  have hm := mul_le_mul hr hd hpOne hr0
  have hu : dCoeff lam omega*rho ≤ rho := by
    simpa only [dCoeff,one_mul] using
      (mul_le_mul_of_nonneg_right (sub_le_self (1 : ℝ) hp) hr0)
  constructor
  · dsimp [tailP]
    nlinarith only [he0,hm]
  · dsimp [tailP]
    linarith only [he1,hg,hu]

theorem tail_eta_product {r : AnalyticRow} {lam omega : ℝ}
    (hl : 0 < lam) (hw : 0 < omega) (hY : logMass omega ≠ 0) :
    tailEta r lam omega*(omega*logMass omega) = kappa r*(1+lam*omega) := by
  unfold tailEta rCoeff gamma
  rw [rate_identity _ _ _ hl.ne' hw.ne' (by positivity)]
  field_simp [hw.ne',hY] <;> ring

theorem tail_eta_lower {r : AnalyticRow} {lam omega cap : ℝ}
    (hl : 0 < lam) (hw : 0 < omega) (hY : 0 < logMass omega)
    (hc : 0 < cap) (hprod : omega*logMass omega < cap) :
    kappa r/cap < tailEta r lam omega := by
  have hk := (row_constants_pos r).2.2.2
  have he : 0 < tailEta r lam omega := div_pos (rCoeff_pos hl hw) hY
  have hid := tail_eta_product (r := r) hl hw hY.ne'
  have hp : kappa r < tailEta r lam omega*(omega*logMass omega) := by
    have h := mul_pos hk (mul_pos hl hw)
    nlinarith only [hid,h]
  have hm := mul_lt_mul_of_pos_left hprod he
  exact (div_lt_iff₀ hc).2 (by nlinarith only [hp,hm])

theorem tail_BC_row_data {r : AnalyticRow} {lam : ℝ}
    (hr : InRow r lam) (hrow : r = .B ∨ r = .C) :
    lam ≤ 4/5 ∧ kappa r = 8/25 ∧ alpha r = 37/40 ∧ beta r = 43/40 ∧
      centerResponse r = 1 ∧ tailH r = 3/4 := by
  rcases hrow with rfl | rfl
  · refine ⟨hr.2.trans tail_B_row_upper_gate,?_,?_,?_,?_,?_⟩ <;>
      norm_num [kappa,alpha,beta,centerResponse,tailH]
  · refine ⟨hr.2,?_,?_,?_,?_,?_⟩ <;>
      norm_num [kappa,alpha,beta,centerResponse,tailH]

theorem tail_FG_row_data {r : AnalyticRow} {lam : ℝ}
    (hr : InRow r lam) (hrow : r = .F ∨ r = .G) :
    lam ≤ 7/4 ∧ kappa r = 3/10 ∧ 43/40 ≤ alpha r ∧ 8/7 ≤ beta r ∧
      89/80 ≤ centerResponse r ∧ centerResponse r ≤ 157/140 ∧ tailH r = 5/8 := by
  rcases hrow with rfl | rfl
  · refine ⟨hr.2.trans tail_F_row_upper_gate,rfl,le_rfl,tail_FG_beta_gate,?_,?_,rfl⟩
    · norm_num [centerResponse,alpha,beta]
    · convert tail_FG_center_gate using 1 <;> norm_num [centerResponse,alpha,beta]
  · refine ⟨hr.2,rfl,tail_FG_alpha_gate,le_rfl,?_,?_,rfl⟩
    · convert tail_FG_center_gate using 1 <;> norm_num [centerResponse,alpha,beta]
    · norm_num [centerResponse,alpha,beta]

/-- Every printed BC tail bound, derived from the actual scalar domain. -/
theorem tail_BC_bounds {r : AnalyticRow} {lam omega rho : ℝ}
    (hf : Feasible r lam omega rho) (hrow : r = .B ∨ r = .C) (ht : omega ≤ 1/16) :
    397/500 ≤ tailK r omega rho-tailP r lam omega rho ∧
      169/375 < tailEta r lam omega-tailP r lam omega rho ∧
      |tailP r lam omega rho-centerResponse r| ≤ 89/189 := by
  obtain ⟨hr,hw,_,hrho,hr1⟩ := hf
  have hl := activity_pos hr
  obtain ⟨hlhi,hkap,ha,hb,ht0,hH⟩ := tail_BC_row_data hr hrow
  obtain ⟨hY,hprod⟩ := tail_BC_log_bounds hw ht
  have hr0 : 0 ≤ rho := ((rhoZero_bounds hl hw).1.trans_le hrho).le
  have hrec : (5 : ℝ)/9 ≤ 1/(1+lam) := by
    have h := one_div_le_one_div_of_le (show 0 < 1+lam by linarith)
      (show 1+lam ≤ 1+4/5 by linarith only [hlhi])
    convert h using 1 <;> norm_num
  have hrl : (5 : ℝ)/9 < rho :=
    (hrec.trans_lt (tail_rhoZero_gt_inverse hl hw)).trans_le hrho
  have hp : occupation lam omega ≤ 1/21 := by
    have h45 := tail_fraction_pos (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*5 < 4*1)
    have h116 := tail_fraction_pos (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*16 < 1*1)
    simp only [Nat.cast_one, Nat.cast_ofNat] at h45 h116
    have hx := mul_le_mul hlhi ht hw.le h45.le
    have h := tail_occupation_cap hl hw (mul_nonneg h45.le h116.le) hx
    convert h using 1 <;> norm_num
  have hg : gamma r lam ≤ 32/125 := by
    unfold gamma
    rw [hkap]
    have h := mul_le_mul_of_nonneg_left hlhi
      (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*25 < 8*1)).le
    convert h using 1 <;> norm_num
  have hP := tail_P_bounds hl hw hr0 hrl.le hp
    (show (0 : ℝ) ≤ 1-1/21 by
      have h := tail_fraction_le (by decide +kernel) (by decide +kernel)
        (by decide +kernel : (1 : ℕ)*1 ≤ 1*21)
      linarith only [h])
    (hp.trans tail_BC_p_gate.le) hg
  have hPlo : (100 : ℝ)/189 ≤ tailP r lam omega rho := by
    convert hP.1 using 1 <;> norm_num
  have hPhi : tailP r lam omega rho ≤ (157 : ℝ)/125 := by
    linarith only [hP.2,hr1]
  have hEta : (128 : ℝ)/75 < tailEta r lam omega := by
    have h := tail_eta_lower (r := r) hl hw (show 0 < logMass omega by linarith only [hY])
      (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*16 < 3*1)) hprod
    rw [hkap] at h
    convert h using 1 <;> norm_num
  have hmass : (2 : ℝ) ≤ (3/4)*logMass omega := by linarith only [hY]
  have hm := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (tail_fraction_pos (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*40 < 43*1)).le hr0)
  have hK : 397/500 ≤ tailK r omega rho-tailP r lam omega rho := by
    dsimp [tailK]
    rw [ha,hb,hH]
    nlinarith only [hm,hP.2,hrl.le]
  refine ⟨hK,?_,?_⟩
  · linarith only [hEta,hPhi]
  · rw [ht0]
    apply abs_le.mpr
    constructor
    · linarith only [hPlo]
    · linarith only [hPhi,tail_BC_response_gate]

/-- Every printed FG tail bound, derived from the actual scalar domain. -/
theorem tail_FG_bounds {r : AnalyticRow} {lam omega rho : ℝ}
    (hf : Feasible r lam omega rho) (hrow : r = .F ∨ r = .G) (ht : omega ≤ 1/64) :
    4/5 < tailK r omega rho-tailP r lam omega rho ∧
      329/120 < tailEta r lam omega-tailP r lam omega rho ∧
      |tailP r lam omega rho-centerResponse r| ≤ tailFGResponse := by
  obtain ⟨hr,hw,_,hrho,hr1⟩ := hf
  have hl := activity_pos hr
  obtain ⟨hlhi,hkap,ha,hb,htlo,hthi,hH⟩ := tail_FG_row_data hr hrow
  obtain ⟨hY,hprod⟩ := tail_FG_log_bounds hw ht
  have hr0 : 0 ≤ rho := ((rhoZero_bounds hl hw).1.trans_le hrho).le
  have hrec : (4 : ℝ)/11 ≤ 1/(1+lam) := by
    have h := one_div_le_one_div_of_le (show 0 < 1+lam by linarith)
      (show 1+lam ≤ 1+7/4 by linarith only [hlhi])
    convert h using 1 <;> norm_num
  have hrl : (4 : ℝ)/11 < rho :=
    (hrec.trans_lt (tail_rhoZero_gt_inverse hl hw)).trans_le hrho
  have hp : occupation lam omega ≤ 7/263 := by
    have h74 := tail_fraction_pos (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*4 < 7*1)
    have h164 := tail_fraction_pos (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*64 < 1*1)
    simp only [Nat.cast_one, Nat.cast_ofNat] at h74 h164
    have hx := mul_le_mul hlhi ht hw.le h74.le
    have h := tail_occupation_cap hl hw (mul_nonneg h74.le h164.le) hx
    convert h using 1 <;> norm_num
  have hg : gamma r lam ≤ 21/40 := by
    unfold gamma
    rw [hkap]
    have h := mul_le_mul_of_nonneg_left hlhi
      (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*10 < 3*1)).le
    convert h using 1 <;> norm_num
  have hP := tail_P_bounds hl hw hr0 hrl.le hp
    (show (0 : ℝ) ≤ 1-7/263 by
      have h := tail_fraction_le (by decide +kernel) (by decide +kernel)
        (by decide +kernel : (7 : ℕ)*1 ≤ 1*263)
      linarith only [h])
    (hp.trans tail_FG_p_gate.le) hg
  have hPlo : (1024 : ℝ)/2893 ≤ tailP r lam omega rho := by
    convert hP.1 using 1 <;> norm_num
  have hPhi : tailP r lam omega rho ≤ (61 : ℝ)/40 := by
    linarith only [hP.2,hr1]
  have hEta : (64 : ℝ)/15 < tailEta r lam omega := by
    have h := tail_eta_lower (r := r) hl hw (show 0 < logMass omega by linarith only [hY])
      (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*128 < 9*1)) hprod
    rw [hkap] at h
    convert h using 1 <;> norm_num
  have hmass : (5 : ℝ)/2 ≤ (5/8)*logMass omega := by linarith only [hY]
  have hm := mul_le_mul (mul_le_mul_of_nonneg_right hb hr0) hmass
    (tail_fraction_pos (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*2 < 5*1)).le
    (mul_nonneg (row_constants_pos r).2.2.1.le hr0)
  have halpha := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hr1)
  have hbase : 11/20+(219/280)*rho ≤ tailK r omega rho-tailP r lam omega rho := by
    dsimp [tailK]
    rw [hH]
    nlinarith only [hm,halpha,hP.2]
  have hlinear : 11/20+(219/280)*(4/11) ≤ 11/20+(219/280)*rho := by
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hrl.le (tail_fraction_pos (by decide +kernel)
        (by decide +kernel : (0 : ℕ)*280 < 219*1)).le)
  refine ⟨tail_FG_K_gate.trans_le (hlinear.trans hbase),?_,?_⟩
  · linarith only [hEta,hPhi]
  · apply abs_le.mpr
    unfold tailFGResponse
    constructor
    · linarith only [hPlo,hthi]
    · have hgap := tail_FG_response_gate
      unfold tailFGResponse at hgap
      linarith only [hPhi,htlo,hgap]

theorem tail_BC_scalar {r : AnalyticRow} {lam omega rho : ℝ}
    (hf : Feasible r lam omega rho) (hrow : r = .B ∨ r = .C) (ht : omega ≤ 1/16)
    (z : ℝ) : epsilon < tailPsi r lam omega rho z := by
  obtain ⟨hK,hC,hB⟩ := tail_BC_bounds hf hrow ht
  exact tail_epsilon_BC_gate.trans
    (tail_BC_square_minimum hK hC.le hB z)

theorem tail_FG_scalar {r : AnalyticRow} {lam omega rho : ℝ}
    (hf : Feasible r lam omega rho) (hrow : r = .F ∨ r = .G) (ht : omega ≤ 1/64)
    (z : ℝ) : epsilon < tailPsi r lam omega rho z := by
  obtain ⟨hK,hC,hB⟩ := tail_FG_bounds hf hrow ht
  exact tail_epsilon_FG_gate.trans
    (tail_FG_square_minimum hK.le hC.le hB z)

/-- Actual scalar tail conclusion, for every real response and every literal row. -/
theorem tail_scalar {r : AnalyticRow} {lam omega rho : ℝ}
    (hf : Feasible r lam omega rho) (ht : omega ≤ tailCutoff r) (z : ℝ) :
    epsilon < tailPsi r lam omega rho z := by
  cases r with
  | B => exact tail_BC_scalar hf (Or.inl rfl) ht z
  | C => exact tail_BC_scalar hf (Or.inr rfl) ht z
  | F => exact tail_FG_scalar hf (Or.inl rfl) ht z
  | G => exact tail_FG_scalar hf (Or.inr rfl) ht z

/-- The scalar is the original Lemma 5.11 expression, with f0=0 and printed H0,T0. -/
theorem tailPsi_eq_oneVertexPsi (r : AnalyticRow) (lam omega rho z : ℝ) :
    tailPsi r lam omega rho z =
      Erdos993Lean.Analytic.V213.VarianceResponse.oneVertexPsi
        (price r lam) (alpha r) (beta r) (gamma r lam)
        (occupation lam omega) rho (logMass omega) z 0 (tailH r)
        (cubicEnvelope (occupation lam omega)) := by
  unfold tailPsi tailK tailP tailEta eCoeff dCoeff rCoeff centerResponse
    Erdos993Lean.Analytic.V213.VarianceResponse.oneVertexPsi
  simp only [mul_zero,add_zero,div_div]
  ring

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.tailCutoff
#print axioms Erdos993Lean.BCFG.Analytic.tailCutoff
#check Erdos993Lean.BCFG.Analytic.tailH
#print axioms Erdos993Lean.BCFG.Analytic.tailH
#check Erdos993Lean.BCFG.Analytic.tailP
#print axioms Erdos993Lean.BCFG.Analytic.tailP
#check Erdos993Lean.BCFG.Analytic.tailK
#print axioms Erdos993Lean.BCFG.Analytic.tailK
#check Erdos993Lean.BCFG.Analytic.tailEta
#print axioms Erdos993Lean.BCFG.Analytic.tailEta
#check Erdos993Lean.BCFG.Analytic.tailPsi
#print axioms Erdos993Lean.BCFG.Analytic.tailPsi
#check Erdos993Lean.BCFG.Analytic.tail_rhoZero_gt_inverse
#print axioms Erdos993Lean.BCFG.Analytic.tail_rhoZero_gt_inverse
#check Erdos993Lean.BCFG.Analytic.tail_occupation_cap
#print axioms Erdos993Lean.BCFG.Analytic.tail_occupation_cap
#check Erdos993Lean.BCFG.Analytic.tail_P_bounds
#print axioms Erdos993Lean.BCFG.Analytic.tail_P_bounds
#check Erdos993Lean.BCFG.Analytic.tail_eta_product
#print axioms Erdos993Lean.BCFG.Analytic.tail_eta_product
#check Erdos993Lean.BCFG.Analytic.tail_eta_lower
#print axioms Erdos993Lean.BCFG.Analytic.tail_eta_lower
#check Erdos993Lean.BCFG.Analytic.tail_BC_row_data
#print axioms Erdos993Lean.BCFG.Analytic.tail_BC_row_data
#check Erdos993Lean.BCFG.Analytic.tail_FG_row_data
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_row_data
#check Erdos993Lean.BCFG.Analytic.tail_BC_bounds
#print axioms Erdos993Lean.BCFG.Analytic.tail_BC_bounds
#check Erdos993Lean.BCFG.Analytic.tail_FG_bounds
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_bounds
#check Erdos993Lean.BCFG.Analytic.tail_BC_scalar
#print axioms Erdos993Lean.BCFG.Analytic.tail_BC_scalar
#check Erdos993Lean.BCFG.Analytic.tail_FG_scalar
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_scalar
#check Erdos993Lean.BCFG.Analytic.tail_scalar
#print axioms Erdos993Lean.BCFG.Analytic.tail_scalar
#check Erdos993Lean.BCFG.Analytic.tailPsi_eq_oneVertexPsi
#print axioms Erdos993Lean.BCFG.Analytic.tailPsi_eq_oneVertexPsi
