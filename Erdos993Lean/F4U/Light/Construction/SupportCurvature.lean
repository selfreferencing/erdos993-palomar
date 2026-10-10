module
public import Erdos993Lean.F4U.Light.Construction.SupportAnalytic

/-! Curvature of the actual endpoint child curves. The shared-E estimate uses
T>-1/4 together with the quadratic childH upper bound, repairing the false
T>-1/8 intermediate estimate on the extended interval. -/
@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

/-- Extended endpoint domain from the manuscript's support table. -/
def supportUpper : Row → ℝ
  | .D => 13/23
  | .E1 | .E2 => 8/13
  | .H => 7/10

def supportLogConstant : Row → ℝ
  | .D => 1/2
  | .E1 | .E2 => 1/4
  | .H => 1/3

def supportCoarseLower (k u : ℝ) : ℝ :=
  4*(2*k*u^3-10*k*u^2+8*k*u-2*u^2+9*u-6)/(3*u*(u-2))

theorem support_log_lower {r : Row} {lam u : ℝ}
    (hlam : (rowData r).lo ≤ lam) (hu0 : 0 < u) (huhi : u ≤ supportUpper r) :
    -supportLogConstant r < Real.log (lam*(1-u)/u) := by
  cases r
  · simp only [rowData] at hlam
    simp only [supportUpper, supportLogConstant] at huhi ⊢
    have h1 : 0 < 1-u := by linarith
    have ha : 0 < lam*(1-u)/u := by positivity
    have hm : (8 : ℝ)/13 ≤ lam*(1-u)/u := by
      rw [le_div_iff₀ hu0]
      nlinarith [mul_nonneg (by linarith : 0 ≤ lam-4/5) h1.le]
    have hl := (Real.log_le_log_iff (by norm_num : 0 < (8 : ℝ)/13) ha).mpr hm
    have hb := log_13_8_lt_half
    rw [show (8 : ℝ)/13 = ((13 : ℝ)/8)⁻¹ by norm_num, Real.log_inv] at hl
    linarith
  · simp only [rowData] at hlam
    simp only [supportUpper, supportLogConstant] at huhi ⊢
    have h1 : 0 < 1-u := by linarith
    have ha : 0 < lam*(1-u)/u := by positivity
    have hm : (13 : ℝ)/16 ≤ lam*(1-u)/u := by
      rw [le_div_iff₀ hu0]
      nlinarith [mul_nonneg (by linarith : 0 ≤ lam-13/10) h1.le]
    have hl := (Real.log_le_log_iff (by norm_num : 0 < (13 : ℝ)/16) ha).mpr hm
    linarith [log_13_16_gt_neg_quarter]
  · simp only [rowData] at hlam
    simp only [supportUpper, supportLogConstant] at huhi ⊢
    have h1 : 0 < 1-u := by linarith
    have ha : 0 < lam*(1-u)/u := by positivity
    have hm : (13 : ℝ)/16 ≤ lam*(1-u)/u := by
      rw [le_div_iff₀ hu0]
      nlinarith [mul_nonneg (by linarith : 0 ≤ lam-13/10) h1.le]
    have hl := (Real.log_le_log_iff (by norm_num : 0 < (13 : ℝ)/16) ha).mpr hm
    linarith [log_13_16_gt_neg_quarter]
  · simp only [rowData] at hlam
    simp only [supportUpper, supportLogConstant] at huhi ⊢
    have h1 : 0 < 1-u := by linarith
    have ha : 0 < lam*(1-u)/u := by positivity
    have hm : (3 : ℝ)/4 ≤ lam*(1-u)/u := by
      rw [le_div_iff₀ hu0]
      nlinarith [mul_nonneg (by linarith : 0 ≤ lam-7/4) h1.le]
    have hl := (Real.log_le_log_iff (by norm_num : 0 < (3 : ℝ)/4) ha).mpr hm
    rw [show (3 : ℝ)/4 = ((4 : ℝ)/3)⁻¹ by norm_num, Real.log_inv] at hl
    linarith [log_4_3_lt_third]

theorem support_numerator_lower {lam u k : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hk0 : 0 ≤ k) (hT : -k ≤ Real.log (lam*(1-u)/u)) :
    supportCoarseLower k u*u^3/8 ≤
      (1-u)*(supportA u*Real.log (lam*(1-u)/u)+supportB u) := by
  have hA := support_A_pos hu0 hu1
  have hphi := parentLog_le_zPlus hu0.le hu1
  have hphi' : phi u ≤ zPlus u := by
    simpa only [phi, ite_eq_right hu0.ne'] using hphi
  let C := -2*k*(1-u)^2-(3-2*u)
  have hC : C ≤ 0 := by
    dsimp [C]
    have hm : 0 ≤ 2*k*(1-u)^2 := by positivity
    nlinarith
  have ht := mul_le_mul_of_nonneg_left hT hA.le
  have hp := mul_le_mul_of_nonpos_left hphi' hC
  have h1 : 0 ≤ 1-u := by linarith
  have hn : (1-u)*(C*zPlus u+3*u+2*k*u-3*k*u^2) ≤
      (1-u)*(supportA u*Real.log (lam*(1-u)/u)+supportB u) := by
    apply mul_le_mul_of_nonneg_left _ h1
    simp only [supportA, supportB] at ht ⊢
    dsimp [C] at hp ⊢
    nlinarith
  have he : (1-u)*(C*zPlus u+3*u+2*k*u-3*k*u^2) = supportCoarseLower k u*u^3/8 := by
    dsimp [C, zPlus, supportCoarseLower]
    have h1n : 1-u ≠ 0 := by linarith
    have h2n : 2-u ≠ 0 := by linarith
    have h2n' : u-2 ≠ 0 := by linarith
    field_simp [hu0.ne', h1n, h2n, h2n'] <;> ring
  rwa [he] at hn

theorem supportCoarse_D_lower {u : ℝ} (hu0 : 0 < u) (huhi : u ≤ 13/23) :
    (348 : ℝ)/299 ≤ supportCoarseLower (1/2) u := by
  have he : supportCoarseLower (1/2) u-348/299 =
      4*(69-13*u)*(13-23*u)/(897*u) := by
    unfold supportCoarseLower
    have h2 : u-2 ≠ 0 := by linarith
    field_simp [hu0.ne', h2] <;> ring
  have hp : 0 ≤ 4*(69-13*u)*(13-23*u)/(897*u) := by
    have h1 : 0 ≤ 69-13*u := by linarith
    have h2 : 0 ≤ 13-23*u := by linarith
    positivity
  linarith

theorem supportCoarse_E_half_lower {u : ℝ} (hu0 : 0 < u) (huhi : u ≤ 1/2) :
    (25 : ℝ)/9 ≤ supportCoarseLower (1/4) u := by
  have he : supportCoarseLower (1/4) u-25/9 =
      (1-2*u)*(3*u^2-38*u+72)/(9*u*(2-u)) := by
    unfold supportCoarseLower
    have h2 : u-2 ≠ 0 := by linarith
    have h2' : 2-u ≠ 0 := by linarith
    field_simp [hu0.ne', h2, h2'] <;> ring
  have hp : 0 ≤ (1-2*u)*(3*u^2-38*u+72)/(9*u*(2-u)) := by
    have h1 : 0 ≤ 1-2*u := by linarith
    have h2 : 0 ≤ 3*u^2-38*u+72 := by nlinarith [sq_nonneg u]
    have h3 : 0 < 2-u := by linarith
    positivity
  linarith

theorem supportCoarse_E_lower {u : ℝ} (hu0 : 0 < u) (huhi : u ≤ 8/13) :
    (899 : ℝ)/702 ≤ supportCoarseLower (1/4) u := by
  have he : supportCoarseLower (1/4) u-899/702 =
      (8-13*u)*(36*u^2-371*u+702)/(702*u*(2-u)) := by
    unfold supportCoarseLower
    have h2 : u-2 ≠ 0 := by linarith
    have h2' : 2-u ≠ 0 := by linarith
    field_simp [hu0.ne', h2, h2'] <;> ring
  have hp : 0 ≤ (8-13*u)*(36*u^2-371*u+702)/(702*u*(2-u)) := by
    have h1 : 0 ≤ 8-13*u := by linarith
    have h2 : 0 ≤ 36*u^2-371*u+702 := by nlinarith [sq_nonneg u]
    have h3 : 0 < 2-u := by linarith
    positivity
  linarith

theorem supportCoarse_H_lower {u : ℝ} (hu0 : 0 < u) (huhi : u ≤ 7/10) :
    (436 : ℝ)/1365 ≤ supportCoarseLower (1/3) u := by
  have he : supportCoarseLower (1/3) u-436/1365 =
      4*(7-10*u)*(91*u^2-697*u+1170)/(4095*u*(2-u)) := by
    unfold supportCoarseLower
    have h2 : u-2 ≠ 0 := by linarith
    have h2' : 2-u ≠ 0 := by linarith
    field_simp [hu0.ne', h2, h2'] <;> ring
  have hp : 0 ≤ 4*(7-10*u)*(91*u^2-697*u+1170)/(4095*u*(2-u)) := by
    have h1 : 0 ≤ 7-10*u := by linarith
    have h2 : 0 ≤ 91*u^2-697*u+1170 := by nlinarith [sq_nonneg u]
    have h3 : 0 < 2-u := by linarith
    positivity
  linarith

/-- Convert the original numerator and w bounds to the actual curvature. -/
theorem supportSecond_bound_of_numerator {lam u K : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hnum : K*(supportW u)^3 <
      (1-u)*(supportA u*Real.log (lam*(1-u)/u)+supportB u)) :
    supportSecond lam u < -K := by
  have hw := support_w_pos hu0 hu1
  unfold supportSecond
  rw [div_lt_iff₀ (pow_pos hw 3)]
  nlinarith


theorem supportSecond_bound_of_coarse {lam u k K a c : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hk0 : 0 ≤ k) (hK : 0 ≤ K) (hT : -k ≤ Real.log (lam*(1-u)/u))
    (hc : c ≤ supportCoarseLower k u) (hw : supportW u ≤ a*u)
    (hmargin : K*a^3 < c/8) : supportSecond lam u < -K := by
  apply supportSecond_bound_of_numerator hu0 hu1
  have hwp := support_w_pos hu0 hu1
  have hcube := pow_le_pow_left₀ hwp.le hw 3
  calc
    K*(supportW u)^3 ≤ K*(a*u)^3 := mul_le_mul_of_nonneg_left hcube hK
    _ < c*u^3/8 := by
      have hm := mul_lt_mul_of_pos_right hmargin (pow_pos hu0 3)
      nlinarith
    _ ≤ supportCoarseLower k u*u^3/8 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (pow_nonneg hu0.le 3)) (by norm_num)
    _ ≤ (1-u)*(supportA u*Real.log (lam*(1-u)/u)+supportB u) :=
      support_numerator_lower hu0 hu1 hk0 hT

/-- Strict endpoint curvature on the original shared extended table domains.
The E rows use the corrected -1/4 logarithm estimate and stronger w bound. -/
theorem endpoint_support_curvature {r : Row} {lam u : ℝ}
    (hlam : (rowData r).lo ≤ lam) (hu0 : 0 < u) (huhi : u ≤ supportUpper r) :
    supportSecond lam u < -curvature r := by
  have hu1 : u < 1 := by cases r <;> simp only [supportUpper] at huhi <;> linarith
  have hT := (support_log_lower hlam hu0 huhi).le
  have hw := support_w_upper_half hu0.le hu1
  cases r
  · simp only [supportLogConstant] at hT
    simp only [supportUpper] at huhi
    simp only [curvature]
    apply supportSecond_bound_of_coarse (k := (1 : ℝ)/2) (a := (1 : ℝ)/2)
      (c := (348 : ℝ)/299) hu0 hu1 (by norm_num) (by norm_num) hT
      (supportCoarse_D_lower hu0 huhi)
    · simpa only [div_eq_mul_inv, mul_comm, one_mul] using hw
    · norm_num
  · simp only [supportLogConstant] at hT
    simp only [supportUpper] at huhi
    simp only [curvature]
    by_cases hh : u ≤ 1/2
    · apply supportSecond_bound_of_coarse (k := (1 : ℝ)/4) (a := (1 : ℝ)/2)
        (c := (25 : ℝ)/9) hu0 hu1 (by norm_num) (by norm_num) hT
        (supportCoarse_E_half_lower hu0 hh)
      · simpa only [div_eq_mul_inv, mul_comm, one_mul] using hw
      · norm_num
    · have hwh := support_w_upper hu0.le hu1
      have hw' : supportW u ≤ ((11 : ℝ)/24)*u := by
        nlinarith [mul_nonneg hu0.le (show 0 ≤ u-1/2 by linarith)]
      exact supportSecond_bound_of_coarse hu0 hu1 (by norm_num) (by norm_num) hT
        (supportCoarse_E_lower hu0 huhi) hw' (by norm_num)
  · simp only [supportLogConstant] at hT
    simp only [supportUpper] at huhi
    simp only [curvature]
    by_cases hh : u ≤ 1/2
    · apply supportSecond_bound_of_coarse (k := (1 : ℝ)/4) (a := (1 : ℝ)/2)
        (c := (25 : ℝ)/9) hu0 hu1 (by norm_num) (by norm_num) hT
        (supportCoarse_E_half_lower hu0 hh)
      · simpa only [div_eq_mul_inv, mul_comm, one_mul] using hw
      · norm_num
    · have hwh := support_w_upper hu0.le hu1
      have hw' : supportW u ≤ ((11 : ℝ)/24)*u := by
        nlinarith [mul_nonneg hu0.le (show 0 ≤ u-1/2 by linarith)]
      exact supportSecond_bound_of_coarse hu0 hu1 (by norm_num) (by norm_num) hT
        (supportCoarse_E_lower hu0 huhi) hw' (by norm_num)
  · simp only [supportLogConstant] at hT
    simp only [supportUpper] at huhi
    simp only [curvature]
    apply supportSecond_bound_of_coarse (k := (1 : ℝ)/3) (a := (1 : ℝ)/2)
      (c := (436 : ℝ)/1365) hu0 hu1 (by norm_num) (by norm_num) hT
      (supportCoarse_H_lower hu0 huhi)
    · simpa only [div_eq_mul_inv, mul_comm, one_mul] using hw
    · norm_num

end
end F4Unified.LightConstruction
