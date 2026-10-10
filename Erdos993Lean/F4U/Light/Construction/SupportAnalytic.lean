module

public import Erdos993Lean.F4U.Light.Construction.ChildBounds
public import Erdos993Lean.F4U.Light.Construction.SupportDefinitions
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Literal support derivatives and analytic bounds.
-/

@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

theorem support_phi_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 0 < phi u := by
  simp only [phi, ite_eq_right hu0.ne']
  exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

theorem support_childH_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 0 < childH u := by
  simp only [childH, ite_eq_right hu0.ne']
  exact div_pos hu0 (support_phi_pos hu0 hu1)

theorem support_phi_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    phi u < u/(1-u) := by
  have h1 : 0 < 1-u := by linarith
  have hi : 0 < (1-u)⁻¹ := inv_pos.mpr h1
  have hne : (1-u)⁻¹ ≠ 1 := by
    intro he
    have he' := (inv_eq_one.mp he)
    linarith
  have hl := Real.log_lt_sub_one_of_pos hi hne
  simp only [Real.log_inv] at hl
  have he : (1-u)⁻¹-1 = u/(1-u) := by field_simp [h1.ne'] <;> ring
  simpa only [phi, ite_eq_right hu0.ne', he] using hl

theorem support_w_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 0 < supportW u := by
  have hp := support_phi_pos hu0 hu1
  have h1 : 0 < 1-u := by linarith
  have hl := (lt_div_iff₀ h1).mp (support_phi_upper hu0 hu1)
  have hh : 1-u < childH u := by
    simp only [childH, ite_eq_right hu0.ne']
    rw [lt_div_iff₀ hp]
    nlinarith
  unfold supportW
  linarith

theorem support_w_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    supportW u ≤ u/2-u^2/12 := by
  have hh := childH_le_parentHBound hu0 hu1
  unfold parentHBound at hh
  unfold supportW
  linarith

theorem support_w_upper_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    supportW u ≤ u/2 := by
  have hh := support_w_upper hu0 hu1
  nlinarith [sq_nonneg u]

theorem support_A_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 0 < supportA u := by
  have hd := zMinus_den_pos hu1
  have hl := zMinus_le_parentLog hu0.le hu1
  have he : 2*(1-u)^2*zMinus u+3*u^2-2*u =
      u^3*(4-3*u)/(u^2-6*u+6) := by
    unfold zMinus
    generalize hDeq : u^2-6*u+6 = D at hd ⊢
    field_simp [hd.ne']
    rw [← hDeq]
    ring
  have hp : 0 < u^3*(4-3*u)/(u^2-6*u+6) := by
    have ht : 0 < 4-3*u := by linarith
    positivity
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2*(1-u)^2)
  simp only [phi, ite_eq_right hu0.ne', supportA]
  linarith

/-- Corrected shared-E logarithm estimate; the manuscript's stronger -1/8
claim on the extended E interval is false. -/
theorem log_16_13_lt_quarter : Real.log ((16 : ℝ)/13) < 1/4 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : 0 < (16 : ℝ)/13)
    (by norm_num : (16 : ℝ)/13 ≠ 1)
  norm_num at h ⊢
  linarith

theorem log_13_16_gt_neg_quarter : -(1/4 : ℝ) < Real.log (13/16) := by
  have h := log_16_13_lt_quarter
  rw [show (13 : ℝ)/16 = ((16 : ℝ)/13)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem log_13_8_lt_half : Real.log ((13 : ℝ)/8) < 1/2 := by
  have h := parentLog_le_zPlus (H := (5 : ℝ)/13) (by norm_num) (by norm_num)
  have he : -Real.log (1-(5 : ℝ)/13) = Real.log ((13 : ℝ)/8) := by
    rw [show 1-(5 : ℝ)/13 = ((13 : ℝ)/8)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [he] at h
  norm_num [zPlus] at h
  linarith

theorem log_4_3_lt_third : Real.log ((4 : ℝ)/3) < 1/3 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : 0 < (4 : ℝ)/3)
    (by norm_num : (4 : ℝ)/3 ≠ 1)
  norm_num at h ⊢
  exact h

theorem childH_support_hasDerivAt {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt childH (-supportW u/((1-u)*phi u)) u := by
  have hp := support_phi_pos hu0 hu1
  have hp' : -Real.log (1-u) ≠ 0 := by simpa only [phi, ite_eq_right hu0.ne'] using hp.ne'
  have hd := (hasDerivAt_id u).div (parentLog_hasDerivAt hu1) hp'
  have h1 : 1-u ≠ 0 := by linarith
  have he : (1*(-Real.log (1-u))-u*(1/(1-u)))/(-Real.log (1-u))^2 =
      -supportW u/((1-u)*phi u) := by
    simp only [supportW, childH, phi, ite_eq_right hu0.ne']
    generalize hpeq : -Real.log (1-u) = P at hp' ⊢
    field_simp [h1, hp'] <;> ring
  dsimp only [id_eq, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply] at hd
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hu0.ne'] with v hv
  simp only [childH, phi, ite_eq_right hv]
  rfl


theorem support_log_hasDerivAt {lam u : ℝ} (hlam : 0 < lam)
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun v : ℝ => Real.log (lam*(1-v)/v)) (-1/(u*(1-u))) u := by
  have hid := hasDerivAt_id u
  have ha := ((hasDerivAt_const u lam).mul ((hasDerivAt_const u (1 : ℝ)).sub hid)).div hid hu0.ne'
  have hn : lam*(1-u)/u ≠ 0 := by positivity
  have hd := ha.log hn
  convert hd using 1
  · rfl
  · dsimp
    have h1 : 1-u ≠ 0 := by linarith
    field_simp [hlam.ne', hu0.ne', h1] <;> ring

theorem childJ_support_hasDerivAt {lam u : ℝ} (hlam : 0 < lam)
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (childJ lam) ((-supportW u/((1-u)*phi u))*supportDerivative lam u) u := by
  have hh := childH_support_hasDerivAt hu0 hu1
  have ht := support_log_hasDerivAt hlam hu0 hu1
  have hd := ((hasDerivAt_id u).mul hh).mul ht
  have hp := support_phi_pos hu0 hu1
  have hw := support_w_pos hu0 hu1
  have h1 : 1-u ≠ 0 := by linarith
  have he : (1*childH u+u*(-supportW u/((1-u)*phi u)))*Real.log (lam*(1-u)/u)+
      (u*childH u)*(-1/(u*(1-u))) =
      (-supportW u/((1-u)*phi u))*supportDerivative lam u := by
    unfold supportDerivative supportW
    simp only [childH, phi, ite_eq_right hu0.ne']
    have hp' : -Real.log (1-u) ≠ 0 := by simpa only [phi, ite_eq_right hu0.ne'] using hp.ne'
    have hw' : u/(-Real.log (1-u))-1+u ≠ 0 := by
      simpa only [supportW, childH, phi, ite_eq_right hu0.ne'] using hw.ne'
    generalize hpeq : -Real.log (1-u) = P at hp' hw' ⊢
    have hD : -P+P*u+u ≠ 0 := by
      intro hz
      apply hw'
      have he : u/P-1+u=(-P+P*u+u)/P := by field_simp [hp'] <;> ring
      rw [he, hz]
      simp
    field_simp [h1, hu0.ne', hp', hw']
    ring_nf
    generalize hDeq : -P+P*u+u = D at hD ⊢
    field_simp [hD]
    rw [← hDeq]
    ring
  dsimp only [id_eq, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply] at hd
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hu0.ne'] with v hv
  simp only [childJ, ite_eq_right hv]
  rfl

theorem supportDerivative_hasDerivAt {lam u : ℝ} (hlam : 0 < lam)
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (supportDerivative lam)
      ((-supportW u/((1-u)*phi u))*supportSecond lam u) u := by
  have hid := hasDerivAt_id u
  have hh := childH_support_hasDerivAt hu0 hu1
  have ht := support_log_hasDerivAt hlam hu0 hu1
  have hshift := hh.sub (((hasDerivAt_const u (1 : ℝ)).sub hid).const_mul 2)
  have hnum := hid.mul ((hshift.mul ht).const_add 1)
  have hden := (hh.sub_const 1).add hid
  have hw := support_w_pos hu0 hu1
  have hd := hnum.div hden hw.ne'
  have hp := support_phi_pos hu0 hu1
  have h1 : 1-u ≠ 0 := by linarith
  convert hd using 1
  · rfl
  · dsimp only [id_eq, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
    simp only [supportSecond, supportA, supportB, supportW, supportDerivative,
      childH, phi, ite_eq_right hu0.ne']
    have hp' : -Real.log (1-u) ≠ 0 := by simpa only [phi, ite_eq_right hu0.ne'] using hp.ne'
    have hw' : u/(-Real.log (1-u))-1+u ≠ 0 := by
      simpa only [supportW, childH, phi, ite_eq_right hu0.ne'] using hw.ne'
    generalize hpeq : -Real.log (1-u) = P at hp' hw' ⊢
    have hD : -P+P*u+u ≠ 0 := by
      intro hz
      apply hw'
      have he : u/P-1+u=(-P+P*u+u)/P := by field_simp [hp'] <;> ring
      rw [he, hz]
      simp
    field_simp [h1, hu0.ne', hp', hw']
    ring_nf <;> field_simp [hD] <;> ring

end
end F4Unified.LightConstruction
