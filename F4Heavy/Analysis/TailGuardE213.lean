module

public import F4Heavy.Analysis.TailRayE213
public import F4Heavy.Analysis.TailGuardE202
public import F4Heavy.Analysis.TailGuardE208
public import F4Heavy.Analysis.TailDomain

public import F4Heavy.Analysis.TailFinalPolynomialForms

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def tail_guard_E2_13_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.mul (.mul (.mul reflectTailE2Delta (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 3)) (.add (.mul (.mul (.mul (.add reflectTailE2Gamma (.mul (.const ⟨(-1), 1⟩) reflectTailE2Delta)) reflectTailE2Scale) (.add (.const ⟨(1), 1⟩) .parent)) (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) (.pow .parent 2)) (.add (.mul (.add (.const ⟨(1), 1⟩) (.mul reflectTailE2Gamma (.const ⟨(1), 2⟩))) (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.mul (.mul reflectTailE2Gamma .parent) (.const ⟨(1), 6⟩))))))) (.add (.const ⟨(29), 1⟩) (.mul (.const ⟨(10), 1⟩) .parent))) (.mul (.add (.add (.mul (.mul (.add reflectTailE2Gamma (.mul (.const ⟨(-1), 1⟩) reflectTailE2Delta)) (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 3)) (.add (.mul (.mul (.mul (.add reflectTailE2Gamma (.mul (.const ⟨(-1), 1⟩) reflectTailE2Delta)) reflectTailE2Scale) (.add (.const ⟨(1), 1⟩) .parent)) (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) (.pow .parent 2)) (.add (.mul (.add (.const ⟨(1), 1⟩) (.mul reflectTailE2Gamma (.const ⟨(1), 2⟩))) (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.mul (.mul reflectTailE2Gamma .parent) (.const ⟨(1), 6⟩))))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul .parent reflectTailE2Hi) (.add (.add (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2) (.mul (.const ⟨(-1), 1⟩) (.mul .parent (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)))) (.mul reflectTailE2Gamma (.add (.add (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul .parent (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.const ⟨(1), 2⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .parent 2) (.const ⟨(1), 12⟩))))))) (.add (.mul (.mul (.mul (.add reflectTailE2Gamma (.mul (.const ⟨(-1), 1⟩) reflectTailE2Delta)) reflectTailE2Scale) (.add (.const ⟨(1), 1⟩) .parent)) (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) (.pow .parent 2)) (.add (.mul (.add (.const ⟨(1), 1⟩) (.mul reflectTailE2Gamma (.const ⟨(1), 2⟩))) (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.mul (.mul reflectTailE2Gamma .parent) (.const ⟨(1), 6⟩))))))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.pow reflectTailExtraE2Eta 2) (.const ⟨(1), 2⟩)) (.pow .parent 2)) (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 4)))) (.mul (.const ⟨(10), 1⟩) .parent))) (.row tail_ray_E2_13_denominator_power))

def tail_guard_E2_13_identity_right_expression : PolynomialExpr :=
  (.mul (.row tail_ray_E2_13_numerator_power) (.mul (.mul (.mul .parent (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)) (.add (.mul (.mul (.mul (.add reflectTailE2Gamma (.mul (.const ⟨(-1), 1⟩) reflectTailE2Delta)) reflectTailE2Scale) (.add (.const ⟨(1), 1⟩) .parent)) (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) (.pow .parent 2)) (.add (.mul (.add (.const ⟨(1), 1⟩) (.mul reflectTailE2Gamma (.const ⟨(1), 2⟩))) (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.mul (.mul reflectTailE2Gamma .parent) (.const ⟨(1), 6⟩))))))) (.add (.const ⟨(29), 1⟩) (.mul (.const ⟨(10), 1⟩) .parent))))

set_option maxRecDepth 4096 in
theorem tail_guard_E2_13_identity_coefficients_check : PolynomialExpr.check tail_guard_E2_13_identity_left_expression tail_guard_E2_13_identity_right_expression = true := by
  decide +kernel

theorem tail_guard_E2_13_identity (lam : ℝ) (hr : InRow .E2 lam) :
    tailGuard .E2 lam 13 = realHorner (tail_ray_E2_13_numerator_power.map fractionValue) lam /
      realHorner (tail_ray_E2_13_denominator_power.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ tail_guard_E2_13_identity_coefficients_check 0 lam
  simp only [tail_guard_E2_13_identity_left_expression, tail_guard_E2_13_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailE2Delta_value, reflectTailE2Gamma_value, reflectTailE2Hi_value, reflectTailE2Scale_value, reflectTailExtraE2Eta_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hl := inRow_activity_pos .E2 lam hr
  have hd := ne_of_gt (tail_ray_E2_13_denominator_positive lam hr)
  have hT : 0 < tailTauLo .E2 lam := by
    have h := tail_guard_E2_02_positive lam hr
    change 0 < tailTauLo .E2 lam - 3 / 2 at h
    linarith only [h]
  have hL : 0 < tailLStar .E2 lam := tail_guard_E2_08_positive lam hr
  have hN := tail_LNumerator_positive .E2 lam hl hL
  have hs := tail_scale_positive .E2
  have hden : tailFinalDD .E2 lam*(29+10*lam) ≠ 0 := by
    simp only [tailFinalDD,tailFinalTD,tailProbabilityDen]
    positivity
  have hq : tailGuard .E2 lam 13 = (tailFinalGN .E2 lam (10*lam) (29+10*lam))/(tailFinalDD .E2 lam*(29+10*lam)) := by
    simp only [tailGuard,tailChildC]
    exact tail_final_G_quotient .E2 lam (10*lam) (29+10*lam) hl hL (by positivity)
  rw [hq]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [tailFinalGN,tailFinalTN,tailFinalTD,tailFinalAN,tailFinalAD,
    tailFinalCN,tailFinalDN,tailFinalDD,tailProbabilityDen,tailP1Numerator,
    tailANumerator,tailLNumerator,sub_eq_add_neg,neg_mul,one_mul,mul_one,one_pow,
    div_eq_mul_inv,mul_assoc] using hp


theorem tail_guard_E2_13_positive (lam : ℝ) (hr : InRow .E2 lam) : 0 < tailGuard .E2 lam 13 := by
  rw [tail_guard_E2_13_identity lam hr]
  exact div_pos (tail_ray_E2_13_numerator_positive lam hr) (tail_ray_E2_13_denominator_positive lam hr)

end F4Heavy.Analysis
