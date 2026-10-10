module

public import F4Heavy.Analysis.TailRayD04
public import F4Heavy.Analysis.TailDomain

public import F4Heavy.Analysis.TailIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def tail_guard_D_04_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.mul (.add reflectTailDGamma (.mul (.const ⟨(-1), 1⟩) reflectTailDDelta)) (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul reflectTailDGamma .parent) reflectTailDHi))) (.row tail_ray_D_04_denominator_power))

def tail_guard_D_04_identity_right_expression : PolynomialExpr :=
  (.mul (.row tail_ray_D_04_numerator_power) (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent))

set_option maxRecDepth 4096 in
theorem tail_guard_D_04_identity_coefficients_check : PolynomialExpr.check tail_guard_D_04_identity_left_expression tail_guard_D_04_identity_right_expression = true := by
  decide +kernel

theorem tail_guard_D_04_identity (lam : ℝ) (hr : InRow .D lam) :
    tailGuard .D lam 4 = realHorner (tail_ray_D_04_numerator_power.map fractionValue) lam /
      realHorner (tail_ray_D_04_denominator_power.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ tail_guard_D_04_identity_coefficients_check 0 lam
  simp only [tail_guard_D_04_identity_left_expression, tail_guard_D_04_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailDDelta_value, reflectTailDGamma_value, reflectTailDHi_value, reflectTailDScale_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hd := ne_of_gt (tail_ray_D_04_denominator_positive lam hr)
  have hl := inRow_activity_pos .D lam hr
  have hs := tail_scale_positive .D
  have hden : (tailScale .D*(1+lam)+lam) ≠ 0 := by positivity
  have hq : tailGuard .D lam 4 = ((gamma .D lam-delta .D lam)*(tailScale .D*(1+lam)+lam)-gamma .D lam*lam*tailTauHi .D lam)/(tailScale .D*(1+lam)+lam) := by
    simp only [tailGuard, tailD0, tailPStar]
    field_simp [hden]
    <;> ring
  rw [hq]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [sub_eq_add_neg, neg_mul] using hp


theorem tail_guard_D_04_positive (lam : ℝ) (hr : InRow .D lam) : 0 < tailGuard .D lam 4 := by
  rw [tail_guard_D_04_identity lam hr]
  exact div_pos (tail_ray_D_04_numerator_positive lam hr) (tail_ray_D_04_denominator_positive lam hr)

end F4Heavy.Analysis
