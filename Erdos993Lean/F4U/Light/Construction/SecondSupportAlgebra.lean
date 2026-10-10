module

public import Erdos993Lean.F4U.Light.Construction.CoefficientSigns
public import Erdos993Lean.F4U.Light.Construction.GuardConstruction

/-!
Exact identities connecting literal light guards to the full second-support
response window. Parent/source/row fields remain fixed and explicit. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 def responseR (r : Row) (lam H rho z h : ℝ) : ℝ :=
  responseC r lam H rho+2*responseD r lam H rho z*h

 def responseG (r : Row) (lam H rho z h : ℝ) : ℝ :=
  delta r lam+responseD r lam H rho z*supportLine r .second lam h

 def responseSlack (r : Row) (lam H rho z h : ℝ) : ℝ :=
  10*responseG r lam H rho z h-responseR r lam H rho z h

 theorem responseR_at_zPlus (r : Row) (lam H rho h : ℝ) :
    responseR r lam H rho (zPlus H) h = RGuard r lam H h rho := by
  unfold responseR responseC responseD RGuard
  ring

 theorem responseSlack_at_hi_zPlus (r : Row) (lam H h : ℝ) :
    responseSlack r lam H 1 (zPlus H) h = SGuard r lam H h := by
  simp only [responseSlack, responseG, responseR, responseC, responseD,
    supportLine, slope, SGuard]
  ring

 theorem responseR_z_difference (r : Row) (lam H rho z h : ℝ) :
    responseR r lam H rho z h-responseR r lam H rho (zPlus H) h =
      2*pH lam H*(zPlus H-z)*parentPPlus r lam H rho*h := by
  unfold responseR responseC responseD
  ring

 theorem responseSlack_z_difference (r : Row) (lam H rho z h : ℝ) :
    responseSlack r lam H rho z h-responseSlack r lam H rho (zPlus H) h =
      pH lam H*(zPlus H-z)*parentPPlus r lam H rho*(h+10*intercept r .second lam) := by
  simp only [responseSlack, responseG, responseR, responseC, responseD, supportLine, slope]
  ring

 theorem responseSlack_rho_difference (r : Row) (lam H rho h : ℝ) :
    responseSlack r lam H rho (zPlus H) h-responseSlack r lam H 1 (zPlus H) h =
      pH lam H*(1-rho)*(1-pH lam H)*
        (2+zPlus H*(h+10*intercept r .second lam)) := by
  simp only [responseSlack, responseG, responseR, responseC, responseD,
    supportLine, slope, parentPPlus]
  ring

 theorem RGuard_rho_difference (r : Row) (lam H rho e h : ℝ) :
    RGuard r lam H h rho-RGuard r lam H h e =
      2*pH lam H*(rho-e)*(1-pH lam H)*(1-zPlus H*h) := by
  unfold RGuard parentPPlus
  ring

 theorem RGuard_h_interpolation (r : Row) (lam H e h0 h1 t : ℝ) :
    RGuard r lam H ((1-t)*h0+t*h1) e =
      (1-t)*RGuard r lam H h0 e+t*RGuard r lam H h1 e := by
  unfold RGuard
  ring

 theorem RGuard_rho_interpolation (r : Row) (lam H h e0 e1 t : ℝ) :
    RGuard r lam H h ((1-t)*e0+t*e1) =
      (1-t)*RGuard r lam H h e0+t*RGuard r lam H h e1 := by
  unfold RGuard parentPPlus
  ring

 theorem SGuard_h_interpolation (r : Row) (lam H h0 h1 t : ℝ) :
    SGuard r lam H ((1-t)*h0+t*h1) =
      (1-t)*SGuard r lam H h0+t*SGuard r lam H h1 := by
  unfold SGuard
  ring

 theorem response_denominator_interpolation (delta d L Lcross : ℝ)
    (hcross : Lcross ≠ 0) :
    delta+d*L=(1-L/Lcross)*delta+(L/Lcross)*(delta+d*Lcross) := by
  field_simp [hcross]
  <;> ring

 theorem firstSupport_denominator_pos (delta d L Lcross : ℝ)
    (hd : 0 < delta) (hL0 : 0 ≤ L) (hL1 : L ≤ Lcross)
    (hcross : 0 < Lcross) (hGcross : 0 < delta+d*Lcross) :
    0 < delta+d*L := by
  by_cases hd0 : 0 ≤ d
  · exact add_pos_of_pos_of_nonneg hd (mul_nonneg hd0 hL0)
  · have hh := mul_le_mul_of_nonpos_left hL1 (le_of_not_ge hd0)
    linarith

#print axioms responseR
#print axioms responseG
#print axioms responseSlack
#print axioms responseR_at_zPlus
#print axioms responseSlack_at_hi_zPlus
#print axioms responseR_z_difference
#print axioms responseSlack_z_difference
#print axioms responseSlack_rho_difference
#print axioms RGuard_rho_difference
#print axioms RGuard_h_interpolation
#print axioms RGuard_rho_interpolation
#print axioms SGuard_h_interpolation
#print axioms response_denominator_interpolation
#print axioms firstSupport_denominator_pos

end
end F4Unified.LightConstruction
