module

public import Erdos993Lean.F4U.Light.Construction.ResponseGeometry
public import Erdos993Lean.F4U.Light.Construction.SecondSupportDerivative
public import Erdos993Lean.F4U.Light.Construction.ScaledSquare

/-! Same-parent response consumers. Exact restoration keeps the original row,
source chord, child support and parent coefficients in every minimum/W object.
No LightCore assembly or global support estimate is assumed here. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 def secondSupportMinimum (r : Row) (phase : SourcePhase) (lam H rho z h : ℝ) : ℝ :=
  supportMinimum (pH lam H*parentNHat r phase lam H rho/z)
    (pH lam H*beta r lam*rho) (responseC r lam H rho) (responseD r lam H rho z)
    (delta r lam) (3/10) (intercept r .second lam) h

 theorem supportMinimum_W_cleared (p N z b c d delta slope intercept h : ℝ)
    (hz : z ≠ 0) (hG : delta+d*(slope*h+intercept) ≠ 0) :
    4*z*(delta+d*(slope*h+intercept))*
      supportMinimum (p*N/z) (p*b) c d delta slope intercept h =
      4*(delta+d*(slope*h+intercept))*(p*N+z*p*b*h)+
        4*delta*z*(c*h+d*h^2)-z*(slope*h+intercept)*c^2 := by
  unfold supportMinimum
  field_simp [hz,hG]
  <;> ring

 theorem secondSupportMinimum_W_identity (r : Row) (phase : SourcePhase)
    (lam H rho z h : ℝ) (hz : z ≠ 0) (hG : responseG r lam H rho z h ≠ 0) :
    4*z*responseG r lam H rho z h*secondSupportMinimum r phase lam H rho z h =
      W r phase lam H rho z h (supportLine r .second lam h) := by
  have hh := supportMinimum_W_cleared (pH lam H) (parentNHat r phase lam H rho) z
    (beta r lam*rho) (responseC r lam H rho) (responseD r lam H rho z)
    (delta r lam) (3/10) (intercept r .second lam) h hz
    (by simpa only [responseG,supportLine,slope] using hG)
  simpa only [secondSupportMinimum,responseG,supportLine,slope,W,mul_assoc] using hh

 theorem first_support_le_cross (r : Row) (lam h : ℝ) (hh : h ≤ hCross r lam) :
    supportLine r .first lam h ≤ supportLine r .first lam (hCross r lam) := by
  have hs : 0 ≤ slope r .first := by cases r <;> norm_num [slope]
  simpa only [supportLine,add_comm] using
    add_le_add_right (mul_le_mul_of_nonneg_left hh hs) (intercept r .first lam)

 theorem firstSupport_denominator_on_domain {r : Row} {lam H rho z h : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam)
    (hg : EndpointGuardsPositive r lam H)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1) (hz : z ≤ zPlus H)
    (hh : h ≤ hCross r lam) (hL : 0 ≤ supportLine r .first lam h) :
    0 < delta r lam+responseD r lam H rho z*supportLine r .first lam h := by
  have hx := secondSupport_guards_on_domain hlam hH0 hHq hg hr0 hr1 le_rfl
    (hCross_lt_hPlus hlam).le hz
  have hI := actual_second_response_interval hlam le_rfl (hCross_lt_hPlus hlam).le
  have hLcross := (second_support_signs hlam hI.1).1
  have heq := hCross_support_identity r lam
  have hd := (inRow_coefficient_positive hlam).2.2.2
  apply firstSupport_denominator_pos _ _ _ (supportLine r .first lam (hCross r lam))
    hd hL (first_support_le_cross r lam h hh)
  · rw [heq]
    exact hLcross
  · simpa only [heq,responseG] using hx.2.2

 theorem secondSupportMinimum_pos_from_W_start {r : Row} {phase : SourcePhase}
    {lam H rho z h0 h : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam)
    (hg : EndpointGuardsPositive r lam H)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1) (hz0 : 0 < z) (hz1 : z ≤ zPlus H)
    (hstart : hCross r lam ≤ h0) (hh0 : h0 ≤ h) (hh1 : h ≤ hPlus lam)
    (hW : 0 < W r phase lam H rho z h0 (supportLine r .second lam h0)) :
    0 < secondSupportMinimum r phase lam H rho z h := by
  have hd := (inRow_coefficient_positive hlam).2.2.2
  have hden := light_rational_denominators hlam hH0 hHq
  have hp : 0 < pH lam H := hden.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 0 < vacancyLo lam H := hden.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hr : 0 ≤ rho := hv.le.trans hr0
  have hb : 0 ≤ pH lam H*beta r lam*rho := by
    have hbeta := (inRow_coefficient_positive hlam).2.1
    positivity
  have hguards : ∀ x ∈ Set.Icc h0 (hPlus lam),
      0 < responseC r lam H rho+2*responseD r lam H rho z*x ∧
      responseC r lam H rho+2*responseD r lam H rho z*x <
        10*(delta r lam+responseD r lam H rho z*((3/10)*x+intercept r .second lam)) := by
    intro x hx
    have hxg := secondSupport_guards_on_domain hlam hH0 hHq hg hr0 hr1
      (hstart.trans hx.1) hx.2 hz1
    simpa only [responseR,responseSlack,responseG,supportLine,slope] using
      (show 0 < responseR r lam H rho z x ∧
        responseR r lam H rho z x < 10*responseG r lam H rho z x from
        ⟨hxg.1,by have hs := hxg.2.1; unfold responseSlack at hs; linarith⟩)
  have hG0 := (secondSupport_guards_on_domain hlam hH0 hHq hg hr0 hr1
    hstart (hh0.trans hh1) hz1).2.2
  have hm0 : 0 < secondSupportMinimum r phase lam H rho z h0 := by
    have hi := secondSupportMinimum_W_identity r phase lam H rho z h0 hz0.ne' hG0.ne'
    have hh : 0 < 4*z*responseG r lam H rho z h0*secondSupportMinimum r phase lam H rho z h0 := by
      rw [hi]
      exact hW
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4*z*responseG r lam H rho z h0)).mp hh
  exact supportMinimum_pos_from_left _ _ _ _ _ _ h0 (hPlus lam) h hb hd hguards hh0 hh1 hm0

 theorem secondSupport_W_pos_from_start {r : Row} {phase : SourcePhase}
    {lam H rho z h0 h : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam)
    (hg : EndpointGuardsPositive r lam H)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1) (hz0 : 0 < z) (hz1 : z ≤ zPlus H)
    (hstart : hCross r lam ≤ h0) (hh0 : h0 ≤ h) (hh1 : h ≤ hPlus lam)
    (hW : 0 < W r phase lam H rho z h0 (supportLine r .second lam h0)) :
    0 < W r phase lam H rho z h (supportLine r .second lam h) := by
  have hm := secondSupportMinimum_pos_from_W_start hlam hH0 hHq hg hr0 hr1 hz0 hz1 hstart hh0 hh1 hW
  have hG := (secondSupport_guards_on_domain hlam hH0 hHq hg hr0 hr1
    (hstart.trans hh0) hh1 hz1).2.2
  rw [← secondSupportMinimum_W_identity r phase lam H rho z h hz0.ne' hG.ne']
  positivity

 theorem scaledPayment_second_pos_from_start {r : Row} {phase : SourcePhase}
    {lam H rho z h0 h y : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam)
    (hg : EndpointGuardsPositive r lam H)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1) (hz0 : 0 < z) (hz1 : z ≤ zPlus H)
    (hstart : hCross r lam ≤ h0) (hh0 : h0 ≤ h) (hh1 : h ≤ hPlus lam)
    (hW : 0 < W r phase lam H rho z h0 (supportLine r .second lam h0)) :
    0 < scaledPayment r phase lam H rho z h y (supportLine r .second lam h) := by
  have hWp := secondSupport_W_pos_from_start hlam hH0 hHq hg hr0 hr1 hz0 hz1 hstart hh0 hh1 hW
  have hG := (secondSupport_guards_on_domain hlam hH0 hHq hg hr0 hr1
    (hstart.trans hh0) hh1 hz1).2.2
  have hI := actual_second_response_interval hlam (hstart.trans hh0) hh1
  have hL := (second_support_signs hlam hI.1).1
  have hden := light_rational_denominators hlam hH0 hHq
  exact scaledPayment_pos_of_W r phase lam H rho z h y (supportLine r .second lam h)
    hden.2.2.2.2.2.2.2.2.2.2.2.1 hL hG hz0.le hWp

#print axioms secondSupportMinimum
#print axioms supportMinimum_W_cleared
#print axioms secondSupportMinimum_W_identity
#print axioms first_support_le_cross
#print axioms firstSupport_denominator_on_domain
#print axioms secondSupportMinimum_pos_from_W_start
#print axioms secondSupport_W_pos_from_start
#print axioms scaledPayment_second_pos_from_start

end
end F4Unified.LightConstruction
