module

public import Erdos993Lean.BCFG.FullLightEndpoints
public import Erdos993Lean.BCFG.FullLightConcavity
public import Erdos993Lean.BCFG.LightEndpointResiduals

/-! Printed Lemma 5.16 on the entire closed light domain. The proof uses
the same three source values and a direct affine endpoint minorant, avoiding
division by either phase length. No finite certificate or source bound is assumed. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Set Erdos993Lean.Analytic Erdos993Lean.Analytic.V213.VarianceResponse

theorem fullLight_middle_minorant {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    lightSourceA lam omega*lightRhoStar lam omega+lightSourceB lam omega ≤
      O2.src lam (occupation lam omega) (lightRhoStar lam omega) := by
  rw [fullLight_source_middle hl hlo hhi]
  change lightSourceA lam omega*((lam/(1+2*lam))/occupation lam omega)+
    lightSourceB lam omega ≤ _
  rw [light_middle_endpoint_identity hl hlo]
  have hb := fullLight_AB_bounds hl hlo hhi
  have hm := min_ge_product_div hl hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  have hd := div_le_div_of_nonneg_right hm (show 0 ≤ 4*lam by positivity)
  have heq : ((1-omega)/omega)*((1+lam)*omega-1)/(4*lam^2) =
      (((1-omega)/omega)*((1+lam)*omega-1)/lam)/(4*lam) := by
    field_simp [hl.ne'] <;> ring
  rw [heq]
  exact add_le_add le_rfl hd

theorem light_source_minorant {lam omega rho : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1)
    (hr : rhoZero lam omega ≤ rho) (hr1 : rho ≤ 1) :
    lightSourceA lam omega*rho+lightSourceB lam omega ≤
      O2.src lam (occupation lam omega) rho := by
  have hleft : lightSourceA lam omega*rhoZero lam omega+lightSourceB lam omega ≤
      O2.src lam (occupation lam omega) (rhoZero lam omega) := by
    rw [fullLight_source_left hl hlo hhi]
    exact light_left_endpoint_minorant hl hlo hhi
  have hright : lightSourceA lam omega*1+lightSourceB lam omega ≤
      O2.src lam (occupation lam omega) 1 := by
    rw [mul_one,fullLight_source_right hl hlo hhi]
    exact light_right_endpoint_minorant hl hlo hhi
  have hmiddle := fullLight_middle_minorant hl hlo hhi
  rcases le_total rho (lightRhoStar lam omega) with h | h
  · exact affine_minorant_of_concave_endpoints
      (fullLight_source_concave_one hl hlo hhi) ⟨hr,h⟩ hleft hmiddle
  · exact affine_minorant_of_concave_endpoints
      (fullLight_source_concave_two hl hlo hhi) ⟨h,hr1⟩ hmiddle hright

theorem lightSourceA_pos {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) : 0 < lightSourceA lam omega := by
  have h1 : 0 < 1+lam := by linarith
  have hw := fullLight_omega_pos hl hlo
  have hbase : (1+lam)*(1/(1+lam))^2+
      lam*(2*lam+1)*(1/(1+lam))-1 = 2*lam^2/(1+lam) := by
    field_simp [h1.ne'] <;> ring
  have hbasepos : 0 < (1+lam)*(1/(1+lam))^2+
      lam*(2*lam+1)*(1/(1+lam))-1 := by
    rw [hbase]
    positivity
  have hdiff :
      ((1+lam)*omega^2+lam*(2*lam+1)*omega-1)-
      ((1+lam)*(1/(1+lam))^2+lam*(2*lam+1)*(1/(1+lam))-1) =
      (omega-1/(1+lam))*((1+lam)*(omega+1/(1+lam))+lam*(2*lam+1)) := by ring
  have hnonneg : 0 ≤ (omega-1/(1+lam))*
      ((1+lam)*(omega+1/(1+lam))+lam*(2*lam+1)) :=
    mul_nonneg (sub_nonneg.mpr hlo) (by positivity)
  have hn : 0 < 2*lam^2*omega+lam*omega^2+lam*omega+omega^2-1 := by
    nlinarith
  unfold lightSourceA
  exact div_pos (mul_pos (by linarith) hn) (by positivity)

/-- The complete printed source inequality and strict coefficient sign. -/
theorem global_light_source {lam omega rho : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1)
    (hr : rhoZero lam omega ≤ rho) (hr1 : rho ≤ 1) :
    lightSourceA lam omega*rho+lightSourceB lam omega ≤
      O2.src lam (occupation lam omega) rho ∧ 0 < lightSourceA lam omega :=
  ⟨light_source_minorant hl hlo hhi hr hr1,lightSourceA_pos hl hlo⟩

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.fullLight_middle_minorant
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_middle_minorant
#check Erdos993Lean.BCFG.Analytic.light_source_minorant
#print axioms Erdos993Lean.BCFG.Analytic.light_source_minorant
#check Erdos993Lean.BCFG.Analytic.lightSourceA_pos
#print axioms Erdos993Lean.BCFG.Analytic.lightSourceA_pos
#check Erdos993Lean.BCFG.Analytic.global_light_source
#print axioms Erdos993Lean.BCFG.Analytic.global_light_source
