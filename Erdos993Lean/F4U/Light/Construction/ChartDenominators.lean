module

public import Erdos993Lean.F4U.Light.Construction.ResponseGeometry
public import Erdos993Lean.F4U.Light.Construction.SourceCharts

/-! Original nonconstant factor domain for all twelve literal light charts:
regime A, regime B and the full guard chart on each of the four rows.
Each field names the actual lambda/H/source/log/support function it certifies.
No rational-normalization theorem or final LightCore theorem is assumed. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

structure OriginalLightFactors (r : Row) (lam H : ℝ) : Prop where
  lambda_pos : 0 < lam
  lambda_add_one_pos : 0 < 1+lam
  q_pos : 0 < q lam
  one_sub_q_pos : 0 < 1-q lam
  one_add_q_pos : 0 < 1+q lam
  two_sub_q_pos : 0 < 2-q lam
  H_pos : 0 < H
  one_sub_H_pos : 0 < 1-H
  two_sub_H_pos : 0 < 2-H
  one_sub_qH_pos : 0 < 1-q lam*H
  one_add_q_sub_qH_pos : 0 < 1+q lam-q lam*H
  p_pos : 0 < pH lam H
  one_sub_p_pos : 0 < 1-pH lam H
  vacancyLo_pos : 0 < vacancyLo lam H
  source_phase_width_pos : 0 < vacancySwitch lam H-vacancyLo lam H
  log_minus_denominator_pos : 0 < H^2-6*H+6
  slope_difference_pos : 0 < slope r .first-slope r .second
  sigma_pos : 0 < sigma r

 theorem original_light_factors {r : Row} {lam H : ℝ}
    (hlam : InRow r lam) (hH0 : q lam/2 ≤ H) (hHq : H ≤ q lam) :
    OriginalLightFactors r lam H := by
  have hH : 0 < H := by linarith [(inRow_q_bounds hlam).1]
  rcases light_rational_denominators hlam hH.le hHq with
    ⟨hl,hl1,hq,hq1,hqplus,hq2,hH1,hH2,hqH,hqplusH,hpoly,hp,hp1,hR⟩
  exact ⟨hl,hl1,hq,hq1,hqplus,hq2,hH,hH1,hH2,hqH,hqplusH,hp,hp1,hR,
    vacancy_first_phase_positive hlam hH hHq,hpoly,
    sub_pos.mpr (first_slope_gt_second r),sigma_positive r⟩

 theorem parentChart_bounds {r : Row} {reg : Regime} {lam t : ℝ}
    (hlam : InRow r lam) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    q lam/2 ≤ parentChart r reg lam t ∧ parentChart r reg lam t ≤ q lam := by
  have hx := HCross_between_parent_endpoints hlam
  cases reg
  · have hw : 0 ≤ HCross r lam-q lam/2 := sub_nonneg.mpr hx.1.le
    have hm0 := mul_nonneg hw ht0
    have hm1 := mul_le_mul_of_nonneg_left ht1 hw
    simp only [parentChart]
    constructor <;> linarith
  · have hw : 0 ≤ q lam-HCross r lam := sub_nonneg.mpr hx.2.le
    have hm0 := mul_nonneg hw ht0
    have hm1 := mul_le_mul_of_nonneg_left ht1 hw
    simp only [parentChart]
    constructor <;> linarith

 theorem guardParentChart_bounds {r : Row} {lam t : ℝ}
    (hlam : InRow r lam) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    q lam/2 ≤ guardParentChart lam t ∧ guardParentChart lam t ≤ q lam := by
  have hq := (inRow_q_bounds hlam).1
  have hm0 := mul_nonneg hq.le ht0
  have hm1 := mul_le_mul_of_nonneg_left ht1 hq.le
  unfold guardParentChart
  constructor <;> linarith

 theorem parentChart_factors {r : Row} {reg : Regime} {lam t : ℝ}
    (hlam : InRow r lam) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OriginalLightFactors r lam (parentChart r reg lam t) := by
  have hb := parentChart_bounds (reg:=reg) hlam ht0 ht1
  exact original_light_factors hlam hb.1 hb.2

 theorem guardChart_factors {r : Row} {lam t : ℝ}
    (hlam : InRow r lam) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OriginalLightFactors r lam (guardParentChart lam t) := by
  have hb := guardParentChart_bounds hlam ht0 ht1
  exact original_light_factors hlam hb.1 hb.2

 theorem lambda_from_q (lam : ℝ) (hlam : 0 < lam) : q lam/(1-q lam)=lam := by
  have hden : 0 < 1+lam := by linarith
  have hcomp : 0 < 1-q lam := by
    unfold q
    apply sub_pos.mpr
    rw [div_lt_one hden]
    linarith
  unfold q
  field_simp [hden.ne',hcomp.ne']
  <;> ring

#print axioms OriginalLightFactors
#print axioms original_light_factors
#print axioms parentChart_bounds
#print axioms guardParentChart_bounds
#print axioms parentChart_factors
#print axioms guardChart_factors
#print axioms lambda_from_q

end
end F4Unified.LightConstruction
