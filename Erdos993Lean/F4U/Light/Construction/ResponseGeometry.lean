module

public import Erdos993Lean.F4U.Light.Construction.ChildBounds
public import Erdos993Lean.F4U.Light.Construction.GuardConsumption

/-!
Literal rational geometry for the original light supporting lines. Endpoint
numbers refer to named row/intercept/chart objects, never unnamed bounds.
The D correction and the E correction remain exactly the original functions. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem first_slope_gt_second (r : Row) : slope r .second < slope r .first := by
  cases r <;> norm_num [slope]

 theorem sigma_positive (r : Row) : 0 < sigma r := by
  cases r <;> norm_num [sigma]

 theorem q_mono_nonnegative {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : q a ≤ q b := by
  have ha' : 0 < 1+a := by linarith
  have hb' : 0 < 1+b := by linarith
  unfold q
  apply (div_le_div_iff₀ ha' hb').2
  nlinarith

 theorem inRow_q_endpoint_bounds {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    q (rowData r).lo ≤ q lam ∧ q lam ≤ q (rowData r).hi := by
  have ha : 0 ≤ (rowData r).lo := by cases r <;> norm_num [rowData]
  exact ⟨q_mono_nonnegative ha hlam.1,
    q_mono_nonnegative (inRow_lambda_bounds hlam).1.le hlam.2⟩

 def supportWeight (r : Row) (lam : ℝ) : ℝ :=
  match r with
  | .D | .H => (q lam-q (rowData r).lo)/(q (rowData r).hi-q (rowData r).lo)
  | .E1 | .E2 => (lam-(rowData r).lo)/((rowData r).hi-(rowData r).lo)

 theorem supportWeight_bounds {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    0 ≤ supportWeight r lam ∧ supportWeight r lam ≤ 1 := by
  have hq := inRow_q_endpoint_bounds hlam
  cases r <;> simp only [supportWeight,InRow,rowData] at *
  all_goals norm_num [q] at hq ⊢
  all_goals constructor
  all_goals first
    | positivity
    | apply (div_le_iff₀ (by norm_num)).2; linarith [hlam.1,hlam.2,hq.1,hq.2]
    | apply div_nonneg; linarith [hlam.1,hlam.2,hq.1,hq.2]; norm_num

 theorem intercept_as_weight (r : Row) (s : Support) (lam : ℝ) :
    intercept r s lam=(1-supportWeight r lam)*endpointInterceptLo r s+
      supportWeight r lam*endpointInterceptHi r s+interceptError r lam := by
  cases r <;> simp only [intercept,supportWeight,rowData]
  all_goals norm_num
  all_goals ring
  all_goals simp

 theorem interceptError_nonnegative {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    0 ≤ interceptError r lam := by
  have hq := inRow_q_endpoint_bounds hlam
  cases r <;> simp only [interceptError,rowData]
  · have hqa : 0 ≤ q lam-q (4/5) := sub_nonneg.mpr hq.1
    have hqb : 0 ≤ q (13/10)-q lam := sub_nonneg.mpr hq.2
    norm_num [q] at hqa hqb ⊢
    positivity
  · norm_num [q]
  · norm_num [q]
  · norm_num

 theorem endpoint_intercepts_order (r : Row) (s : Support) :
    endpointInterceptLo r s ≤ endpointInterceptHi r s := by
  cases r <;> cases s <;> norm_num [endpointInterceptLo,endpointInterceptHi]

 theorem intercept_lower_endpoint {r : Row} {s : Support} {lam : ℝ}
    (hlam : InRow r lam) : endpointInterceptLo r s ≤ intercept r s lam := by
  have hw := supportWeight_bounds hlam
  have hc := endpoint_intercepts_order r s
  have he := interceptError_nonnegative hlam
  rw [intercept_as_weight]
  have hh := mul_nonneg hw.1 (sub_nonneg.mpr hc)
  nlinarith

 def endpointCrossLo (r : Row) : ℝ :=
  (endpointInterceptLo r .second-endpointInterceptLo r .first)/
    (slope r .first-slope r .second)

 def endpointCrossHi (r : Row) : ℝ :=
  (endpointInterceptHi r .second-endpointInterceptHi r .first)/
    (slope r .first-slope r .second)

 theorem hCross_as_weight (r : Row) (lam : ℝ) :
    hCross r lam=(1-supportWeight r lam)*endpointCrossLo r+
      supportWeight r lam*endpointCrossHi r := by
  have hs : slope r .first-slope r .second ≠ 0 := sub_ne_zero.mpr (ne_of_gt (first_slope_gt_second r))
  unfold hCross
  rw [intercept_as_weight,intercept_as_weight]
  unfold endpointCrossLo endpointCrossHi
  field_simp [hs]
  <;> ring

 theorem cross_endpoint_geometry (r : Row) :
    endpointCrossHi r < endpointCrossLo r ∧
    responseIntervalLo r < endpointCrossHi r ∧
    endpointCrossLo r < hPlus (rowData r).hi ∧
    1-sigma r*q (rowData r).lo < endpointCrossHi r ∧
    0 < responseIntervalLo r+10*endpointInterceptLo r .second ∧
    0 < (3/10)*responseIntervalLo r+endpointInterceptLo r .second := by
  cases r <;> norm_num [endpointCrossLo,endpointCrossHi,endpointInterceptLo,
    endpointInterceptHi,slope,sigma,responseIntervalLo,hPlus,rowData,q]

 theorem hCross_endpoint_bounds {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    endpointCrossHi r ≤ hCross r lam ∧ hCross r lam ≤ endpointCrossLo r := by
  have hw := supportWeight_bounds hlam
  have hc := (cross_endpoint_geometry r).1.le
  rw [hCross_as_weight]
  have hlow := mul_nonneg (sub_nonneg.mpr hw.2) (sub_nonneg.mpr hc)
  have hhigh := mul_nonneg hw.1 (sub_nonneg.mpr hc)
  constructor <;> nlinarith

 theorem hPlus_endpoint_bounds {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    hPlus (rowData r).hi ≤ hPlus lam ∧ hPlus lam ≤ hPlus (rowData r).lo := by
  have hq := inRow_q_endpoint_bounds hlam
  have hqa : 0 ≤ q (rowData r).lo/2 := by cases r <;> norm_num [rowData,q]
  have hql : 0 ≤ q lam/2 := by linarith [(inRow_q_bounds hlam).1]
  have hqb : 0 ≤ q (rowData r).hi/2 := by cases r <;> norm_num [rowData,q]
  constructor
  · rw [← childTaylor4_q_half,← childTaylor4_q_half]
    exact childTaylor4_antitoneOn hql hqb (by linarith [hq.2])
  · rw [← childTaylor4_q_half,← childTaylor4_q_half]
    exact childTaylor4_antitoneOn hqa hql (by linarith [hq.1])

 theorem hPlus_below_response_interval (r : Row) :
    hPlus (rowData r).lo < responseIntervalHi r := by
  cases r <;> norm_num [hPlus,rowData,q,responseIntervalHi]

 theorem actual_second_response_interval {r : Row} {lam h : ℝ}
    (hlam : InRow r lam) (hh0 : hCross r lam ≤ h) (hh1 : h ≤ hPlus lam) :
    responseIntervalLo r ≤ h ∧ h ≤ responseIntervalHi r := by
  have hc := hCross_endpoint_bounds hlam
  have hg := cross_endpoint_geometry r
  have hp := hPlus_endpoint_bounds hlam
  exact ⟨(hg.2.1.le.trans hc.1).trans hh0,
    hh1.trans (hp.2.trans (hPlus_below_response_interval r).le)⟩

 theorem second_support_signs {r : Row} {lam h : ℝ}
    (hlam : InRow r lam) (hh : responseIntervalLo r ≤ h) :
    0 < supportLine r .second lam h ∧ 0 < h+10*intercept r .second lam := by
  have hc := intercept_lower_endpoint (s:=Support.second) hlam
  have hg := cross_endpoint_geometry r
  have hL := hg.2.2.2.2.2
  have hS := hg.2.2.2.2.1
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ (3/10:ℝ) by norm_num)
  simp only [supportLine,slope]
  constructor <;> linarith

 theorem hCross_support_identity (r : Row) (lam : ℝ) :
    supportLine r .first lam (hCross r lam)=supportLine r .second lam (hCross r lam) := by
  have hs : slope r .first-slope r .second ≠ 0 := sub_ne_zero.mpr (ne_of_gt (first_slope_gt_second r))
  unfold supportLine hCross
  field_simp [hs]
  <;> ring

 theorem hMinus_at_HCross (r : Row) (lam : ℝ) : hMinus r (HCross r lam)=hCross r lam := by
  have hs := (sigma_positive r).ne'
  unfold hMinus HCross
  field_simp [hs]
  <;> ring

 theorem regimeA_hMinus_above_cross (r : Row) {lam H : ℝ}
    (hreg : RegimeDomain r .A lam H) : hCross r lam ≤ hMinus r H := by
  have hm := mul_le_mul_of_nonneg_left hreg.2 (sigma_positive r).le
  rw [← hMinus_at_HCross r lam]
  unfold hMinus
  linarith

 theorem regimeB_hMinus_below_cross (r : Row) {lam H : ℝ}
    (hreg : RegimeDomain r .B lam H) : hMinus r H ≤ hCross r lam := by
  have hm := mul_le_mul_of_nonneg_left hreg.1 (sigma_positive r).le
  rw [← hMinus_at_HCross r lam]
  unfold hMinus
  linarith

 theorem zPlus_nonnegative_on_light {r : Row} {lam H : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam) : 0 ≤ zPlus H := by
  have hH : H ≤ 7/10 := hHq.trans (inRow_q_bounds hlam).2
  have hn : 0 < H^2-12*H+12 := by nlinarith [sq_nonneg H]
  have h1 : 0 < 1-H := by linarith
  have h2 : 0 < 2-H := by linarith
  unfold zPlus
  positivity

 theorem zPlus_le_one_to_8_13 {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 8/13) : zPlus H ≤ 1 := by
  have h1 : 0 < 1-H := by linarith
  have h2 : 0 < 2-H := by linarith
  have hden : 0 < 6*(1-H)*(2-H) := by positivity
  have hf : 0 ≤ H^2+H*(8/13)+(8/13)^2-18*H-18*(8/13)+30 := by
    nlinarith [sq_nonneg H]
  have hm := mul_nonneg (sub_nonneg.mpr hH1) hf
  have hi : 12-30*H+18*H^2-H^3 =
      12-30*(8/13)+18*(8/13)^2-(8/13)^3+
      ((8/13)-H)*(H^2+H*(8/13)+(8/13)^2-18*H-18*(8/13)+30) := by ring
  have hc : (0:ℝ) ≤ 12-30*(8/13)+18*(8/13)^2-(8/13)^3 := by norm_num
  unfold zPlus
  apply (div_le_iff₀ hden).2
  nlinarith [hi]

 theorem zPlus_le_one_E {r : Row} {lam H : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam)
    (hE : r=.E1 ∨ r=.E2) : zPlus H ≤ 1 := by
  apply zPlus_le_one_to_8_13 hH0
  have hq := inRow_q_endpoint_bounds hlam
  unfold q at hHq
  rcases hE with rfl | rfl
  · norm_num [rowData,q] at hq
    linarith [hq.2]
  · norm_num [rowData,q] at hq
    exact hHq.trans hq.2

 /-- Native guard consumer with all geometric signs discharged on the actual light parent.
 The input family is the literal endpoint guards. The full same-parent response
 fields are retained; no new analytic premise replaces a manuscript step. -/
 theorem secondSupport_guards_on_domain {r : Row} {lam H rho z h : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam)
    (hg : EndpointGuardsPositive r lam H)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1)
    (hh0 : hCross r lam ≤ h) (hh1 : h ≤ hPlus lam) (hz : z ≤ zPlus H) :
    0 < responseR r lam H rho z h ∧
    0 < responseSlack r lam H rho z h ∧
    0 < responseG r lam H rho z h := by
  have hd := light_rational_denominators hlam hH0 hHq
  have hp : 0 < pH lam H := hd.2.2.2.2.2.2.2.2.2.2.2.1
  have hp1 : pH lam H ≤ 1 := by linarith [hd.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hv : 0 < vacancyLo lam H := hd.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hr : 0 ≤ rho := hv.le.trans hr0
  have hP := parentPPlus_positive hlam hH0 hHq hr
  have hI := actual_second_response_interval hlam hh0 hh1
  have hS := (second_support_signs hlam hI.1).2
  exact secondSupport_guards_consumer r lam H rho z h hp hp1 hP.le hg
    hI.1 hI.2 hr0 hr1 hz (zPlus_nonnegative_on_light hlam hH0 hHq) hS.le
    (zPlus_le_one_E hlam hH0 hHq)

 theorem hCross_lt_hPlus {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    hCross r lam < hPlus lam := by
  exact lt_of_le_of_lt (hCross_endpoint_bounds hlam).2
    (lt_of_lt_of_le (cross_endpoint_geometry r).2.2.1 (hPlus_endpoint_bounds hlam).1)

 theorem supportWeight_D_reconstructs_q (lam : ℝ) :
    (1-supportWeight .D lam)*q (rowData .D).lo+
      supportWeight .D lam*q (rowData .D).hi=q lam := by
  norm_num [supportWeight,rowData,q]
  ring

 theorem D_cross_below_half_parent {lam : ℝ} (hlam : InRow .D lam) :
    hCross .D lam < 1-sigma .D*q lam/2 := by
  have hw := supportWeight_bounds hlam
  have h0 : (0:ℝ) < 1-sigma .D*q (rowData .D).lo/2-endpointCrossLo .D := by
    norm_num [sigma,rowData,q,endpointCrossLo,endpointInterceptLo,slope]
  have h1 : (0:ℝ) < 1-sigma .D*q (rowData .D).hi/2-endpointCrossHi .D := by
    norm_num [sigma,rowData,q,endpointCrossHi,endpointInterceptHi,slope]
  have hp := positive_convex_combination h0 h1 hw.1 hw.2
  have hi : 1-sigma .D*q lam/2-hCross .D lam =
      (1-supportWeight .D lam)*(1-sigma .D*q (rowData .D).lo/2-endpointCrossLo .D)+
      supportWeight .D lam*(1-sigma .D*q (rowData .D).hi/2-endpointCrossHi .D) := by
    rw [hCross_as_weight,← supportWeight_D_reconstructs_q lam]
    ring
  rw [← hi] at hp
  linarith

 theorem HCross_between_parent_endpoints {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    q lam/2 < HCross r lam ∧ HCross r lam < q lam := by
  have hs := sigma_positive r
  have hq := inRow_q_endpoint_bounds hlam
  have hc := hCross_endpoint_bounds hlam
  have hg := cross_endpoint_geometry r
  constructor
  · have hh : hCross r lam < 1-sigma r*q lam/2 := by
      by_cases hr : r=.D
      · subst r
        exact D_cross_below_half_parent hlam
      · have he : endpointCrossLo r < 1-sigma r*q (rowData r).hi/2 := by
          cases r
          · exact False.elim (hr rfl)
          · norm_num [endpointCrossLo,endpointInterceptLo,slope,sigma,rowData,q]
          · norm_num [endpointCrossLo,endpointInterceptLo,slope,sigma,rowData,q]
          · norm_num [endpointCrossLo,endpointInterceptLo,slope,sigma,rowData,q]
        have hm := mul_le_mul_of_nonneg_left hq.2 hs.le
        linarith
    unfold HCross
    apply (lt_div_iff₀ hs).2
    linarith
  · have hm := mul_le_mul_of_nonneg_left hq.1 hs.le
    have he := hg.2.2.2.1
    unfold HCross
    apply (div_lt_iff₀ hs).2
    linarith

 theorem actual_parent_chart_exists {r : Row} {lam H : ℝ}
    (hlam : InRow r lam) (hH0 : q lam/2 ≤ H) (hHq : H ≤ q lam) :
    ∃ reg t, 0 ≤ t ∧ t ≤ 1 ∧ parentChart r reg lam t=H ∧ RegimeDomain r reg lam H := by
  have hx := HCross_between_parent_endpoints hlam
  rcases le_total H (HCross r lam) with hA | hB
  · have hd : 0 < HCross r lam-q lam/2 := sub_pos.mpr hx.1
    let t := (H-q lam/2)/(HCross r lam-q lam/2)
    refine ⟨.A,t,div_nonneg (sub_nonneg.mpr hH0) hd.le,?_,?_,hH0,hA⟩
    · apply (div_le_iff₀ hd).2
      linarith
    · dsimp [t,parentChart]
      rw [mul_div_cancel₀ _ hd.ne']
      ring
  · have hd : 0 < q lam-HCross r lam := sub_pos.mpr hx.2
    let t := (H-HCross r lam)/(q lam-HCross r lam)
    refine ⟨.B,t,div_nonneg (sub_nonneg.mpr hB) hd.le,?_,?_,hB,hHq⟩
    · apply (div_le_iff₀ hd).2
      linarith
    · dsimp [t,parentChart]
      rw [mul_div_cancel₀ _ hd.ne']
      ring

 theorem actual_guard_chart_exists {r : Row} {lam H : ℝ}
    (hlam : InRow r lam) (hH0 : q lam/2 ≤ H) (hHq : H ≤ q lam) :
    ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ guardParentChart lam t=H := by
  have hq := (inRow_q_bounds hlam).1
  let t := (H-q lam/2)/(q lam/2)
  refine ⟨t,div_nonneg (sub_nonneg.mpr hH0) (by positivity),?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < q lam/2)).2
    linarith
  · dsimp [t,guardParentChart]
    field_simp [hq.ne']
    <;> ring

#print axioms first_slope_gt_second
#print axioms sigma_positive
#print axioms q_mono_nonnegative
#print axioms inRow_q_endpoint_bounds
#print axioms supportWeight
#print axioms supportWeight_bounds
#print axioms intercept_as_weight
#print axioms interceptError_nonnegative
#print axioms endpoint_intercepts_order
#print axioms intercept_lower_endpoint
#print axioms endpointCrossLo
#print axioms endpointCrossHi
#print axioms hCross_as_weight
#print axioms cross_endpoint_geometry
#print axioms hCross_endpoint_bounds
#print axioms hPlus_endpoint_bounds
#print axioms hPlus_below_response_interval
#print axioms actual_second_response_interval
#print axioms second_support_signs
#print axioms hCross_support_identity
#print axioms hMinus_at_HCross
#print axioms regimeA_hMinus_above_cross
#print axioms regimeB_hMinus_below_cross
#print axioms zPlus_nonnegative_on_light
#print axioms zPlus_le_one_to_8_13
#print axioms zPlus_le_one_E
#print axioms secondSupport_guards_on_domain
#print axioms hCross_lt_hPlus
#print axioms supportWeight_D_reconstructs_q
#print axioms D_cross_below_half_parent
#print axioms HCross_between_parent_endpoints
#print axioms actual_parent_chart_exists
#print axioms actual_guard_chart_exists

end
end F4Unified.LightConstruction
