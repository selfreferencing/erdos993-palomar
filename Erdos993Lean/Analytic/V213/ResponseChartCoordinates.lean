module

public import Erdos993Lean.Analytic.V213.ResponseChartSource

/-! The closed heavy/light chart coordinates of current Lemma 5.23.
The affine-coordinate lemma explicitly includes zero-length intervals, so
the light seam and parent-leaf endpoints are not excluded by division.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set

noncomputable def chartParent (lam omega : ℝ) : ℝ := lam*omega/(1+lam*omega)
noncomputable def heavyOmega (lam x : ℝ) : ℝ := x/(1+lam)
noncomputable def lightOmega (lam x : ℝ) : ℝ := 1-actQ lam*x
noncomputable def chartRho (lo hi t : ℝ) : ℝ := lo+t*(hi-lo)

theorem sourceSwitch_activity {lam : ℝ} (hl : 0 < lam) :
    sourceSwitch (actQ lam) = lam/(1+2*lam) := by
  have h1 : 1+lam ≠ 0 := by positivity
  have h2 : 1+2*lam ≠ 0 := by positivity
  have h3 : 1+actQ lam ≠ 0 := by unfold actQ; positivity
  unfold sourceSwitch actQ at *
  field_simp [h1,h2,h3]
  ring

theorem chartParent_bounds {lam omega : ℝ} (hl : 0 < lam)
    (ho : 0 < omega) (ho1 : omega ≤ 1) :
    0 < chartParent lam omega ∧ chartParent lam omega ≤ actQ lam ∧
      chartParent lam omega < 1 := by
  have hd : 0 < 1+lam*omega := by positivity
  refine ⟨div_pos (mul_pos hl ho) hd,?_,(div_lt_one hd).2 (by linarith)⟩
  unfold chartParent actQ
  apply (div_le_div_iff₀ hd (by linarith)).2
  nlinarith

theorem chartParent_odds {lam omega : ℝ} (hl : 0 < lam) (ho : 0 < omega) :
    chartParent lam omega/(lam*(1-chartParent lam omega)) = omega := by
  have hd : 1+lam*omega ≠ 0 := by positivity
  have hp1 : chartParent lam omega < 1 :=
    (div_lt_one (by positivity : 0 < 1+lam*omega)).2 (by linarith)
  have hk : 1-chartParent lam omega ≠ 0 := by linarith
  unfold chartParent at *
  field_simp [hl.ne',hd,hk]
  ring

theorem chart_cavity_cap {lam omega : ℝ} (hl : 0 < lam) (ho : 0 < omega) :
    O2.cavH lam (chartParent lam omega) = min (actQ lam) (1-omega) := by
  rw [O2.cavH,chartParent_odds hl ho]

theorem heavy_chart_bounds {lam x : ℝ} (hl : 0 < lam)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < heavyOmega lam x ∧ heavyOmega lam x ≤ 1 ∧
    chartParent lam (heavyOmega lam x) ≤ sourceSwitch (actQ lam) ∧
    O2.cavH lam (chartParent lam (heavyOmega lam x)) = actQ lam := by
  have h1 : 0 < 1+lam := by linarith
  have ho : 0 < heavyOmega lam x := div_pos hx h1
  have ho1 : heavyOmega lam x ≤ 1 := (div_le_one h1).2 (by linarith)
  refine ⟨ho,ho1,?_,?_⟩
  · rw [sourceSwitch_activity hl]
    unfold chartParent heavyOmega
    have hxlam : 0 < 1+lam*(x/(1+lam)) := by positivity
    apply (div_le_div_iff₀ hxlam (by linarith)).2
    have hfrac : (x/(1+lam))*(1+lam) ≤ 1 := by
      rw [div_mul_cancel₀ _ h1.ne']
      exact hx1
    nlinarith
  · rw [chart_cavity_cap hl ho, min_eq_left]
    unfold actQ heavyOmega
    have heq : 1-x/(1+lam)-lam/(1+lam) = (1-x)/(1+lam) := by
      field_simp [h1.ne']
      ring
    have hn : 0 ≤ 1-x/(1+lam)-lam/(1+lam) := by
      rw [heq]
      exact div_nonneg (by linarith) h1.le
    linarith

theorem light_chart_bounds {lam x : ℝ} (hl : 0 < lam)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < lightOmega lam x ∧ lightOmega lam x ≤ 1 ∧
    sourceSwitch (actQ lam) ≤ chartParent lam (lightOmega lam x) ∧
    chartParent lam (lightOmega lam x) ≤ actQ lam ∧
    O2.cavH lam (chartParent lam (lightOmega lam x)) = actQ lam*x := by
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have ho : 0 < lightOmega lam x := by unfold lightOmega; nlinarith
  have ho1 : lightOmega lam x ≤ 1 := by unfold lightOmega; nlinarith
  refine ⟨ho,ho1,?_,(chartParent_bounds hl ho ho1).2.1,?_⟩
  · rw [sourceSwitch_activity hl]
    have hbase : 1/(1+lam) ≤ lightOmega lam x := by
      have hid : 1-actQ lam = 1/(1+lam) := by
        unfold actQ
        field_simp [ne_of_gt (show 0 < 1+lam by linarith)]
        ring
      rw [← hid]
      unfold lightOmega
      nlinarith
    have hb := (div_le_iff₀ (show 0 < 1+lam by linarith)).mp hbase
    unfold chartParent
    apply (div_le_div_iff₀ (by linarith : 0 < 1+2*lam) (by positivity)).2
    nlinarith
  · rw [chart_cavity_cap hl ho]
    have hid : 1-lightOmega lam x = actQ lam*x := by unfold lightOmega; ring
    rw [hid, min_eq_right (by nlinarith)]

theorem rhoStar_bounds {lam p : ℝ} (hl : 0 < lam) (hp : 0 < p)
    (hpstar : sourceSwitch (actQ lam) ≤ p) (hpq : p ≤ actQ lam) :
    rhoMin lam p ≤ rhoStar lam p ∧ rhoStar lam p ≤ 1 := by
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hp1 := hpq.trans_lt hq1
  have hpm : 0 < 1-p := sub_pos.mpr hp1
  constructor
  · have hd : 0 < 1+lam*(1-p) := by positivity
    have hb := (le_div_iff₀ (show 0 < 1+lam by linarith)).mp hpq
    unfold rhoMin rhoStar
    rw [sourceSwitch_activity hl]
    apply (div_le_div_iff₀ hd hp).2
    have heq : lam/(1+2*lam)*(1+lam*(1-p))-p =
        (1+lam)*(lam-p*(1+lam))/(1+2*lam) := by
      field_simp [ne_of_gt (show 0 < 1+2*lam by linarith)]
      ring
    have hn : 0 ≤ lam/(1+2*lam)*(1+lam*(1-p))-p := by
      rw [heq]
      exact div_nonneg (mul_nonneg (by linarith) (by nlinarith)) (by linarith)
    linarith
  · exact (div_le_one hp).2 hpstar

theorem closed_affine_coordinate {a b z : ℝ} (haz : a ≤ z) (hzb : z ≤ b) :
    ∃ t ∈ Icc (0 : ℝ) 1, z = chartRho a b t := by
  by_cases hab : a = b
  · have hz : z = a := by linarith
    refine ⟨0,by norm_num,?_⟩
    simpa [chartRho] using hz
  · have hd : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne (haz.trans hzb) hab)
    refine ⟨(z-a)/(b-a),⟨div_nonneg (by linarith) hd.le,
      (div_le_one hd).2 (by linarith)⟩,?_⟩
    unfold chartRho
    rw [div_mul_cancel₀ _ hd.ne']
    ring

theorem closed_child_coordinate {H u : ℝ} (hu : 0 ≤ u) (huH : u ≤ H) :
    ∃ v ∈ Icc (0 : ℝ) 1, u = H*v := by
  rcases closed_affine_coordinate hu huH with ⟨v,hv,heq⟩
  refine ⟨v,hv,?_⟩
  simpa only [chartRho,sub_zero,zero_add,mul_comm] using heq

theorem light_vacancy_coordinate {lam p rho : ℝ} (hl : 0 < lam) (hp : 0 < p)
    (hpstar : sourceSwitch (actQ lam) ≤ p) (hpq : p ≤ actQ lam)
    (hr : rhoMin lam p ≤ rho) (hr1 : rho ≤ 1) :
    (∃ t ∈ Icc (0 : ℝ) 1, rho = chartRho (rhoMin lam p) (rhoStar lam p) t) ∨
    (∃ t ∈ Icc (0 : ℝ) 1, rho = chartRho (rhoStar lam p) 1 t) := by
  rcases le_total rho (rhoStar lam p) with h | h
  · exact Or.inl (closed_affine_coordinate hr h)
  · exact Or.inr (closed_affine_coordinate h hr1)

theorem heavy_coordinates {lam Y p rho u : ℝ} (hl : 0 < lam)
    (hY : Real.log (1+lam) ≤ Y) (hx : 1/8 ≤ (1+lam)*Real.exp (-Y))
    (hp : p = chartParent lam (Real.exp (-Y)))
    (hr : rhoMin lam p ≤ rho) (hr1 : rho ≤ 1) (hu : 0 ≤ u) (huq : u ≤ actQ lam) :
    ∃ x ∈ Icc (1/8 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
      Real.exp (-Y) = heavyOmega lam x ∧ p = chartParent lam (heavyOmega lam x) ∧
      rho = chartRho (rhoMin lam p) 1 t ∧ u = actQ lam*v := by
  have h1 : 0 < 1+lam := by linarith
  have he := Real.exp_le_exp.mpr (neg_le_neg hY)
  have hlogexp : Real.exp (-Real.log (1+lam)) = (1+lam)⁻¹ := by
    rw [Real.exp_neg,Real.exp_log h1]
  rw [hlogexp] at he
  have hx1 : (1+lam)*Real.exp (-Y) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left he h1.le
    simpa [h1.ne',mul_comm] using hh
  obtain ⟨t,ht,hrt⟩ := closed_affine_coordinate hr hr1
  obtain ⟨v,hv,huv⟩ := closed_child_coordinate hu huq
  refine ⟨(1+lam)*Real.exp (-Y),⟨hx,hx1⟩,t,ht,v,hv,?_,?_,hrt,huv⟩
  · unfold heavyOmega
    field_simp [h1.ne']
  · rw [hp]
    congr 1
    unfold heavyOmega
    field_simp [h1.ne']

theorem light_coordinates {lam Y p rho u : ℝ} (hl : 0 < lam)
    (hY0 : 0 ≤ Y) (hY : Y ≤ Real.log (1+lam))
    (hp : p = chartParent lam (Real.exp (-Y)))
    (hr : rhoMin lam p ≤ rho) (hr1 : rho ≤ 1)
    (hu : 0 ≤ u) (huH : u ≤ O2.cavH lam p) :
    ∃ x ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
      Real.exp (-Y) = lightOmega lam x ∧ p = chartParent lam (lightOmega lam x) ∧
      u = actQ lam*x*v ∧
      ((∃ t ∈ Icc (0 : ℝ) 1, rho = chartRho (rhoMin lam p) (rhoStar lam p) t) ∨
       (∃ t ∈ Icc (0 : ℝ) 1, rho = chartRho (rhoStar lam p) 1 t)) := by
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have h1 : 0 < 1+lam := by linarith
  have he0 : Real.exp (-Y) ≤ 1 := by simpa using Real.exp_le_exp.mpr (show -Y ≤ 0 by linarith)
  have he1 := Real.exp_le_exp.mpr (neg_le_neg hY)
  rw [Real.exp_neg,Real.exp_log h1] at he1
  have hqid : 1-actQ lam = (1+lam)⁻¹ := by
    unfold actQ
    field_simp [h1.ne']
    ring
  let x := (1-Real.exp (-Y))/actQ lam
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hq.le
  have hx1 : x ≤ 1 := (div_le_one hq).2 (by rw [← hqid] at he1; linarith)
  have hox : Real.exp (-Y) = lightOmega lam x := by
    unfold lightOmega x
    field_simp [hq.ne']
    ring
  have hb := light_chart_bounds hl hx0 hx1
  have hp' : p = chartParent lam (lightOmega lam x) := hp.trans (congrArg _ hox)
  have hH : O2.cavH lam p = actQ lam*x := by rw [hp']; exact hb.2.2.2.2
  obtain ⟨v,hv,huv⟩ := closed_child_coordinate hu (hH ▸ huH)
  refine ⟨x,⟨hx0,hx1⟩,v,hv,hox,hp',huv,?_⟩
  apply light_vacancy_coordinate hl
  · rw [hp']; exact (chartParent_bounds hl hb.1 hb.2.1).1
  · rw [hp']; exact hb.2.2.1
  · rw [hp']; exact hb.2.2.2.1
  · exact hr
  · exact hr1

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.chartParent
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.chartParent
#check Erdos993Lean.Analytic.V213.VarianceResponse.heavyOmega
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.heavyOmega
#check Erdos993Lean.Analytic.V213.VarianceResponse.lightOmega
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.lightOmega
#check Erdos993Lean.Analytic.V213.VarianceResponse.chartRho
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.chartRho
#check Erdos993Lean.Analytic.V213.VarianceResponse.sourceSwitch_activity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.sourceSwitch_activity
#check Erdos993Lean.Analytic.V213.VarianceResponse.chartParent_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.chartParent_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.chartParent_odds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.chartParent_odds
#check Erdos993Lean.Analytic.V213.VarianceResponse.chart_cavity_cap
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.chart_cavity_cap
#check Erdos993Lean.Analytic.V213.VarianceResponse.heavy_chart_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.heavy_chart_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_chart_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_chart_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.rhoStar_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rhoStar_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.closed_affine_coordinate
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.closed_affine_coordinate
#check Erdos993Lean.Analytic.V213.VarianceResponse.closed_child_coordinate
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.closed_child_coordinate
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_vacancy_coordinate
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_vacancy_coordinate
#check Erdos993Lean.Analytic.V213.VarianceResponse.heavy_coordinates
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.heavy_coordinates
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_coordinates
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_coordinates
