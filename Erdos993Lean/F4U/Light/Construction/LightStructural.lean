module
public import Erdos993Lean.F4U.Light.Construction.FiniteFunctionSigns
public import Erdos993Lean.F4U.Light.Construction.ConsumerAliases
public import Erdos993Lean.F4U.Light.Construction.SupportConstruction
public import Erdos993Lean.F4U.Light.Construction.SupportResponse
public import Erdos993Lean.F4U.Light.Construction.ParentReplacement
public import Erdos993Lean.F4U.Light.Construction.ResponseSquare

/-! Consumer of precisely the retained actual function and guard signs.
Every intermediate retains the original parent, vacancy, source chord, child
and response. The two finite sign predicates are the only finite inputs. -/
@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

theorem actual_controls_from_finite {r : Row} {reg : Regime} {lam H t : ℝ}
    (hf : ActualFiniteFunctionSigns r) (hlam : InRow r lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hchart : parentChart r reg lam t = H)
    (hH0 : 0 < H) (hHq : H ≤ q lam)
    (control : ChildControl) (hactive : reg = .A → control = .V0)
    (endpoint : LogEndpoint) (phase : SourcePhase) :
    ∀ s ≤ vacancyControlDegree reg phase,
      0 < actualVacancyControl r reg phase endpoint control s lam H := by
  have hfirst : ∀ s ≤ vacancyControlDegree reg .first,
      0 < actualVacancyControl r reg .first endpoint control s lam H := by
    intro s hs
    simpa only [actualFunctionValue, hchart] using
      hf reg .first endpoint control s lam t hlam ht0 ht1 hactive hs (by simp)
  cases phase with
  | first => exact hfirst
  | second =>
    apply actual_second_controls_pos_of_retained r reg endpoint control hlam hH0 hHq hfirst
    intro s hs0 hs1
    simpa only [actualFunctionValue, hchart] using
      hf reg .second endpoint control s lam t hlam ht0 ht1 hactive hs1 (by simp [hs0])

theorem actual_guards_from_finite {r : Row} {lam H : ℝ}
    (hg : ActualGuardFunctionSigns r) (hlam : InRow r lam)
    (hH0 : q lam/2 ≤ H) (hHq : H ≤ q lam) : EndpointGuardsPositive r lam H := by
  obtain ⟨t, ht0, ht1, heq⟩ := actual_guard_chart_exists hlam hH0 hHq
  intro slot hslot
  simpa only [guardFunctionValue, heq] using hg slot lam t hslot hlam ht0 ht1

theorem quadratic_bernstein_pos {v0 vm v1 t : ℝ}
    (hv0 : 0 < v0) (hvm : 0 < vm) (hv1 : 0 < v1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (1-t)^2*v0+2*t*(1-t)*vm+t^2*v1 := by
  by_cases ht : t=1
  · subst t
    simpa using hv1
  · have htp : 0 < 1-t := by exact sub_pos.mpr (lt_of_le_of_ne ht1 ht)
    have h0 := mul_pos (sq_pos_of_pos htp) hv0
    have hm : 0 ≤ 2*t*(1-t)*vm := by positivity
    have h1 : 0 ≤ t^2*v1 := by positivity
    linarith

theorem first_W_pos_of_child_controls {r : Row} {phase : SourcePhase}
    {lam H rho z h : ℝ}
    (hh0 : hMinus r H ≤ h) (hh1 : h ≤ hCross r lam)
    (hv0 : 0 < childV0 r .B phase lam H rho z)
    (hvm : 0 < childM0 r phase lam H rho z)
    (hv1 : 0 < childV1 r phase lam H rho z) :
    0 < W r phase lam H rho z h (supportLine r .first lam h) := by
  by_cases heq : hMinus r H = hCross r lam
  · have hh : h=hMinus r H := by linarith
    simpa only [hh,childV0] using hv0
  · have hwidth : 0 < hCross r lam-hMinus r H :=
      sub_pos.mpr (lt_of_le_of_ne (hh0.trans hh1) heq)
    let t := (h-hMinus r H)/(hCross r lam-hMinus r H)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hh0) hwidth.le
    have ht1 : t ≤ 1 := (div_le_one hwidth).mpr (by linarith)
    have harg : hMinus r H+t*(hCross r lam-hMinus r H)=h := by
      dsimp [t]
      rw [div_mul_cancel₀ _ hwidth.ne']
      ring
    have hid := W_child_bernstein_identity r phase lam H rho z t
    rw [harg] at hid
    rw [hid]
    exact quadratic_bernstein_pos hv0 hvm hv1 ht0 ht1

def selectedSupport (reg : Regime) (r : Row) (lam h : ℝ) : Support :=
  match reg with
  | .A => .second
  | .B => if h ≤ hCross r lam then .first else .second

theorem scaled_endpoint_pos {r : Row} {reg : Regime} {phase : SourcePhase}
    {lam H t u y rho : ℝ}
    (hf : ActualFiniteFunctionSigns r) (hg : EndpointGuardsPositive r lam H)
    (hlam : InRow r lam) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hchart : parentChart r reg lam t=H) (hreg : RegimeDomain r reg lam H)
    (hH0 : 0 < H) (hHq : H ≤ q lam)
    (hphase : PhaseDomain phase lam H rho)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1)
    (hu0 : 0 < u) (huq : u ≤ q lam)
    (hh0 : hMinus r H ≤ childH u) (hh1 : childH u ≤ hPlus lam)
    (endpoint : LogEndpoint) :
    0 < scaledPayment r phase lam H rho (logEndpoint endpoint H) (childH u) y
      (supportLine r (selectedSupport reg r lam (childH u)) lam (childH u)) := by
  have hH1 : H < 1 := lt_of_le_of_lt (hHq.trans (inRow_q_bounds hlam).2) (by norm_num)
  have hz0 : 0 < logEndpoint endpoint H := by
    have hzminus : 0 < zMinus H := by
      have h2 : 0 < 2-H := by linarith
      unfold zMinus
      exact div_pos (by positivity) (zMinus_den_pos hH1)
    have hbr := logEndpoint_brackets hH0.le hH1
    cases endpoint <;> simp only [logEndpoint]
    · exact hzminus
    · linarith
  have hz1 : logEndpoint endpoint H ≤ zPlus H := by
    have hb := logEndpoint_brackets hH0.le hH1
    cases endpoint <;> simp only [logEndpoint] <;> linarith
  have hc : ∀ control, (reg=.A → control=.V0) →
      0 < childControlValue r reg phase control lam H rho (logEndpoint endpoint H) := by
    intro control hactive
    exact actual_child_control_pos r reg phase endpoint control hphase
      (actual_controls_from_finite hf hlam ht0 ht1 hchart hH0 hHq control hactive endpoint phase)
  cases reg with
  | A =>
    exact scaledPayment_second_pos_from_start hlam hH0.le hHq hg hr0 hr1 hz0 hz1
      (regimeA_hMinus_above_cross r hreg) hh0 hh1
      (by simpa only [childControlValue,childV0] using hc .V0 (by simp))
  | B =>
    by_cases hh : childH u ≤ hCross r lam
    · have hW := first_W_pos_of_child_controls hh0 hh
        (by simpa only [childControlValue] using hc .V0 (by simp))
        (by simpa only [childControlValue] using hc .M0 (by simp))
        (by simpa only [childControlValue] using hc .V1 (by simp))
      have hL := supportLine_positive (s:=.first) hlam hu0 huq
      have hG := firstSupport_denominator_on_domain hlam hH0.le hHq hg hr0 hr1 hz1 hh hL.le
      have hp := (light_rational_denominators hlam hH0.le hHq).2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [selectedSupport,if_pos hh] using
        scaledPayment_pos_of_W r phase lam H rho _ (childH u) y _ hp hL hG hz0.le hW
    · have hW : 0 < W r phase lam H rho (logEndpoint endpoint H) (hCross r lam)
          (supportLine r .second lam (hCross r lam)) := by
        rw [← hCross_support_identity r lam]
        simpa only [childControlValue,childV1] using hc .V1 (by simp)
      simpa only [selectedSupport,if_neg hh] using
        scaledPayment_second_pos_from_start hlam hH0.le hHq hg hr0 hr1 hz0 hz1
          le_rfl (le_of_not_ge hh) hh1 hW

theorem scaled_log_pos {r : Row} {phase : SourcePhase}
    {lam H rho z h y L : ℝ}
    (hP : 0 ≤ parentPPlus r lam H rho)
    (hz0 : zMinus H ≤ z) (hz1 : z ≤ zPlus H)
    (hm : 0 < scaledPayment r phase lam H rho (zMinus H) h y L)
    (hp : 0 < scaledPayment r phase lam H rho (zPlus H) h y L) :
    0 < scaledPayment r phase lam H rho z h y L := by
  by_cases heq : zMinus H=zPlus H
  · have hz : z=zMinus H := by linarith
    simpa only [hz] using hm
  · have hw : 0 < zPlus H-zMinus H :=
      sub_pos.mpr (lt_of_le_of_ne (hz0.trans hz1) heq)
    let t := (z-zMinus H)/(zPlus H-zMinus H)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hz0) hw.le
    have ht1 : t ≤ 1 := (div_le_one hw).mpr (by linarith)
    have harg : (1-t)*zMinus H+t*zPlus H=z := by
      dsimp [t]
      field_simp [hw.ne']
      <;> ring
    have hpos := positive_convex_combination hm hp ht0 ht1
    have hle := scaledPayment_log_chord_le r phase lam H rho (zMinus H) (zPlus H)
      h y L t hP ht0 ht1
    rw [harg] at hle
    exact lt_of_lt_of_le hpos hle

theorem reserve_ge_support {r : Row} {lam u y L : ℝ}
    (hd : 0 ≤ delta r lam) (hL : 0 < L) (hJL : childJ lam u ≤ L)
    (hy : Admissible lam u y) :
    delta r lam/L*(childH u-y)^2 ≤ reserve r lam u y := by
  rcases hy with hJ | ⟨hJ,hy⟩
  · simp only [reserve,if_pos hJ]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (mul_nonneg hd (sq_nonneg _)) hJ hJL
  · subst y
    simp only [sub_self,sq, mul_zero, reserve, hJ, lt_self_iff_false, if_false,le_refl]

theorem payment_scaled_gap (r : Row) (phase : SourcePhase) (lam Y rho u y L : ℝ)
    (hY : Y ≠ 0) (hp : p lam Y ≠ 0) :
    paymentWithParentP r lam Y rho u y (parentPPlus r lam (parentH Y) rho)-
      p lam Y/Y*scaledPayment r phase lam (parentH Y) rho Y (childH u) y L =
    p lam Y/Y*((rowData r).price/(1+lam))*rho*
      (source lam Y rho-sourceChord phase lam (parentH Y) rho)+
      (reserve r lam u y-delta r lam/L*(childH u-y)^2) := by
  simp only [paymentWithParentP,scaledPayment,parentNHat,pH_original]
  field_simp [hY,hp]
  <;> ring

theorem payment_ge_scaled {r : Row} {phase : SourcePhase} {lam Y rho u y L : ℝ}
    (hlam : InRow r lam) (hY : 0 < Y) (hcap : parentH Y ≤ q lam)
    (hHlo : q lam/2 ≤ parentH Y) (hphase : PhaseDomain phase lam (parentH Y) rho)
    (hrho : 0 ≤ rho) (hL : 0 < L) (hJL : childJ lam u ≤ L)
    (hy : Admissible lam u y) :
    p lam Y/Y*scaledPayment r phase lam (parentH Y) rho Y (childH u) y L ≤
      payment r lam Y rho u y := by
  have hl := (inRow_lambda_bounds hlam).1
  have hp := (p_original_bounds hl (Y:=Y)).1
  have hd := (inRow_coefficient_positive hlam).2.2.2
  have hchord := sourceChord_le_sourceH hlam hHlo hcap phase hphase
  rw [sourceH_original hcap] at hchord
  have hreserve := reserve_ge_support hd.le hL hJL hy
  have hprice : 0 ≤ (rowData r).price := by cases r <;> norm_num [rowData]
  have hgap := payment_scaled_gap r phase lam Y rho u y L hY.ne' hp.ne'
  have hnonneg : 0 ≤ p lam Y/Y*((rowData r).price/(1+lam))*rho*
      (source lam Y rho-sourceChord phase lam (parentH Y) rho) := by
    have hden : 0 < 1+lam := by linarith
    positivity
  have hle : p lam Y/Y*scaledPayment r phase lam (parentH Y) rho Y (childH u) y L ≤
      paymentWithParentP r lam Y rho u y (parentPPlus r lam (parentH Y) rho) := by linarith
  exact hle.trans (payment_parentPPlus_le hlam hY hcap)

theorem responseQuadratic_pos_of_support {r : Row} {lam Y rho u L : ℝ}
    (hlam : InRow r lam) (hY : 0 < Y) (hcap : parentH Y ≤ q lam)
    (hJ : 0 < childJ lam u) (hJL : childJ lam u ≤ L)
    (hG : 0 < delta r lam+responseD r lam (parentH Y) rho Y*L) :
    0 < responseQuadratic r lam Y rho u := by
  have hd := (inRow_coefficient_positive hlam).2.2.2
  have hQ := response_curvature_of_support _ _ _ _ hd hJ hJL hG
  have hp := (p_original_bounds (inRow_lambda_bounds hlam).1 (Y:=Y)).1
  have hP := parentP_le_parentPPlus hlam hY hcap (rho:=rho)
  have hmul := mul_le_mul_of_nonneg_left hP (mul_nonneg hp.le hY.le)
  simp only [responseQuadratic,responseD,pH_original] at hQ ⊢
  linarith

theorem selectedSupport_denominator {r : Row} {reg : Regime} {lam H rho z u : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam)
    (hreg : RegimeDomain r reg lam H) (hg : EndpointGuardsPositive r lam H)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1) (hz : z ≤ zPlus H)
    (hu0 : 0 < u) (huq : u ≤ q lam)
    (hh0 : hMinus r H ≤ childH u) (hh1 : childH u ≤ hPlus lam) :
    0 < delta r lam+responseD r lam H rho z*
      supportLine r (selectedSupport reg r lam (childH u)) lam (childH u) := by
  cases reg with
  | A =>
    have hh := (regimeA_hMinus_above_cross r hreg).trans hh0
    exact (secondSupport_guards_on_domain hlam hH0 hHq hg hr0 hr1 hh hh1 hz).2.2
  | B =>
    by_cases hh : childH u ≤ hCross r lam
    · simpa only [selectedSupport,if_pos hh] using
        firstSupport_denominator_on_domain hlam hH0 hHq hg hr0 hr1 hz hh
          (supportLine_positive (s:=.first) hlam hu0 huq).le
    · simpa only [selectedSupport,if_neg hh,responseG] using
        (secondSupport_guards_on_domain hlam hH0 hHq hg hr0 hr1
          (le_of_not_ge hh) hh1 hz).2.2

theorem lightCore_of_actual_signs (r : Row)
    (hf : ActualFiniteFunctionSigns r) (hg : ActualGuardFunctionSigns r) : LightCore r := by
  intro lam Y rho u hlam hY hcap hr hu0 huH
  have hH := parentH_bounds hY
  have hq := inRow_q_bounds hlam
  have hl := (inRow_lambda_bounds hlam).1
  have hup : 0 < u := by linarith [hq.1]
  have huq : u ≤ q lam := huH.trans hcap
  have hu1 : u < 1 := by linarith [hq.2]
  have hHlo : q lam/2 ≤ parentH Y := hu0.trans huH
  have hr0 : vacancyLo lam (parentH Y) ≤ rho := by
    simpa only [vacancyLo,lowerVacancy,pH_original] using hr.1
  have hr1 : rho ≤ 1 := hr.2
  have hden := light_rational_denominators hlam hH.1.le hcap
  have hv : 0 < vacancyLo lam (parentH Y) := hden.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hrho : 0 ≤ rho := hv.le.trans hr0
  obtain ⟨reg,t,ht0,ht1,hchart,hreg⟩ := actual_parent_chart_exists hlam hHlo hcap
  obtain ⟨phase,hphase⟩ : ∃ phase, PhaseDomain phase lam (parentH Y) rho := by
    rcases le_total rho (vacancySwitch lam (parentH Y)) with hp | hp
    · exact ⟨.first,hr0,hp⟩
    · exact ⟨.second,hp,hr1⟩
  have hguards := actual_guards_from_finite hg hlam hHlo hcap
  have hh0 := hMinus_le_childH hlam hcap hup.le huH
  have hh1 := childH_le_hPlus hlam hY hcap hu0 huH
  let s := selectedSupport reg r lam (childH u)
  let L := supportLine r s lam (childH u)
  have hL : 0 < L := supportLine_positive hlam hup huq
  have hJL : childJ lam u ≤ L := (childJ_lt_supportLine hlam hup huq).le
  have hz := logEndpoint_parent_brackets hY
  have hscaled : ∀ y, 0 < scaledPayment r phase lam (parentH Y) rho Y (childH u) y L := by
    intro y
    apply scaled_log_pos (parentPPlus_positive hlam hH.1.le hcap hrho).le hz.1 hz.2
    · exact scaled_endpoint_pos hf hguards hlam ht0 ht1 hchart hreg hH.1 hcap
        hphase hr0 hr1 hup huq hh0 hh1 .lower
    · exact scaled_endpoint_pos hf hguards hlam ht0 ht1 hchart hreg hH.1 hcap
        hphase hr0 hr1 hup huq hh0 hh1 .upper
  have hpay : ∀ y, Admissible lam u y → 0 < payment r lam Y rho u y := by
    intro y hy
    have hp := (p_original_bounds hl (Y:=Y)).1
    exact lt_of_lt_of_le (mul_pos (div_pos hp hY) (hscaled y))
      (payment_ge_scaled hlam hY hcap hHlo hphase hrho hL hJL hy)
  have hJ0 := childJ_nonnegative hl hup hu1 huq
  by_cases hJ : childJ lam u=0
  · refine ⟨payment r lam Y rho u (childH u),MinAt_zero_reserve r lam Y rho u hJ,?_⟩
    exact hpay (childH u) (Or.inr ⟨hJ,rfl⟩)
  · have hJpos : 0 < childJ lam u := lt_of_le_of_ne hJ0 (Ne.symm hJ)
    have hG : 0 < delta r lam+responseD r lam (parentH Y) rho Y*L :=
      selectedSupport_denominator hlam hH.1.le hcap hreg hguards hr0 hr1 hz.2
        hup huq hh0 hh1
    have hQ := responseQuadratic_pos_of_support hlam hY hcap hJpos hJL hG
    have hmin := MinAt_positive_reserve r lam Y rho u hJpos hQ
    refine ⟨_,hmin,?_⟩
    obtain ⟨y,hy,heq⟩ := hmin.2
    rw [← heq]
    exact hpay y hy

#print axioms actual_controls_from_finite
#print axioms actual_guards_from_finite
#print axioms first_W_pos_of_child_controls
#print axioms scaled_endpoint_pos
#print axioms scaled_log_pos
#print axioms reserve_ge_support
#print axioms payment_scaled_gap
#print axioms payment_ge_scaled
#print axioms responseQuadratic_pos_of_support
#print axioms selectedSupport_denominator
#print axioms lightCore_of_actual_signs

end
end F4Unified.LightConstruction
