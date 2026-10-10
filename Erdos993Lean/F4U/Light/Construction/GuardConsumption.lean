module

public import Erdos993Lean.F4U.Light.Construction.SecondSupportAlgebra

/-!
The finite input is exactly the set of twenty literal ActiveGuard functions.
Response interval and support geometry below are named helper premises which
must be discharged from the original LightCore domain before this is consumed.
No extra premise is added to the unchanged LightCore statement. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 def EndpointGuardsPositive (r : Row) (lam H : ℝ) : Prop :=
  ∀ slot, ActiveGuard r slot → 0 < guardValue r slot lam H

 theorem positive_convex_combination {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (1-t)*a+t*b := by
  by_cases ht : t=1
  · subst t
    simpa using hb
  · have htlt : t < 1 := lt_of_le_of_ne ht1 ht
    have ht' : 0 < 1-t := by linarith
    have ha' := mul_pos ht' ha
    have hb' := mul_nonneg ht0 hb.le
    linarith

 theorem affine_pos_on_closed_interval (f : ℝ → ℝ) {a b x : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b)
    (hfa : 0 < f a) (hfb : 0 < f b)
    (haff : ∀ t, f ((1-t)*a+t*b)=(1-t)*f a+t*f b) : 0 < f x := by
  by_cases hab : a=b
  · have hxa : x=a := by linarith
    simpa [hxa] using hfa
  · have hablt : a < b := lt_of_le_of_ne (hax.trans hxb) hab
    have hwidth : 0 < b-a := sub_pos.mpr hablt
    let t := (x-a)/(b-a)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hax) hwidth.le
    have ht1 : t ≤ 1 := by
      apply (div_le_iff₀ hwidth).2
      linarith
    have hx : (1-t)*a+t*b=x := by
      dsimp [t]
      field_simp [hwidth.ne']
      <;> ring
    rw [← hx,haff]
    exact positive_convex_combination hfa hfb ht0 ht1

 theorem responseInterval_nonnegative (r : Row) :
    0 ≤ responseIntervalLo r ∧ responseIntervalHi r ≤ 1 := by
  cases r <;> norm_num [responseIntervalLo,responseIntervalHi]

 theorem RGuard_pos_on_response_interval (r : Row) (lam H e h : ℝ)
    (hh0 : responseIntervalLo r ≤ h) (hh1 : h ≤ responseIntervalHi r)
    (h0 : 0 < RGuard r lam H (responseIntervalLo r) e)
    (h1 : 0 < RGuard r lam H (responseIntervalHi r) e) :
    0 < RGuard r lam H h e := by
  exact affine_pos_on_closed_interval (fun h => RGuard r lam H h e)
    hh0 hh1 h0 h1 (RGuard_h_interpolation r lam H e _ _)

 theorem SGuard_pos_on_response_interval (r : Row) (lam H h : ℝ)
    (hh0 : responseIntervalLo r ≤ h) (hh1 : h ≤ responseIntervalHi r)
    (h0 : 0 < SGuard r lam H (responseIntervalLo r))
    (h1 : 0 < SGuard r lam H (responseIntervalHi r)) :
    0 < SGuard r lam H h := by
  exact affine_pos_on_closed_interval (fun h => SGuard r lam H h)
    hh0 hh1 h0 h1 (SGuard_h_interpolation r lam H _ _)

 theorem activeGuards_R_at_lo (r : Row) (lam H h : ℝ)
    (hp : 0 < pH lam H) (hg : EndpointGuardsPositive r lam H)
    (hh0 : responseIntervalLo r ≤ h) (hh1 : h ≤ responseIntervalHi r) :
    0 < RGuard r lam H h (vacancyLo lam H) := by
  apply RGuard_pos_on_response_interval r lam H _ _ hh0 hh1
  · apply (retainedRGuard_pos_iff r lam H _ _ hp).mp
    simpa only [guardValue] using hg .r0_lo (by cases r <;> simp [ActiveGuard])
  · apply (retainedRGuard_pos_iff r lam H _ _ hp).mp
    simpa only [guardValue] using hg .r0_hi (by cases r <;> simp [ActiveGuard])

 theorem activeGuards_S (r : Row) (lam H h : ℝ)
    (hg : EndpointGuardsPositive r lam H)
    (hh0 : responseIntervalLo r ≤ h) (hh1 : h ≤ responseIntervalHi r) :
    0 < SGuard r lam H h := by
  apply SGuard_pos_on_response_interval r lam H _ hh0 hh1
  · simpa only [guardValue] using hg .s0 (by cases r <;> simp [ActiveGuard])
  · simpa only [guardValue] using hg .s1 (by cases r <;> simp [ActiveGuard])

 theorem activeGuards_R (r : Row) (lam H rho h : ℝ)
    (hp : 0 < pH lam H) (hp1 : pH lam H ≤ 1)
    (hg : EndpointGuardsPositive r lam H)
    (hh0 : responseIntervalLo r ≤ h) (hh1 : h ≤ responseIntervalHi r)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1)
    (hE : r=.E1 ∨ r=.E2 → zPlus H ≤ 1) :
    0 < RGuard r lam H h rho := by
  have hR0 := activeGuards_R_at_lo r lam H h hp hg hh0 hh1
  by_cases he : r=.E1 ∨ r=.E2
  · have hh0' : 0 ≤ h := (responseInterval_nonnegative r).1.trans hh0
    have hh1' : h ≤ 1 := hh1.trans (responseInterval_nonnegative r).2
    have hzh : 0 ≤ 1-zPlus H*h := by
      have hm := mul_le_mul_of_nonneg_right (hE he) hh0'
      linarith
    have hd : 0 ≤ RGuard r lam H h rho-RGuard r lam H h (vacancyLo lam H) := by
      rw [RGuard_rho_difference]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (sub_nonneg.mpr hr0)) (sub_nonneg.mpr hp1)) hzh
    linarith
  · have ha0 : ActiveGuard r .r1_lo := by cases r <;> simp [ActiveGuard] at he ⊢
    have ha1 : ActiveGuard r .r1_hi := by cases r <;> simp [ActiveGuard] at he ⊢
    have hR1 : 0 < RGuard r lam H h 1 := by
      apply RGuard_pos_on_response_interval r lam H _ _ hh0 hh1
      · apply (retainedRGuard_pos_iff r lam H _ _ hp).mp
        simpa only [guardValue] using hg .r1_lo ha0
      · apply (retainedRGuard_pos_iff r lam H _ _ hp).mp
        simpa only [guardValue] using hg .r1_hi ha1
    exact affine_pos_on_closed_interval (fun e => RGuard r lam H h e)
      hr0 hr1 hR0 hR1 (RGuard_rho_interpolation r lam H h _ _)

 theorem secondSupport_guards_consumer (r : Row) (lam H rho z h : ℝ)
    (hp : 0 < pH lam H) (hp1 : pH lam H ≤ 1)
    (hP : 0 ≤ parentPPlus r lam H rho)
    (hg : EndpointGuardsPositive r lam H)
    (hh0 : responseIntervalLo r ≤ h) (hh1 : h ≤ responseIntervalHi r)
    (hr0 : vacancyLo lam H ≤ rho) (hr1 : rho ≤ 1)
    (hz : z ≤ zPlus H) (hzplus : 0 ≤ zPlus H)
    (hintercept : 0 ≤ h+10*intercept r .second lam)
    (hE : r=.E1 ∨ r=.E2 → zPlus H ≤ 1) :
    0 < responseR r lam H rho z h ∧
    0 < responseSlack r lam H rho z h ∧
    0 < responseG r lam H rho z h := by
  have hh : 0 ≤ h := (responseInterval_nonnegative r).1.trans hh0
  have hz' : 0 ≤ zPlus H-z := sub_nonneg.mpr hz
  have hp1' : 0 ≤ 1-pH lam H := sub_nonneg.mpr hp1
  have hr1' : 0 ≤ 1-rho := sub_nonneg.mpr hr1
  have hR := activeGuards_R r lam H rho h hp hp1 hg hh0 hh1 hr0 hr1 hE
  have hRz : 0 ≤ responseR r lam H rho z h-
      responseR r lam H rho (zPlus H) h := by
    rw [responseR_z_difference]
    positivity
  rw [← responseR_at_zPlus] at hR
  have hRactual : 0 < responseR r lam H rho z h := by linarith
  have hS := activeGuards_S r lam H h hg hh0 hh1
  rw [← responseSlack_at_hi_zPlus] at hS
  have hSrho : 0 ≤ responseSlack r lam H rho (zPlus H) h-
      responseSlack r lam H 1 (zPlus H) h := by
    rw [responseSlack_rho_difference]
    positivity
  have hSz : 0 ≤ responseSlack r lam H rho z h-
      responseSlack r lam H rho (zPlus H) h := by
    rw [responseSlack_z_difference]
    positivity
  have hSactual : 0 < responseSlack r lam H rho z h := by linarith
  refine ⟨hRactual,hSactual,?_⟩
  unfold responseSlack at hSactual
  linarith

#print axioms EndpointGuardsPositive
#print axioms positive_convex_combination
#print axioms affine_pos_on_closed_interval
#print axioms responseInterval_nonnegative
#print axioms RGuard_pos_on_response_interval
#print axioms SGuard_pos_on_response_interval
#print axioms activeGuards_R_at_lo
#print axioms activeGuards_S
#print axioms activeGuards_R
#print axioms secondSupport_guards_consumer

end
end F4Unified.LightConstruction
