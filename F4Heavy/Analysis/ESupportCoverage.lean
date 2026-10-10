module

public import F4Heavy.Analysis.ESupportGeometry

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem closed_interval_chord_parameter (a b h : ℝ) (hab : a < b)
    (ha : a ≤ h) (hb : h ≤ b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ h = (1-t)*a+t*b := by
  have ht := activity_weight_bounds a b h hab ha hb
  refine ⟨(h-a)/(b-a), ht.1, ht.2, ?_⟩
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

theorem e_support_chord_coverage (r : Row) (lam h J : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hh0 : eSupportVertex r lam 0 ≤ h) (hh1 : h ≤ 1)
    (hJ0 : J ≤ (7/3)*h+eSupportIntercept0 r lam)
    (hJ1 : J ≤ (3/10)*h+eSupportIntercept1 r lam)
    (hJ2 : J ≤ (-8/15)*h+eSupportIntercept2 r lam) :
    ∃ (i j : Fin 4) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      h = (1-t)*eSupportVertex r lam i+t*eSupportVertex r lam j ∧
      J ≤ (1-t)*eSupportHeight r lam i+t*eSupportHeight r lam j := by
  have hv := e_support_vertex_order r lam he hr
  by_cases hfirst : h ≤ eSupportVertex r lam 1
  · obtain ⟨t, ht0, ht1, hEq⟩ := closed_interval_chord_parameter _ _ h hv.2.1 hh0 hfirst
    refine ⟨0, 1, t, ht0, ht1, hEq, ?_⟩
    rw [e_support_first_segment, ← hEq]
    exact hJ0
  · by_cases hsecond : h ≤ eSupportVertex r lam 2
    · obtain ⟨t, ht0, ht1, hEq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.1
        (le_of_lt (lt_of_not_ge hfirst)) hsecond
      refine ⟨1, 2, t, ht0, ht1, hEq, ?_⟩
      rw [e_support_second_segment, ← hEq]
      exact hJ1
    · obtain ⟨t, ht0, ht1, hEq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.2
        (le_of_lt (lt_of_not_ge hsecond)) hh1
      refine ⟨2, 3, t, ht0, ht1, hEq, ?_⟩
      rw [e_support_third_segment, ← hEq]
      exact hJ2

theorem childH_upper_one (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) : childH u ≤ 1 := by
  by_cases hu : u = 0
  · simp [childH, hu]
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hu1)
    have hphi : 0 < -Real.log (1-u) := by linarith only [hlog, hup]
    simp only [childH, phi, if_neg hu]
    exact (div_le_one hphi).mpr (by linarith only [hlog])

theorem e_support_lower_vertex_of_first_bound (r : Row) (lam h J : ℝ)
    (hJ : 0 ≤ J) (hline : J ≤ (7/3)*h+eSupportIntercept0 r lam) :
    eSupportVertex r lam 0 ≤ h := by
  change -eSupportIntercept0 r lam/(7/3) ≤ h
  linarith only [hJ, hline]

end F4Heavy.Analysis
