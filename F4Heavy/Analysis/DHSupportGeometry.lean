module

public import F4Heavy.Analysis.ChildWeight
public import F4Heavy.Analysis.ESupportCoverage

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_support_weight_bounds (lam : ℝ) (hr : InRow .D lam) :
    0 ≤ dSupportWeight lam ∧ dSupportWeight lam ≤ (397812500000000/397630901124639 : ℝ) := by
  have hr' : (4/5 : ℝ) ≤ lam ∧ lam ≤ (13/10 : ℝ) := hr
  have h := rational_activity_weight_bounds (4/5 : ℝ) (13/10 : ℝ) lam (485507815781/1000000000000 : ℝ)
    (by norm_num) (by norm_num) hr'.1 hr'.2 (by norm_num)
  norm_num [dSupportWeight] at h ⊢
  exact h

theorem h_support_weight_bounds (lam : ℝ) (hr : InRow .H lam) :
    0 ≤ hSupportWeight lam ∧ hSupportWeight lam ≤ (18125000000000/18123970564413 : ℝ) := by
  have hr' : (7/4 : ℝ) ≤ lam ∧ lam ≤ (7/3 : ℝ) := hr
  have h := rational_activity_weight_bounds (7/4 : ℝ) (7/3 : ℝ) lam (287682072451/1000000000000 : ℝ)
    (by norm_num) (by norm_num) hr'.1 hr'.2 (by norm_num)
  norm_num [hSupportWeight] at h ⊢
  exact h

noncomputable def dSupportVertex (lam : ℝ) : Fin 4 → ℝ
  | 0 => -dSupportIntercept0 lam/(11/5 : ℝ)
  | 1 => (dSupportIntercept1 lam-dSupportIntercept0 lam)/((11/5 : ℝ)-(3/10 : ℝ))
  | 2 => (dSupportIntercept2 lam-dSupportIntercept1 lam)/((3/10 : ℝ)-(-3/5 : ℝ))
  | 3 => 1

noncomputable def dSupportHeight (lam : ℝ) : Fin 4 → ℝ
  | 0 => 0
  | 1 => (11/5 : ℝ)*dSupportVertex lam 1+dSupportIntercept0 lam
  | 2 => (3/10 : ℝ)*dSupportVertex lam 2+dSupportIntercept1 lam
  | 3 => (-3/5 : ℝ)+dSupportIntercept2 lam

theorem d_support_vertex_order (lam : ℝ) (hr : InRow .D lam) :
    0 < dSupportVertex lam 0 ∧
    dSupportVertex lam 0 < dSupportVertex lam 1 ∧
    dSupportVertex lam 1 < dSupportVertex lam 2 ∧
    dSupportVertex lam 2 < dSupportVertex lam 3 := by
  have hw := d_support_weight_bounds lam hr
  norm_num [dSupportHeight, dSupportVertex, dSupportIntercept0, dSupportIntercept1, dSupportIntercept2]
  repeat' constructor
  all_goals linarith only [hw.1, hw.2]

theorem d_support_height_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < dSupportHeight lam 1 ∧
    0 < dSupportHeight lam 2 ∧
    0 < dSupportHeight lam 3 := by
  have hw := d_support_weight_bounds lam hr
  norm_num [dSupportHeight, dSupportVertex, dSupportIntercept0, dSupportIntercept1, dSupportIntercept2]
  repeat' constructor
  all_goals linarith only [hw.1, hw.2]

theorem d_support_segment_0 (lam t : ℝ) :
    (1-t)*dSupportHeight lam 0+t*dSupportHeight lam 1 =
      (11/5 : ℝ)*((1-t)*dSupportVertex lam 0+t*dSupportVertex lam 1)+dSupportIntercept0 lam := by
  simp only [dSupportHeight, dSupportVertex]
  ring

theorem d_support_segment_1 (lam t : ℝ) :
    (1-t)*dSupportHeight lam 1+t*dSupportHeight lam 2 =
      (3/10 : ℝ)*((1-t)*dSupportVertex lam 1+t*dSupportVertex lam 2)+dSupportIntercept1 lam := by
  simp only [dSupportHeight, dSupportVertex]
  ring

theorem d_support_segment_2 (lam t : ℝ) :
    (1-t)*dSupportHeight lam 2+t*dSupportHeight lam 3 =
      (-3/5 : ℝ)*((1-t)*dSupportVertex lam 2+t*dSupportVertex lam 3)+dSupportIntercept2 lam := by
  simp only [dSupportHeight, dSupportVertex]
  ring

theorem d_support_lower_vertex (lam h J : ℝ) (hJ : 0 ≤ J)
    (hline : J ≤ (11/5 : ℝ)*h+dSupportIntercept0 lam) : dSupportVertex lam 0 ≤ h := by
  change -dSupportIntercept0 lam/(11/5 : ℝ) ≤ h
  linarith only [hJ, hline]

theorem d_support_chord_coverage (lam h J : ℝ) (hr : InRow .D lam)
    (hh0 : dSupportVertex lam 0 ≤ h) (hh1 : h ≤ 1)
    (hJ0 : J ≤ (11/5 : ℝ)*h+dSupportIntercept0 lam)
    (hJ1 : J ≤ (3/10 : ℝ)*h+dSupportIntercept1 lam)
    (hJ2 : J ≤ (-3/5 : ℝ)*h+dSupportIntercept2 lam) :
    ∃ (i j : Fin 4) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      h = (1-t)*dSupportVertex lam i+t*dSupportVertex lam j ∧
      J ≤ (1-t)*dSupportHeight lam i+t*dSupportHeight lam j := by
  have hv := d_support_vertex_order lam hr
  by_cases hc0 : h ≤ dSupportVertex lam 1
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.1 hh0 hc0
    refine ⟨0, 1, t, ht0, ht1, heq, ?_⟩
    rw [d_support_segment_0, ← heq]
    exact hJ0
  by_cases hc1 : h ≤ dSupportVertex lam 2
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.1 (le_of_lt (lt_of_not_ge hc0)) hc1
    refine ⟨1, 2, t, ht0, ht1, heq, ?_⟩
    rw [d_support_segment_1, ← heq]
    exact hJ1
  obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.2 (le_of_lt (lt_of_not_ge hc1)) hh1
  refine ⟨2, 3, t, ht0, ht1, heq, ?_⟩
  rw [d_support_segment_2, ← heq]
  exact hJ2

noncomputable def hSupportVertex (lam : ℝ) : Fin 6 → ℝ
  | 0 => -hSupportIntercept0 lam/(12/5 : ℝ)
  | 1 => (hSupportIntercept1 lam-hSupportIntercept0 lam)/((12/5 : ℝ)-(3/10 : ℝ))
  | 2 => (hSupportIntercept2 lam-hSupportIntercept1 lam)/((3/10 : ℝ)-(-3/5 : ℝ))
  | 3 => (hSupportIntercept3 lam-hSupportIntercept2 lam)/((-3/5 : ℝ)-(-11/5 : ℝ))
  | 4 => (hSupportIntercept4 lam-hSupportIntercept3 lam)/((-11/5 : ℝ)-(-4/1 : ℝ))
  | 5 => 1

noncomputable def hSupportHeight (lam : ℝ) : Fin 6 → ℝ
  | 0 => 0
  | 1 => (12/5 : ℝ)*hSupportVertex lam 1+hSupportIntercept0 lam
  | 2 => (3/10 : ℝ)*hSupportVertex lam 2+hSupportIntercept1 lam
  | 3 => (-3/5 : ℝ)*hSupportVertex lam 3+hSupportIntercept2 lam
  | 4 => (-11/5 : ℝ)*hSupportVertex lam 4+hSupportIntercept3 lam
  | 5 => (-4/1 : ℝ)+hSupportIntercept4 lam

theorem h_support_vertex_order (lam : ℝ) (hr : InRow .H lam) :
    0 < hSupportVertex lam 0 ∧
    hSupportVertex lam 0 < hSupportVertex lam 1 ∧
    hSupportVertex lam 1 < hSupportVertex lam 2 ∧
    hSupportVertex lam 2 < hSupportVertex lam 3 ∧
    hSupportVertex lam 3 < hSupportVertex lam 4 ∧
    hSupportVertex lam 4 < hSupportVertex lam 5 := by
  have hw := h_support_weight_bounds lam hr
  norm_num [hSupportHeight, hSupportVertex, hSupportIntercept0, hSupportIntercept1, hSupportIntercept2, hSupportIntercept3, hSupportIntercept4]
  repeat' constructor
  all_goals linarith only [hw.1, hw.2]

theorem h_support_height_positive (lam : ℝ) (hr : InRow .H lam) :
    0 < hSupportHeight lam 1 ∧
    0 < hSupportHeight lam 2 ∧
    0 < hSupportHeight lam 3 ∧
    0 < hSupportHeight lam 4 ∧
    0 < hSupportHeight lam 5 := by
  have hw := h_support_weight_bounds lam hr
  norm_num [hSupportHeight, hSupportVertex, hSupportIntercept0, hSupportIntercept1, hSupportIntercept2, hSupportIntercept3, hSupportIntercept4]
  repeat' constructor
  all_goals linarith only [hw.1, hw.2]

theorem h_support_segment_0 (lam t : ℝ) :
    (1-t)*hSupportHeight lam 0+t*hSupportHeight lam 1 =
      (12/5 : ℝ)*((1-t)*hSupportVertex lam 0+t*hSupportVertex lam 1)+hSupportIntercept0 lam := by
  simp only [hSupportHeight, hSupportVertex]
  ring

theorem h_support_segment_1 (lam t : ℝ) :
    (1-t)*hSupportHeight lam 1+t*hSupportHeight lam 2 =
      (3/10 : ℝ)*((1-t)*hSupportVertex lam 1+t*hSupportVertex lam 2)+hSupportIntercept1 lam := by
  simp only [hSupportHeight, hSupportVertex]
  ring

theorem h_support_segment_2 (lam t : ℝ) :
    (1-t)*hSupportHeight lam 2+t*hSupportHeight lam 3 =
      (-3/5 : ℝ)*((1-t)*hSupportVertex lam 2+t*hSupportVertex lam 3)+hSupportIntercept2 lam := by
  simp only [hSupportHeight, hSupportVertex]
  ring

theorem h_support_segment_3 (lam t : ℝ) :
    (1-t)*hSupportHeight lam 3+t*hSupportHeight lam 4 =
      (-11/5 : ℝ)*((1-t)*hSupportVertex lam 3+t*hSupportVertex lam 4)+hSupportIntercept3 lam := by
  simp only [hSupportHeight, hSupportVertex]
  ring

theorem h_support_segment_4 (lam t : ℝ) :
    (1-t)*hSupportHeight lam 4+t*hSupportHeight lam 5 =
      (-4/1 : ℝ)*((1-t)*hSupportVertex lam 4+t*hSupportVertex lam 5)+hSupportIntercept4 lam := by
  simp only [hSupportHeight, hSupportVertex]
  ring

theorem h_support_lower_vertex (lam h J : ℝ) (hJ : 0 ≤ J)
    (hline : J ≤ (12/5 : ℝ)*h+hSupportIntercept0 lam) : hSupportVertex lam 0 ≤ h := by
  change -hSupportIntercept0 lam/(12/5 : ℝ) ≤ h
  linarith only [hJ, hline]

theorem h_support_chord_coverage (lam h J : ℝ) (hr : InRow .H lam)
    (hh0 : hSupportVertex lam 0 ≤ h) (hh1 : h ≤ 1)
    (hJ0 : J ≤ (12/5 : ℝ)*h+hSupportIntercept0 lam)
    (hJ1 : J ≤ (3/10 : ℝ)*h+hSupportIntercept1 lam)
    (hJ2 : J ≤ (-3/5 : ℝ)*h+hSupportIntercept2 lam)
    (hJ3 : J ≤ (-11/5 : ℝ)*h+hSupportIntercept3 lam)
    (hJ4 : J ≤ (-4/1 : ℝ)*h+hSupportIntercept4 lam) :
    ∃ (i j : Fin 6) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      h = (1-t)*hSupportVertex lam i+t*hSupportVertex lam j ∧
      J ≤ (1-t)*hSupportHeight lam i+t*hSupportHeight lam j := by
  have hv := h_support_vertex_order lam hr
  by_cases hc0 : h ≤ hSupportVertex lam 1
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.1 hh0 hc0
    refine ⟨0, 1, t, ht0, ht1, heq, ?_⟩
    rw [h_support_segment_0, ← heq]
    exact hJ0
  by_cases hc1 : h ≤ hSupportVertex lam 2
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.1 (le_of_lt (lt_of_not_ge hc0)) hc1
    refine ⟨1, 2, t, ht0, ht1, heq, ?_⟩
    rw [h_support_segment_1, ← heq]
    exact hJ1
  by_cases hc2 : h ≤ hSupportVertex lam 3
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.2.1 (le_of_lt (lt_of_not_ge hc1)) hc2
    refine ⟨2, 3, t, ht0, ht1, heq, ?_⟩
    rw [h_support_segment_2, ← heq]
    exact hJ2
  by_cases hc3 : h ≤ hSupportVertex lam 4
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.2.2.1 (le_of_lt (lt_of_not_ge hc2)) hc3
    refine ⟨3, 4, t, ht0, ht1, heq, ?_⟩
    rw [h_support_segment_3, ← heq]
    exact hJ3
  obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.2.2.2 (le_of_lt (lt_of_not_ge hc3)) hh1
  refine ⟨4, 5, t, ht0, ht1, heq, ?_⟩
  rw [h_support_segment_4, ← heq]
  exact hJ4

noncomputable def hUpperSupportVertex (lam : ℝ) : Fin 5 → ℝ
  | 0 => -hSupportIntercept0 lam/(12/5 : ℝ)
  | 1 => (hSupportIntercept1 lam-hSupportIntercept0 lam)/((12/5 : ℝ)-(3/10 : ℝ))
  | 2 => (hSupportIntercept2 lam-hSupportIntercept1 lam)/((3/10 : ℝ)-(-3/5 : ℝ))
  | 3 => (hSupportIntercept4 lam-hSupportIntercept2 lam)/((-3/5 : ℝ)-(-4/1 : ℝ))
  | 4 => 1

noncomputable def hUpperSupportHeight (lam : ℝ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => (12/5 : ℝ)*hUpperSupportVertex lam 1+hSupportIntercept0 lam
  | 2 => (3/10 : ℝ)*hUpperSupportVertex lam 2+hSupportIntercept1 lam
  | 3 => (-3/5 : ℝ)*hUpperSupportVertex lam 3+hSupportIntercept2 lam
  | 4 => (-4/1 : ℝ)+hSupportIntercept4 lam

theorem hUpper_support_vertex_order (lam : ℝ) (hr : InRow .H lam) :
    0 < hUpperSupportVertex lam 0 ∧
    hUpperSupportVertex lam 0 < hUpperSupportVertex lam 1 ∧
    hUpperSupportVertex lam 1 < hUpperSupportVertex lam 2 ∧
    hUpperSupportVertex lam 2 < hUpperSupportVertex lam 3 ∧
    hUpperSupportVertex lam 3 < hUpperSupportVertex lam 4 := by
  have hw := h_support_weight_bounds lam hr
  norm_num [hUpperSupportHeight, hUpperSupportVertex, hSupportIntercept0, hSupportIntercept1, hSupportIntercept2, hSupportIntercept4]
  repeat' constructor
  all_goals linarith only [hw.1, hw.2]

theorem hUpper_support_height_positive (lam : ℝ) (hr : InRow .H lam) :
    0 < hUpperSupportHeight lam 1 ∧
    0 < hUpperSupportHeight lam 2 ∧
    0 < hUpperSupportHeight lam 3 ∧
    0 < hUpperSupportHeight lam 4 := by
  have hw := h_support_weight_bounds lam hr
  norm_num [hUpperSupportHeight, hUpperSupportVertex, hSupportIntercept0, hSupportIntercept1, hSupportIntercept2, hSupportIntercept4]
  repeat' constructor
  all_goals linarith only [hw.1, hw.2]

theorem hUpper_support_segment_0 (lam t : ℝ) :
    (1-t)*hUpperSupportHeight lam 0+t*hUpperSupportHeight lam 1 =
      (12/5 : ℝ)*((1-t)*hUpperSupportVertex lam 0+t*hUpperSupportVertex lam 1)+hSupportIntercept0 lam := by
  simp only [hUpperSupportHeight, hUpperSupportVertex]
  ring

theorem hUpper_support_segment_1 (lam t : ℝ) :
    (1-t)*hUpperSupportHeight lam 1+t*hUpperSupportHeight lam 2 =
      (3/10 : ℝ)*((1-t)*hUpperSupportVertex lam 1+t*hUpperSupportVertex lam 2)+hSupportIntercept1 lam := by
  simp only [hUpperSupportHeight, hUpperSupportVertex]
  ring

theorem hUpper_support_segment_2 (lam t : ℝ) :
    (1-t)*hUpperSupportHeight lam 2+t*hUpperSupportHeight lam 3 =
      (-3/5 : ℝ)*((1-t)*hUpperSupportVertex lam 2+t*hUpperSupportVertex lam 3)+hSupportIntercept2 lam := by
  simp only [hUpperSupportHeight, hUpperSupportVertex]
  ring

theorem hUpper_support_segment_3 (lam t : ℝ) :
    (1-t)*hUpperSupportHeight lam 3+t*hUpperSupportHeight lam 4 =
      (-4/1 : ℝ)*((1-t)*hUpperSupportVertex lam 3+t*hUpperSupportVertex lam 4)+hSupportIntercept4 lam := by
  simp only [hUpperSupportHeight, hUpperSupportVertex]
  ring

theorem hUpper_support_lower_vertex (lam h J : ℝ) (hJ : 0 ≤ J)
    (hline : J ≤ (12/5 : ℝ)*h+hSupportIntercept0 lam) : hUpperSupportVertex lam 0 ≤ h := by
  change -hSupportIntercept0 lam/(12/5 : ℝ) ≤ h
  linarith only [hJ, hline]

theorem hUpper_support_chord_coverage (lam h J : ℝ) (hr : InRow .H lam)
    (hh0 : hUpperSupportVertex lam 0 ≤ h) (hh1 : h ≤ 1)
    (hJ0 : J ≤ (12/5 : ℝ)*h+hSupportIntercept0 lam)
    (hJ1 : J ≤ (3/10 : ℝ)*h+hSupportIntercept1 lam)
    (hJ2 : J ≤ (-3/5 : ℝ)*h+hSupportIntercept2 lam)
    (hJ3 : J ≤ (-4/1 : ℝ)*h+hSupportIntercept4 lam) :
    ∃ (i j : Fin 5) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      h = (1-t)*hUpperSupportVertex lam i+t*hUpperSupportVertex lam j ∧
      J ≤ (1-t)*hUpperSupportHeight lam i+t*hUpperSupportHeight lam j := by
  have hv := hUpper_support_vertex_order lam hr
  by_cases hc0 : h ≤ hUpperSupportVertex lam 1
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.1 hh0 hc0
    refine ⟨0, 1, t, ht0, ht1, heq, ?_⟩
    rw [hUpper_support_segment_0, ← heq]
    exact hJ0
  by_cases hc1 : h ≤ hUpperSupportVertex lam 2
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.1 (le_of_lt (lt_of_not_ge hc0)) hc1
    refine ⟨1, 2, t, ht0, ht1, heq, ?_⟩
    rw [hUpper_support_segment_1, ← heq]
    exact hJ1
  by_cases hc2 : h ≤ hUpperSupportVertex lam 3
  · obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.2.1 (le_of_lt (lt_of_not_ge hc1)) hc2
    refine ⟨2, 3, t, ht0, ht1, heq, ?_⟩
    rw [hUpper_support_segment_2, ← heq]
    exact hJ2
  obtain ⟨t, ht0, ht1, heq⟩ := closed_interval_chord_parameter _ _ h hv.2.2.2.2 (le_of_lt (lt_of_not_ge hc2)) hh1
  refine ⟨3, 4, t, ht0, ht1, heq, ?_⟩
  rw [hUpper_support_segment_3, ← heq]
  exact hJ3

end F4Heavy.Analysis
