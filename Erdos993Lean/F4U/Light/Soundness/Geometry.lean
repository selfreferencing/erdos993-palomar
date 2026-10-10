module

public import Erdos993Lean.F4U.Light.Soundness.Coordinate

@[expose] public section


namespace F4U.Light

noncomputable def intervalLower (F : Fn) : ℝ := (F.a1 : ℝ) / F.a2
noncomputable def intervalUpper (F : Fn) : ℝ := (F.b1 : ℝ) / F.b2
noncomputable def ActivityInterval (F : Fn) (x : ℝ) : Prop :=
  intervalLower F ≤ x ∧ x ≤ intervalUpper F
noncomputable def activityArg (F : Fn) (x : ℝ) : ℝ :=
  if F.toQ then x / (1 - x) else x

structure GeometryFacts (F : Fn) : Prop where
  a2_pos : (0 : ℝ) < F.a2
  b2_pos : (0 : ℝ) < F.b2
  D_pos : (0 : ℝ) < F.D
  rad_pos : (0 : ℝ) < F.rad
  lo_eq : intervalLower F = ((F.c : ℝ) - F.rad) / F.D
  hi_eq : intervalUpper F = ((F.c : ℝ) + F.rad) / F.D
  q_upper : F.toQ = true → intervalUpper F < 1

theorem geomOK_sound {F : Fn} (h : geomOK F = true) : GeometryFacts F := by
  simp only [geomOK, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨ha2, hb2⟩, hq⟩, hD⟩, hr⟩, hcross⟩, hcenter⟩, hrad⟩
  have ha2r : (0 : ℝ) < F.a2 := by exact_mod_cast ha2
  have hb2r : (0 : ℝ) < F.b2 := by exact_mod_cast hb2
  have hDr : (0 : ℝ) < F.D := by exact_mod_cast hD
  have hrr : (0 : ℝ) < F.rad := by exact_mod_cast hr
  have hcr : (2 : ℝ) * F.c * F.a2 * F.b2 =
      F.D * ((F.a1 : ℝ) * F.b2 + (F.b1 : ℝ) * F.a2) := by exact_mod_cast hcenter
  have hrrad := congrArg (fun n : Nat => (n : ℝ)) hrad
  push_cast [Nat.cast_sub hcross.le] at hrrad
  constructor
  · exact ha2r
  · exact hb2r
  · exact hDr
  · exact hrr
  · unfold intervalLower
    apply (div_eq_div_iff (ne_of_gt ha2r) (ne_of_gt hDr)).mpr
    have hprod : (0 : ℝ) < (F.b2 : ℝ) := hb2r
    have he : ((F.a1 : ℝ) * F.D - ((F.c : ℝ) - F.rad) * F.a2) * F.b2 = 0 := by
      nlinarith [hcr, hrrad]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt hprod))
  · unfold intervalUpper
    apply (div_eq_div_iff (ne_of_gt hb2r) (ne_of_gt hDr)).mpr
    have he : ((F.b1 : ℝ) * F.D - ((F.c : ℝ) + F.rad) * F.b2) * F.a2 = 0 := by
      nlinarith [hcr, hrrad]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt ha2r))
  · intro htoq
    have hbn : F.b1 < F.b2 := by simpa [htoq] using hq
    have hbr : (F.b1 : ℝ) < F.b2 := by exact_mod_cast hbn
    unfold intervalUpper
    exact (div_lt_one hb2r).mpr hbr

theorem centered_coordinate {F : Fn} (hg : GeometryFacts F) {x : ℝ}
    (hx : ActivityInterval F x) :
    |((F.D : ℝ) * x - F.c) / F.rad| ≤ 1 ∧
      ((F.c : ℝ) + (F.rad : ℝ) * (((F.D : ℝ) * x - F.c) / F.rad)) / F.D = x := by
  rcases hx with ⟨hl, hh⟩
  rw [hg.lo_eq] at hl
  rw [hg.hi_eq] at hh
  have hl' := (div_le_iff₀ hg.D_pos).mp hl
  have hh' := (le_div_iff₀ hg.D_pos).mp hh
  constructor
  · apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hg.rad_pos).mpr
      nlinarith
    · apply (div_le_iff₀ hg.rad_pos).mpr
      nlinarith
  · field_simp [ne_of_gt hg.D_pos, ne_of_gt hg.rad_pos] <;> ring

theorem interval_coordinate {F : Fn} (hg : GeometryFacts F) {x : ℝ}
    (hx : ActivityInterval F x) :
    (0 ≤ ((F.D : ℝ) * x - ((F.c : ℝ) - F.rad)) / (2 * F.rad) ∧
      ((F.D : ℝ) * x - ((F.c : ℝ) - F.rad)) / (2 * F.rad) ≤ 1) ∧
      (((F.c : ℝ) - F.rad) + (2 * (F.rad : ℝ)) *
        (((F.D : ℝ) * x - ((F.c : ℝ) - F.rad)) / (2 * F.rad))) / F.D = x := by
  rcases hx with ⟨hl, hh⟩
  rw [hg.lo_eq] at hl
  rw [hg.hi_eq] at hh
  have hl' := (div_le_iff₀ hg.D_pos).mp hl
  have hh' := (le_div_iff₀ hg.D_pos).mp hh
  have hr2 : (0 : ℝ) < 2 * F.rad := by linarith [hg.rad_pos]
  constructor
  · constructor
    · apply div_nonneg _ hr2.le
      nlinarith
    · apply (div_le_iff₀ hr2).mpr
      nlinarith
  · field_simp [ne_of_gt hg.D_pos, ne_of_gt hg.rad_pos] <;> ring

end F4U.Light
