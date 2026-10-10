module

public import Erdos993Lean.F4U.Light.Construction.Definitions
public import Erdos993Lean.F4U.Light.Construction.Domain
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


namespace F4Unified.LightConstruction

theorem zMinus_den_pos {H : ℝ} (hH : H < 1) : 0 < H ^ 2 - 6 * H + 6 := by
  nlinarith [sq_nonneg (H - 1)]

theorem zPlus_den_pos {H : ℝ} (hH : H < 1) : 0 < 6 * (1 - H) * (2 - H) := by
  exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hH)) (by linarith)

theorem parentLog_hasDerivAt {H : ℝ} (hH : H < 1) :
    HasDerivAt (fun u : ℝ => -Real.log (1 - u)) (1 / (1 - H)) H := by
  have hd := ((hasDerivAt_const H (1 : ℝ)).sub (hasDerivAt_id H)).log
    (ne_of_gt (sub_pos.mpr hH))
  convert hd.neg using 1
  · ext u
    rfl
  · dsimp
    ring

/-- The lower-endpoint remainder has exactly the manuscript's nonnegative derivative. -/
theorem zMinus_gap_hasDerivAt {H : ℝ} (hH : H < 1) :
    HasDerivAt (fun u : ℝ => -Real.log (1 - u) - zMinus u)
      (H ^ 4 / ((1 - H) * (H ^ 2 - 6 * H + 6) ^ 2)) H := by
  have hid := hasDerivAt_id H
  have hnum : HasDerivAt (fun u : ℝ => 3 * u * (2 - u)) (6 - 6 * H) H := by
    convert (hid.const_mul 3).mul ((hasDerivAt_const H (2 : ℝ)).sub hid) using 1
    · ext u
      dsimp <;> ring
    · dsimp <;> ring
  have hden : HasDerivAt (fun u : ℝ => u ^ 2 - 6 * u + 6) (2 * H - 6) H := by
    convert ((hid.pow 2).sub (hid.const_mul 6)).add_const 6 using 1
    · ext u
      dsimp <;> ring
    · dsimp <;> ring
  have hd := hnum.div hden (ne_of_gt (zMinus_den_pos hH))
  have hg := (parentLog_hasDerivAt hH).sub hd
  change HasDerivAt (fun u : ℝ => -Real.log (1 - u) - zMinus u)
    (1 / (1 - H) - ((6 - 6 * H) * (H ^ 2 - 6 * H + 6) -
      (3 * H * (2 - H)) * (2 * H - 6)) / (H ^ 2 - 6 * H + 6) ^ 2) H at hg
  convert hg using 1
  have h1 : 1 - H ≠ 0 := ne_of_gt (sub_pos.mpr hH)
  have h2 := ne_of_gt (zMinus_den_pos hH)
  apply (div_eq_iff (mul_ne_zero h1 (pow_ne_zero 2 h2))).mpr
  generalize hDeq : H ^ 2 - 6 * H + 6 = D at h2 ⊢
  field_simp [h1, h2]
  rw [← hDeq]
  ring

/-- The upper-endpoint remainder has exactly the manuscript's nonnegative derivative. -/
theorem zPlus_gap_hasDerivAt {H : ℝ} (hH : H < 1) :
    HasDerivAt (fun u : ℝ => zPlus u + Real.log (1 - u))
      (H ^ 4 / (6 * (1 - H) ^ 2 * (2 - H) ^ 2)) H := by
  have hid := hasDerivAt_id H
  have hnum : HasDerivAt (fun u : ℝ => u * (u ^ 2 - 12 * u + 12))
      (3 * H ^ 2 - 24 * H + 12) H := by
    convert hid.mul (((hid.pow 2).sub (hid.const_mul 12)).add_const 12) using 1
    · ext u
      dsimp <;> ring
    · dsimp <;> ring
  have hden : HasDerivAt (fun u : ℝ => 6 * (1 - u) * (2 - u)) (12 * H - 18) H := by
    convert (((hasDerivAt_const H (1 : ℝ)).sub hid).const_mul 6).mul
      ((hasDerivAt_const H (2 : ℝ)).sub hid) using 1
    · ext u
      dsimp <;> ring
    · dsimp <;> ring
  have hd := hnum.div hden (ne_of_gt (zPlus_den_pos hH))
  have hg := hd.sub (parentLog_hasDerivAt hH)
  have hn1 : (1 - H) ≠ 0 := ne_of_gt (sub_pos.mpr hH)
  have hn2 : (2 - H) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 2 - H)
  convert hg using 1
  · ext u
    dsimp [zPlus]
    ring
  · apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0)
      (pow_ne_zero 2 hn1)) (pow_ne_zero 2 hn2))).mpr
    field_simp [hn1, hn2] <;> ring

theorem zMinus_le_parentLog {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H < 1) :
    zMinus H ≤ -Real.log (1 - H) := by
  let f : ℝ → ℝ := fun u => -Real.log (1 - u) - zMinus u
  let f' : ℝ → ℝ := fun u => u ^ 4 / ((1 - u) * (u ^ 2 - 6 * u + 6) ^ 2)
  have hd : ∀ u ∈ Set.Icc 0 H, HasDerivAt f (f' u) u := by
    intro u hu
    exact zMinus_gap_hasDerivAt (lt_of_le_of_lt hu.2 hH1)
  have hm : MonotoneOn f (Set.Icc 0 H) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 H)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      have hu1 := lt_of_le_of_lt (interior_subset hu).2 hH1
      apply div_nonneg (pow_nonneg (interior_subset hu).1 4)
      exact mul_nonneg (sub_pos.mpr hu1).le (sq_nonneg _)
  have he := hm (show (0 : ℝ) ∈ Set.Icc 0 H by exact ⟨le_refl _, hH0⟩)
    (show H ∈ Set.Icc 0 H by exact ⟨hH0, le_refl _⟩) hH0
  have hf0 : f 0 = 0 := by simp [f, zMinus]
  rw [hf0] at he
  dsimp [f] at he
  linarith

theorem parentLog_le_zPlus {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H < 1) :
    -Real.log (1 - H) ≤ zPlus H := by
  let f : ℝ → ℝ := fun u => zPlus u + Real.log (1 - u)
  let f' : ℝ → ℝ := fun u => u ^ 4 / (6 * (1 - u) ^ 2 * (2 - u) ^ 2)
  have hd : ∀ u ∈ Set.Icc 0 H, HasDerivAt f (f' u) u := by
    intro u hu
    exact zPlus_gap_hasDerivAt (lt_of_le_of_lt hu.2 hH1)
  have hm : MonotoneOn f (Set.Icc 0 H) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 H)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      apply div_nonneg (pow_nonneg (interior_subset hu).1 4)
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have he := hm (show (0 : ℝ) ∈ Set.Icc 0 H by exact ⟨le_refl _, hH0⟩)
    (show H ∈ Set.Icc 0 H by exact ⟨hH0, le_refl _⟩) hH0
  have hf0 : f 0 = 0 := by simp [f, zPlus]
  rw [hf0] at he
  dsimp [f] at he
  linarith

theorem logEndpoint_brackets {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H < 1) :
    zMinus H ≤ -Real.log (1 - H) ∧ -Real.log (1 - H) ≤ zPlus H :=
  ⟨zMinus_le_parentLog hH0 hH1, parentLog_le_zPlus hH0 hH1⟩

theorem parentLog_parentH (Y : ℝ) : -Real.log (1 - parentH Y) = Y := by
  simp [parentH]

/-- The rational endpoints bracket the original parent's actual mass Y. -/
theorem logEndpoint_parent_brackets {Y : ℝ} (hY : 0 < Y) :
    zMinus (parentH Y) ≤ Y ∧ Y ≤ zPlus (parentH Y) := by
  have hb := parentH_bounds hY
  simpa only [parentLog_parentH] using logEndpoint_brackets hb.1.le hb.2

end F4Unified.LightConstruction
