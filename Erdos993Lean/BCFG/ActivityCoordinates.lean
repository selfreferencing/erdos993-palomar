module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Closed activity-row coordinates used by the BCFG norm minorant.
-/

@[expose] public section


namespace Erdos993Lean.BCFG

noncomputable def activityQ (x : ℝ) : ℝ := x / (1+x)

noncomputable def activityCenter (l h : ℝ) : ℝ := (activityQ l + activityQ h)/2

noncomputable def activityRadius (l h : ℝ) : ℝ := (activityQ h - activityQ l)/2

noncomputable def activityS (l h x : ℝ) : ℝ :=
  (activityQ x - activityCenter l h) / activityRadius l h

theorem activityQ_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    activityQ x ≤ activityQ y := by
  have hd1 : 0 < 1+x := by linarith
  have hd2 : 0 < 1+y := by linarith
  unfold activityQ
  apply (div_le_div_iff₀ hd1 hd2).mpr
  nlinarith

theorem activityQ_strictMono {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    activityQ x < activityQ y := by
  have hd1 : 0 < 1+x := by linarith
  have hd2 : 0 < 1+y := by linarith
  unfold activityQ
  apply (div_lt_div_iff₀ hd1 hd2).mpr
  nlinarith

theorem activityQ_lt_one {x : ℝ} (hx : 0 ≤ x) : activityQ x < 1 := by
  unfold activityQ
  apply (div_lt_one (show 0 < 1+x by linarith)).mpr
  linarith

theorem activityQ_inverse {x : ℝ} (hx : 0 ≤ x) :
    activityQ x / (1-activityQ x) = x := by
  have hd : 1+x ≠ 0 := ne_of_gt (by linarith : 0 < 1+x)
  have he : 1-x/(1+x) ≠ 0 := ne_of_gt (sub_pos.mpr (activityQ_lt_one hx))
  unfold activityQ
  field_simp [hd, he] <;> ring

theorem activityQ_reconstruct (l h x : ℝ) (hr : activityRadius l h ≠ 0) :
    activityCenter l h + activityRadius l h * activityS l h x = activityQ x := by
  unfold activityS
  field_simp [hr] <;> ring

/-- Normalization of an arbitrary nondegenerate closed real interval. -/
theorem centered_coordinate_mem {a b x : ℝ} (hab : a < b)
    (hx : a ≤ x ∧ x ≤ b) :
    |(x-(a+b)/2)/((b-a)/2)| ≤ 1 := by
  have hd : 0 < (b-a)/2 := by linarith
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith [hx.1]
  · apply (div_le_iff₀ hd).mpr
    linarith [hx.2]

/-- Recovers either packet chart: heavy (a,b)=(1/2,1/2), light (0,1). -/
theorem chart_coordinate {a b y : ℝ} (hb : 0 < b)
    (hy : a ≤ y ∧ y ≤ a+b) :
    (0 ≤ (y-a)/b ∧ (y-a)/b ≤ 1) ∧ a+b*((y-a)/b) = y := by
  refine ⟨⟨div_nonneg (sub_nonneg.mpr hy.1) hb.le, ?_⟩, ?_⟩
  · apply (div_le_one hb).mpr
    linarith [hy.2]
  · field_simp [ne_of_gt hb] <;> ring

/-- Applies to all four packet activity rows; endpoints are retained. -/
theorem activity_coordinates {l h x : ℝ} (hl : 0 ≤ l) (hlh : l < h)
    (hx : l ≤ x ∧ x ≤ h) :
    0 < activityRadius l h ∧
    0 ≤ activityQ x ∧ activityQ x < 1 ∧ |activityS l h x| ≤ 1 := by
  have hx0 : 0 ≤ x := le_trans hl hx.1
  have hq : activityQ l < activityQ h := activityQ_strictMono hl hlh
  refine ⟨?_, ?_, activityQ_lt_one hx0, ?_⟩
  · unfold activityRadius
    linarith
  · exact div_nonneg hx0 (by linarith)
  · unfold activityS activityCenter activityRadius
    exact centered_coordinate_mem hq
      ⟨activityQ_mono hl hx.1, activityQ_mono hx0 hx.2⟩

end Erdos993Lean.BCFG
