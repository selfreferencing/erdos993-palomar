module

public import Erdos993Lean.Analytic.V213.FiberRootCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
The literal weighted chord maximum on the entire half-line, its
attainment, the two printed logarithmic price routes, and weight E's
interpolation. These are generic analytic statements; no finite family
is consumed here. Source: Eq98--99.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set

noncomputable def fiberWeightedChord (s d k v t : ℝ) : ℝ :=
  s * (d - t) * Real.exp (k * t - v)

theorem fiber_weighted_unit_maximum (y : ℝ) : y * Real.exp (1 - y) ≤ 1 := by
  have h := Real.add_one_le_exp (y - 1)
  have he := mul_le_mul_of_nonneg_right h (Real.exp_pos (1 - y)).le
  have hid : Real.exp (y - 1) * Real.exp (1 - y) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hid] at he
  convert he using 1 <;> ring

theorem fiber_weighted_chord_factor {s d k v t : ℝ} (hk : k ≠ 0) :
    fiberWeightedChord s d k v t =
      (s / k) * Real.exp (k * d - v - 1) *
        ((k * (d - t)) * Real.exp (1 - k * (d - t))) := by
  have he : Real.exp (k * d - v - 1) * Real.exp (1 - k * (d - t)) =
      Real.exp (k * t - v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold fiberWeightedChord
  calc
    _ = (s / k) * (k * (d - t)) * Real.exp (k * t - v) := by field_simp [hk] <;> ring
    _ = _ := by rw [← he]; ring

/-- The bound holds even outside the half-line; its positive maximum is attained inside it. -/
theorem fiber_weighted_chord_maximum {s d k v t : ℝ} (hs : 0 < s) (hk : 0 < k) :
    fiberWeightedChord s d k v t ≤ (s / k) * Real.exp (k * d - v - 1) := by
  rw [fiber_weighted_chord_factor hk.ne']
  have h := mul_le_mul_of_nonneg_left (fiber_weighted_unit_maximum (k * (d - t)))
    (by positivity : 0 ≤ (s / k) * Real.exp (k * d - v - 1))
  simpa only [mul_one] using h

theorem fiber_weighted_chord_attained {s d k v : ℝ} (hk : 0 < k) :
    d - 1 / k ≤ d ∧
      fiberWeightedChord s d k v (d - 1 / k) =
        (s / k) * Real.exp (k * d - v - 1) := by
  constructor
  · have h : 0 < 1 / k := by positivity
    linarith only [h]
  · unfold fiberWeightedChord
    congr 1
    · field_simp [hk.ne'] <;> ring
    · congr 1
      field_simp [hk.ne'] <;> ring

theorem fiber_weighted_chord_strict_price {s d k v eta U : ℝ}
    (hs : 0 < s) (hk : 0 < k) (heta : 0 < eta)
    (hlog : Real.log (s / (k * eta)) ≤ U) (hgap : U < v + 1 - k * d) :
    (s / k) * Real.exp (k * d - v - 1) < eta := by
  have hr : 0 < s / (k * eta) := by positivity
  have h := Real.exp_lt_exp.mpr (lt_of_le_of_lt hlog hgap)
  rw [Real.exp_log hr] at h
  have he := mul_lt_mul_of_pos_right h (Real.exp_pos (k * d - v - 1))
  have hid : Real.exp (v + 1 - k * d) * Real.exp (k * d - v - 1) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hid] at he
  have he' := mul_lt_mul_of_pos_right he heta
  convert he' using 1
  · field_simp [hk.ne',heta.ne'] <;> ring
  · ring

theorem fiber_weighted_chord_price {s d k v eta U t : ℝ}
    (hs : 0 < s) (hk : 0 < k) (heta : 0 < eta)
    (hlog : Real.log (s / (k * eta)) ≤ U) (hgap : U < v + 1 - k * d) :
    fiberWeightedChord s d k v t < eta :=
  (fiber_weighted_chord_maximum hs hk).trans_lt
    (fiber_weighted_chord_strict_price hs hk heta hlog hgap)

theorem fiber_weighted_chord_hasDerivAt (s d k v t : ℝ) :
    HasDerivAt (fiberWeightedChord s d k v)
      (Real.exp (k * t - v) * (k * s * (d - t) - s)) t := by
  have hl := ((hasDerivAt_const t d).sub (hasDerivAt_id t)).const_mul s
  have he := (((hasDerivAt_id t).const_mul k).sub_const v).exp
  convert hl.mul he using 1
  · funext x
    rfl
  · dsimp
    ring

/-- The exceptional G/G and H/H route: the derivative is positive up to h. -/
theorem fiber_weighted_chord_endpoint {s d k v t h : ℝ}
    (hs : 0 < s) (hk : 0 < k) (hth : t ≤ h)
    (hend : 1 ≤ k * s * (d - h) - s) :
    fiberWeightedChord s d k v t ≤ fiberWeightedChord s d k v h := by
  have hm : MonotoneOn (fiberWeightedChord s d k v) (Icc t h) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun x => Real.exp (k * x - v) * (k * s * (d - x) - s)) (convex_Icc t h)
    · intro x hx
      exact (fiber_weighted_chord_hasDerivAt s d k v x).continuousAt.continuousWithinAt
    · intro x hx
      exact (fiber_weighted_chord_hasDerivAt s d k v x).hasDerivWithinAt
    · intro x hx
      have hx' : x ≤ h := (interior_subset hx).2
      have hks : 0 < k * s := mul_pos hk hs
      have hp : 0 ≤ k * s * (d - x) - s := by nlinarith only [hend,hx',hks]
      exact mul_nonneg (Real.exp_pos _).le hp
  exact hm ⟨le_refl _,hth⟩ ⟨hth,le_refl _⟩ hth

theorem fiber_weighted_chord_endpoint_price {s d k v t h eta U : ℝ}
    (hs : 0 < s) (hk : 0 < k) (heta : 0 < eta) (hth : t ≤ h)
    (hz : 0 < s * (d - h)) (hend : 1 ≤ k * s * (d - h) - s)
    (hlog : Real.log (s * (d - h) / eta) ≤ U) (hgap : U < v - k * h) :
    fiberWeightedChord s d k v t < eta := by
  have htest := Real.exp_lt_exp.mpr (lt_of_le_of_lt hlog hgap)
  rw [Real.exp_log (div_pos hz heta)] at htest
  have he := mul_lt_mul_of_pos_right htest (Real.exp_pos (k * h - v))
  have hid : Real.exp (v - k * h) * Real.exp (k * h - v) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hid] at he
  have he' := mul_lt_mul_of_pos_right he heta
  have he'' : fiberWeightedChord s d k v h < eta := by
    unfold fiberWeightedChord
    convert he' using 1 <;> field_simp [heta.ne'] <;> ring
  exact (fiber_weighted_chord_endpoint hs hk hth hend).trans_lt he''

theorem fiber_weight_interpolation {xE xD xF : ℝ}
    (h : (xD + xF) / 2 ≤ xE) :
    Real.exp (-xE) ≤ max (Real.exp (-xD)) (Real.exp (-xF)) := by
  by_cases hd : xD ≤ xF
  · have hx : xD ≤ xE := by linarith only [h,hd]
    exact (Real.exp_le_exp.mpr (neg_le_neg hx)).trans (le_max_left _ _)
  · have hx : xF ≤ xE := by linarith only [h,le_of_not_ge hd]
    exact (Real.exp_le_exp.mpr (neg_le_neg hx)).trans (le_max_right _ _)

theorem fiber_weight_interpolation_price {xE xD xF Z eta : ℝ}
    (h : (xD + xF) / 2 ≤ xE) (hZ : 0 ≤ Z)
    (hD : Real.exp (-xD) * Z < eta) (hF : Real.exp (-xF) * Z < eta) :
    Real.exp (-xE) * Z < eta := by
  have hb := mul_le_mul_of_nonneg_right (fiber_weight_interpolation h) hZ
  rw [max_mul_of_nonneg _ _ hZ] at hb
  exact hb.trans_lt (max_lt hD hF)

end Erdos993Lean.Analytic.V213
