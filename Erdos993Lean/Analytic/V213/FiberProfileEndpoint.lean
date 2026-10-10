module

public import Erdos993Lean.Analytic.V213.FiberWeightedChord
public import Mathlib.Analysis.Convex.Jensen

/-!
Exact E/V quadratic endpoint controls and propagation along the
literal chord of consecutive controls. Every scalar inequality used by
the source has a real semantic consumer. Generated records remain bound
by their separate canonical checker; this generic module consumes none.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set

theorem fiber_profile_endpoint_E {c0 c1 c2 R u z : ℝ}
    (hc1 : 0 ≤ c1) (hR : 0 ≤ R) (hu0 : 0 ≤ u) (huR : u ≤ R)
    (hderiv : 0 ≤ c1 + 2 * c2 * R) (hprice : c0 + c1 * R + c2 * R ^ 2 < z) :
    c0 + c1 * u + c2 * u ^ 2 < z := by
  have hfactor : 0 ≤ c1 + c2 * (R + u) := by
    by_cases hc2 : 0 ≤ c2
    · exact add_nonneg hc1 (mul_nonneg hc2 (add_nonneg hR hu0))
    · have hc2' : c2 ≤ 0 := le_of_not_ge hc2
      have hm := mul_le_mul_of_nonpos_left huR hc2'
      nlinarith only [hderiv,hm]
  have hp := mul_nonneg (sub_nonneg.mpr huR) hfactor
  have hb : c0 + c1 * u + c2 * u ^ 2 ≤ c0 + c1 * R + c2 * R ^ 2 := by
    nlinarith only [hp]
  exact hb.trans_lt hprice

theorem fiber_profile_endpoint_V {c0 c1 c2 u z : ℝ}
    (hc2 : c2 < 0) (hprice : 0 < 4 * (-c2) * (z - c0) - c1 ^ 2) :
    c0 + c1 * u + c2 * u ^ 2 < z := by
  have hsq : 0 ≤ (2 * c2 * u + c1) ^ 2 := sq_nonneg _
  have hid : 4 * (-c2) * (z - (c0 + c1 * u + c2 * u ^ 2)) =
      (4 * (-c2) * (z - c0) - c1 ^ 2) + (2 * c2 * u + c1) ^ 2 := by ring
  have hp : 0 < 4 * (-c2) * (z - (c0 + c1 * u + c2 * u ^ 2)) := by
    linarith only [hprice,hsq,hid]
  have hcoef : 0 < 4 * (-c2) := by linarith only [hc2]
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hcoef).mp hp)

theorem fiber_profile_endpoint_nonnegative_cap {F z : ℝ} (hz : 0 ≤ z) (hF : F ≤ z) :
    max 0 F ≤ z := max_le hz hF

theorem fiber_convex_chord {f : ℝ → ℝ} {l h t zl zh : ℝ}
    (hlh : l < h) (ht : t ∈ Icc l h) (hf : ConvexOn ℝ (Icc l h) f)
    (hl : f l ≤ zl) (hh : f h ≤ zh) :
    f t ≤ (h - t) / (h - l) * zl + (t - l) / (h - l) * zh := by
  have hd : 0 < h - l := sub_pos.mpr hlh
  have hw1 : 0 ≤ (h - t) / (h - l) := div_nonneg (sub_nonneg.mpr ht.2) hd.le
  have hw2 : 0 ≤ (t - l) / (h - l) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hsum : (h - t) / (h - l) + (t - l) / (h - l) = 1 := by
    field_simp [hd.ne']
    ring
  have harg : (h - t) / (h - l) * l + (t - l) / (h - l) * h = t := by
    field_simp [hd.ne']
    ring
  have hc := hf.2 ⟨le_refl _,hlh.le⟩ ⟨hlh.le,le_refl _⟩ hw1 hw2 hsum
  simp only [smul_eq_mul,harg] at hc
  exact hc.trans (add_le_add (mul_le_mul_of_nonneg_left hl hw1)
    (mul_le_mul_of_nonneg_left hh hw2))

theorem fiber_chord_printed_identity {l h t zl zh : ℝ} (hlh : l < h) (hz : zh < zl) :
    (h - t) / (h - l) * zl + (t - l) / (h - l) * zh =
      ((zl - zh) / (h - l)) * (l + zl / ((zl - zh) / (h - l)) - t) := by
  have hd : h - l ≠ 0 := (sub_pos.mpr hlh).ne'
  have hz' : zl - zh ≠ 0 := (sub_pos.mpr hz).ne'
  field_simp [hd,hz']
  ring

theorem fiber_convex_weighted_chord {f : ℝ → ℝ} {l h t zl zh k v : ℝ}
    (hlh : l < h) (ht : t ∈ Icc l h) (hz : zh < zl)
    (hf : ConvexOn ℝ (Icc l h) f) (hl : f l ≤ zl) (hh : f h ≤ zh) :
    Real.exp (k * t - v) * f t ≤
      fiberWeightedChord ((zl - zh) / (h - l))
        (l + zl / ((zl - zh) / (h - l))) k v t := by
  have hb := mul_le_mul_of_nonneg_left (fiber_convex_chord hlh ht hf hl hh)
    (Real.exp_pos (k * t - v)).le
  rw [fiber_chord_printed_identity hlh hz] at hb
  unfold fiberWeightedChord
  convert hb using 1 <;> ring

end Erdos993Lean.Analytic.V213
