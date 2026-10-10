module

public import Erdos993Lean.Analytic.V213.LowMeanHeat

/-!
The chord, tangent, and quadratic support arguments used in
Lemma 6.6 of version 2.13 of the manuscript (`r12:lem13`). The generic lemmas include endpoint anchors.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_convex_tangent {f : ℝ → ℝ} {L H tau x d : ℝ}
    (hf : ConvexOn ℝ (Set.Icc L H) f) (htau : tau ∈ Set.Icc L H)
    (hx : x ∈ Set.Icc L H) (hd : HasDerivAt f d tau) :
    f tau + d * (x - tau) ≤ f x := by
  rcases lt_trichotomy tau x with h | rfl | h
  · have hs := hf.le_slope_of_hasDerivAt htau hx h hd
    rw [slope_def_field] at hs
    have hh := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    linarith
  · simp
  · have hs := hf.slope_le_of_hasDerivAt hx htau h hd
    rw [slope_def_field] at hs
    have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

theorem lowMean_concave_chord {f : ℝ → ℝ} {L H x : ℝ}
    (hLH : L < H) (hf : ConcaveOn ℝ (Set.Icc L H) f) (hx : x ∈ Set.Icc L H) :
    (H - x) / (H - L) * f L + (x - L) / (H - L) * f H ≤ f x := by
  have hd : 0 < H - L := sub_pos.mpr hLH
  have ha : 0 ≤ (H - x) / (H - L) := div_nonneg (sub_nonneg.mpr hx.2) hd.le
  have hb : 0 ≤ (x - L) / (H - L) := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hab : (H - x) / (H - L) + (x - L) / (H - L) = 1 := by field_simp; ring
  have he : (H - x) / (H - L) * L + (x - L) / (H - L) * H = x := by field_simp; ring
  have hh := hf.2 (show L ∈ Set.Icc L H from ⟨le_rfl, hLH.le⟩)
    (show H ∈ Set.Icc L H from ⟨hLH.le, le_rfl⟩) ha hb hab
  simpa only [smul_eq_mul, he] using hh

/-- A lower bound on the second derivative gives a quadratic support at any
anchor, including either closed endpoint. -/
theorem lowMean_quadratic_support {f f' f'' : ℝ → ℝ} {L H tau x Lambda : ℝ}
    (hf : ContinuousOn f (Set.Icc L H))
    (hd : ∀ q ∈ Set.Icc L H, HasDerivAt f (f' q) q)
    (hdd : ∀ q ∈ Set.Icc L H, HasDerivAt f' (f'' q) q)
    (hbound : ∀ q ∈ Set.Icc L H, Lambda ≤ f'' q)
    (htau : tau ∈ Set.Icc L H) (hx : x ∈ Set.Icc L H) :
    f tau + f' tau * (x - tau) + Lambda / 2 * (x - tau) ^ 2 ≤ f x := by
  let g : ℝ → ℝ := fun q => f q - Lambda / 2 * (q - tau) ^ 2
  let g' : ℝ → ℝ := fun q => f' q - Lambda * (q - tau)
  let g'' : ℝ → ℝ := fun q => f'' q - Lambda
  have hgd (q : ℝ) (hq : q ∈ Set.Icc L H) : HasDerivAt g (g' q) q := by
    convert (hd q hq).sub ((((hasDerivAt_id q).sub_const tau).pow 2).const_mul (Lambda / 2)) using 1
    · rfl
    · dsimp [g']
      ring
  have hgdd (q : ℝ) (hq : q ∈ Set.Icc L H) : HasDerivAt g' (g'' q) q := by
    convert (hdd q hq).sub (((hasDerivAt_id q).sub_const tau).const_mul Lambda) using 1
    · rfl
    · dsimp [g'']
      ring
  have hgc : ConvexOn ℝ (Set.Icc L H) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc L H)
      (hf.sub (by fun_prop))
      (fun q hq => (hgd q (interior_subset hq)).hasDerivWithinAt)
      (fun q hq => (hgdd q (interior_subset hq)).hasDerivWithinAt)
    intro q hq
    exact sub_nonneg.mpr (hbound q (interior_subset hq))
  have ht := lowMean_convex_tangent hgc htau hx (hgd tau htau)
  dsimp [g, g'] at ht
  nlinarith

/-- The signed-curvature estimate in the mixed-sign case of Lemma 6.6.
It retains the direction of both inequalities when p is negative. -/
theorem lowMean_curvature_bound {u s v vmin p R : ℝ}
    (hu : 0 ≤ u) (huR : u ≤ R) (hp : p ≤ 0) (hps : p ≤ s)
    (hvmin : 0 < vmin) (hv : vmin ≤ v) :
    p * R / vmin ^ 2 ≤ u * s / v ^ 2 := by
  have hR : 0 ≤ R := le_trans hu huR
  have hvpos : 0 < v := lt_of_lt_of_le hvmin hv
  have hnum : p * R ≤ u * s := by
    have h1 := mul_le_mul_of_nonpos_left huR hp
    have h2 := mul_le_mul_of_nonneg_left hps hu
    nlinarith
  have hsq : vmin ^ 2 ≤ v ^ 2 := by nlinarith
  have hnum0 : p * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hR
  have h1 := mul_le_mul_of_nonpos_left hsq hnum0
  have h2 := mul_le_mul_of_nonneg_right hnum (sq_nonneg vmin)
  apply (div_le_div_iff₀ (sq_pos_of_pos hvmin) (sq_pos_of_pos hvpos)).mpr
  nlinarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_convex_tangent
#print axioms Erdos993Lean.Analytic.V213.lowMean_concave_chord
#print axioms Erdos993Lean.Analytic.V213.lowMean_quadratic_support
#print axioms Erdos993Lean.Analytic.V213.lowMean_curvature_bound
