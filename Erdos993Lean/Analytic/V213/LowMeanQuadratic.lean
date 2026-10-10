module

public import Erdos993Lean.Analytic.V213.LowMeanHeat

/-!
Exact quadratic extrema on a closed interval, used for Pi in Lemma
6.6 and for the budget minimum in `r12:eq59`, version 2.13 of the manuscript.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanQuad (A B C x : ℝ) : ℝ := A * x ^ 2 + B * x + C

theorem lowMeanQuad_vertex (A B C : ℝ) (hA : A ≠ 0) :
    lowMeanQuad A B C (-B / (2 * A)) = C - B ^ 2 / (4 * A) := by
  unfold lowMeanQuad
  field_simp
  ring

/-- Endpoint tests and an interior positive-curvature vertex test suffice
for a quadratic lower bound. The interval is closed. -/
theorem lowMeanQuad_lower {A B C L H bound : ℝ} (hLH : L < H)
    (hL : bound ≤ lowMeanQuad A B C L) (hH : bound ≤ lowMeanQuad A B C H)
    (hvertex : 0 < A → L ≤ -B / (2 * A) → -B / (2 * A) ≤ H →
      bound ≤ lowMeanQuad A B C (-B / (2 * A)))
    {x : ℝ} (hx : x ∈ Set.Icc L H) : bound ≤ lowMeanQuad A B C x := by
  by_cases hA : 0 < A
  · let v := -B / (2 * A)
    have hs : 2 * A * v + B = 0 := by dsimp [v]; field_simp; ring
    by_cases hvL : v < L
    · have hdx : 0 ≤ x - L := sub_nonneg.mpr hx.1
      have hsL : 0 ≤ 2 * A * L + B := by nlinarith
      have hfactor : 0 ≤ A * (x + L) + B := by nlinarith
      have hp := mul_nonneg hdx hfactor
      unfold lowMeanQuad at hL ⊢
      nlinarith
    · by_cases hvH : H < v
      · have hdx : x - H ≤ 0 := sub_nonpos.mpr hx.2
        have hsH : 2 * A * H + B ≤ 0 := by nlinarith
        have hfactor : A * (x + H) + B ≤ 0 := by nlinarith
        have hp := mul_nonneg_of_nonpos_of_nonpos hdx hfactor
        unfold lowMeanQuad at hH ⊢
        nlinarith
      · have hv := hvertex hA (le_of_not_gt hvL) (le_of_not_gt hvH)
        have he : lowMeanQuad A B C x - lowMeanQuad A B C v = A * (x - v) ^ 2 := by
          unfold lowMeanQuad
          linear_combination (x - v) * hs
        have hp := mul_nonneg hA.le (sq_nonneg (x - v))
        change bound ≤ lowMeanQuad A B C v at hv
        linarith
  · have hA' : A ≤ 0 := le_of_not_gt hA
    have h1 := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hL)
    have h2 := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hH)
    have h3 := mul_nonneg (mul_nonneg (neg_nonneg.mpr hA') (sub_nonneg.mpr hLH.le))
      (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))
    have he : (H - L) * (lowMeanQuad A B C x - bound) =
        (H - x) * (lowMeanQuad A B C L - bound) +
        (x - L) * (lowMeanQuad A B C H - bound) + (-A) * (H - L) * ((x - L) * (H - x)) := by
      unfold lowMeanQuad
      ring
    nlinarith

/-- The upper-bound counterpart uses the vertex only for negative curvature. -/
theorem lowMeanQuad_upper {A B C L H bound : ℝ} (hLH : L < H)
    (hL : lowMeanQuad A B C L ≤ bound) (hH : lowMeanQuad A B C H ≤ bound)
    (hvertex : A < 0 → L ≤ -B / (2 * A) → -B / (2 * A) ≤ H →
      lowMeanQuad A B C (-B / (2 * A)) ≤ bound)
    {x : ℝ} (hx : x ∈ Set.Icc L H) : lowMeanQuad A B C x ≤ bound := by
  have he (y : ℝ) : lowMeanQuad (-A) (-B) (-C) y = -lowMeanQuad A B C y := by
    unfold lowMeanQuad
    ring
  have hv : -(-B) / (2 * (-A)) = -B / (2 * A) := by ring
  have hh := lowMeanQuad_lower (A := -A) (B := -B) (C := -C) (bound := -bound) hLH
    (by rw [he]; linarith) (by rw [he]; linarith) (fun hA hvl hvh => ?_) hx
  · rw [he] at hh
    linarith
  · rw [hv] at hvl hvh ⊢
    rw [he]
    exact neg_le_neg (hvertex (by linarith) hvl hvh)

/-- The exact minimum printed in equation r12:eq59. -/
noncomputable def lowMeanQuadMinimum (A B C L H : ℝ) : ℝ :=
  min (lowMeanQuad A B C L) (min (lowMeanQuad A B C H)
    (if 0 < A ∧ L ≤ -B / (2 * A) ∧ -B / (2 * A) ≤ H
     then C - B ^ 2 / (4 * A) else lowMeanQuad A B C L))

theorem lowMeanQuadMinimum_le {A B C L H : ℝ} (hLH : L < H)
    {x : ℝ} (hx : x ∈ Set.Icc L H) :
    lowMeanQuadMinimum A B C L H ≤ lowMeanQuad A B C x := by
  apply lowMeanQuad_lower hLH
    (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)) ?_ hx
  intro hA hL hH
  rw [ite_eq_left ⟨hA, hL, hH⟩, lowMeanQuad_vertex A B C hA.ne']
  exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem lowMeanQuadMinimum_attained {A B C L H : ℝ} (hLH : L < H) :
    ∃ x ∈ Set.Icc L H, lowMeanQuad A B C x = lowMeanQuadMinimum A B C L H := by
  let v := -B / (2 * A)
  have hLmem : L ∈ Set.Icc L H := ⟨le_rfl, hLH.le⟩
  have hHmem : H ∈ Set.Icc L H := ⟨hLH.le, le_rfl⟩
  unfold lowMeanQuadMinimum
  by_cases hv : 0 < A ∧ L ≤ v ∧ v ≤ H
  · rw [ite_eq_left hv, ← lowMeanQuad_vertex A B C hv.1.ne']
    rcases le_total (lowMeanQuad A B C H) (lowMeanQuad A B C v) with hHv | hvH
    · rw [min_eq_left hHv]
      rcases le_total (lowMeanQuad A B C L) (lowMeanQuad A B C H) with hLH' | hHL'
      · exact ⟨L, hLmem, (min_eq_left hLH').symm⟩
      · exact ⟨H, hHmem, (min_eq_right hHL').symm⟩
    · rw [min_eq_right hvH]
      rcases le_total (lowMeanQuad A B C L) (lowMeanQuad A B C v) with hLv | hvL
      · exact ⟨L, hLmem, (min_eq_left hLv).symm⟩
      · exact ⟨v, ⟨hv.2.1, hv.2.2⟩, (min_eq_right hvL).symm⟩
  · rw [ite_eq_right hv, min_left_comm, min_self]
    rcases le_total (lowMeanQuad A B C H) (lowMeanQuad A B C L) with hHL | hLH'
    · exact ⟨H, hHmem, (min_eq_left hHL).symm⟩
    · exact ⟨L, hLmem, (min_eq_right hLH').symm⟩

/-- The variance q(1-q) has its minimum at an interval endpoint. -/
theorem lowMean_variance_min {L H q : ℝ} (hLH : L < H) (hq : q ∈ Set.Icc L H) :
    min (L * (1 - L)) (H * (1 - H)) ≤ q * (1 - q) := by
  have hh := lowMeanQuad_lower (A := -1) (B := 1) (C := 0)
    (bound := min (L * (1 - L)) (H * (1 - H))) hLH
    (by dsimp [lowMeanQuad]; nlinarith [min_le_left (L * (1 - L)) (H * (1 - H))])
    (by dsimp [lowMeanQuad]; nlinarith [min_le_right (L * (1 - L)) (H * (1 - H))])
    (by norm_num) hq
  dsimp [lowMeanQuad] at hh
  nlinarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanQuad_lower
#print axioms Erdos993Lean.Analytic.V213.lowMeanQuad_upper
#print axioms Erdos993Lean.Analytic.V213.lowMeanQuadMinimum_le
#print axioms Erdos993Lean.Analytic.V213.lowMeanQuadMinimum_attained
