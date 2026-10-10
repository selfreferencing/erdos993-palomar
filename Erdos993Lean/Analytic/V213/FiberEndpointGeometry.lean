module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

/-!
Endpoint principle calculus. A convex weighted derivative that is
nonpositive at the right endpoint forces a function's minimum to occur at
an endpoint. Both endpoint and degenerate-interval cases are retained.
The literal root-function specialization is a separate consumer.
No generated data or paper theorem is assumed here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Set

theorem fiber_endpoint_minimum_of_convex_weighted_derivative
    {a b t : ℝ} {f K : ℝ → ℝ} (ht : t ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b)) (hK : ConvexOn ℝ (Icc a b) K)
    (hKb : K b ≤ 0)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (K x / x ^ 2) x) :
    min (f a) (f b) ≤ f t := by
  have hab : a ≤ b := ht.1.trans ht.2
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  by_cases hKt : K t ≤ 0
  · have hneg : ∀ x ∈ Icc t b, K x ≤ 0 := by
      intro x hx
      exact (hK.le_max_of_mem_Icc ht hb hx).trans (max_le hKt hKb)
    have hsub : Icc t b ⊆ Icc a b := by
      intro x hx
      exact ⟨ht.1.trans hx.1, hx.2⟩
    have hanti : AntitoneOn f (Icc t b) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t b) (hf.mono hsub)
        (fun x hx => by
          have hx' : x ∈ Ioo t b := by simpa only [interior_Icc] using hx
          exact (hd x ⟨lt_of_le_of_lt ht.1 hx'.1, hx'.2⟩).hasDerivWithinAt)
        (fun x hx => by
          have hx' : x ∈ Ioo t b := by simpa only [interior_Icc] using hx
          exact div_nonpos_of_nonpos_of_nonneg (hneg x ⟨hx'.1.le, hx'.2.le⟩) (sq_nonneg x))
    exact (min_le_right _ _).trans (hanti ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩ ht.2)
  · have hKtpos : 0 < K t := lt_of_not_ge hKt
    have hpos : ∀ x ∈ Icc a t, 0 ≤ K x := by
      intro x hx
      by_contra h
      have hx0 : K x ≤ 0 := (lt_of_not_ge h).le
      have hxAB : x ∈ Icc a b := ⟨hx.1, hx.2.trans ht.2⟩
      have hbound := hK.le_max_of_mem_Icc hxAB hb ⟨hx.2, ht.2⟩
      have hmax : max (K x) (K b) ≤ 0 := max_le hx0 hKb
      linarith
    have hsub : Icc a t ⊆ Icc a b := by
      intro x hx
      exact ⟨hx.1, hx.2.trans ht.2⟩
    have hmono : MonotoneOn f (Icc a t) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a t) (hf.mono hsub)
        (fun x hx => by
          have hx' : x ∈ Ioo a t := by simpa only [interior_Icc] using hx
          exact (hd x ⟨hx'.1, lt_of_lt_of_le hx'.2 ht.2⟩).hasDerivWithinAt)
        (fun x hx => by
          have hx' : x ∈ Ioo a t := by simpa only [interior_Icc] using hx
          exact div_nonneg (hpos x ⟨hx'.1.le, hx'.2.le⟩) (sq_nonneg x))
    exact (min_le_left _ _).trans (hmono ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1)

end Erdos993Lean.Analytic.V213
