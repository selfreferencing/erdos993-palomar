module

public import Mathlib
public import Erdos993Lean.Zhang.Decomposition
public import Erdos993Lean.Analytic.Tail.PerUnit

/-!
# The tail input T3, part 13: the Laplace identity (item E2), proved

Source: T23 §1 ("Laplace:
`E(1 − q + q t)^M = E t^{K_B} = Z_F(λ on C, λ t on B)/Z_F`") and Zhang (45).

`laplaceIdentity : LaplaceIdentity` discharges the named proposition used by the mixture forms
`laplace_fallback`, `t3_reduction`, `t31_reduction`.  Proof: the weighted form of Zhang's
decomposition (`Zw_lapW_decomposition`: an independent `S` splits uniquely as `J ∪ K` with
`J = S \ B` independent and `K ⊆ avail(J)`, `Erdos993Lean/Zhang/Decomposition.lean`) gives
`Z(λ on C, λ z on B) = ∑_J λ^{|J|} (1 + λ z)^{M(J)}`, and in the mixture
`λ^{|J|} (1 + λ)^{M} (1 − q + q z)^{M} = λ^{|J|} (1 + λ z)^{M}` since `(1 + λ)(1 − q + q z) = 1 + λ z`.

Corollaries: `laplace_fallback'`, `t3_reduction'`, `t31_reduction'` — the mixture forms from
`WeightIdentity` alone (the field `weight_eq` of `MixtureFacts`).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The weighted Zhang decomposition**: for an independent `B ⊆ s`,
`Z(t on C, t z on B)(s) = ∑_J t^{|J|} (1 + t z)^{|avail(J)|}` over the independent `J ⊆ s \ B`. -/
theorem Zw_lapW_decomposition {B s : Finset V} (hB : IsIndepFinset G B) (hBs : B ⊆ s) (t z : ℝ) :
    Zw G (lapW B t z) s = ∑ J ∈ (s \ B).powerset.filter (IsIndepFinset G),
      t ^ J.card * (1 + t * z) ^ (Zhang.avail G B J).card := by
  unfold Zw
  have hmaps : ∀ S ∈ s.powerset.filter (IsIndepFinset G),
      (fun S => S \ B) S ∈ (s \ B).powerset.filter (IsIndepFinset G) := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨Finset.sdiff_subset_sdiff hS.1 subset_rfl,
      Zhang.isIndepFinset_mono hS.2 Finset.sdiff_subset⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ
  obtain ⟨hJs, hJi⟩ := hJ
  have hpow : (1 + t * z) ^ (Zhang.avail G B J).card =
      ∑ K ∈ (Zhang.avail G B J).powerset, (t * z) ^ K.card := by
    have h := Finset.sum_pow_mul_eq_add_pow (t * z) 1 (Zhang.avail G B J)
    simp only [one_pow, mul_one] at h
    rw [h, add_comm]
  rw [hpow, Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun K => J ∪ K) (fun S => S ∩ B) ?_ ?_ ?_ ?_ ?_
  · intro K hK
    rw [Finset.mem_powerset] at hK
    have hKI : K ⊆ B := hK.trans (Zhang.avail_subset G B J)
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨Finset.union_subset (hJs.trans Finset.sdiff_subset) (hKI.trans hBs),
      Zhang.isIndepFinset_union_avail hB hJi hK⟩, (Zhang.decomposition_unique hJs hKI).1⟩
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨⟨_, hSi⟩, hSJ⟩ := hS
    rw [Finset.mem_powerset]
    have h := Zhang.inter_subset_avail (I := B) hSi
    rw [hSJ] at h
    exact h
  · intro K hK
    rw [Finset.mem_powerset] at hK
    exact (Zhang.decomposition_unique hJs (hK.trans (Zhang.avail_subset G B J))).2
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_filter] at hS
    rw [← hS.2]
    exact Finset.sdiff_union_inter S B
  · intro K hK
    rw [Finset.mem_powerset] at hK
    have hKB : K ⊆ B := hK.trans (Zhang.avail_subset G B J)
    have hdisj : Disjoint J K := by
      rw [Finset.disjoint_left]
      intro x hxJ hxK
      exact (Finset.mem_sdiff.mp (hJs hxJ)).2 (hKB hxK)
    have h1 : ∏ v ∈ J, lapW B t z v = t ^ J.card := by
      rw [Finset.prod_congr rfl (fun v hv => (show lapW B t z v = t by
        unfold lapW
        rw [if_neg (Finset.mem_sdiff.mp (hJs hv)).2])), Finset.prod_const]
    have h2 : ∏ v ∈ K, lapW B t z v = (t * z) ^ K.card := by
      rw [Finset.prod_congr rfl (fun v hv => (show lapW B t z v = t * z by
        unfold lapW
        rw [if_pos (hKB hv)])), Finset.prod_const]
    rw [Finset.prod_union hdisj, h1, h2]

/-- **The Laplace identity** (T23 §1; item E2):
`E[(1 − q + q z)^M] = (∑_{S indep} t^{|S \ B|} (t z)^{|S ∩ B|}) / Z_F(t)`. -/
theorem laplaceIdentity : LaplaceIdentity := by
  intro F B t z ht hB
  classical
  have hBf := isIndepFinset_of_isIndepSet hB
  rw [lapSum_eq_Zw, Zw_lapW_decomposition hBf (Finset.subset_univ B), Finset.sum_div]
  simp only [Mixture.expect, forestMixture]
  apply Finset.sum_congr
  · ext σ
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, isIndepFinset_of_isIndepSet h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun v hv w hw _ => h2 v hv w hw⟩
  · intro σ _
    have hfree : freeCount F B σ = (Zhang.avail F.graph B σ).card := by
      unfold freeCount
      congr 1
      ext b
      simp only [Finset.mem_filter, Zhang.mem_avail]
      constructor
      · rintro ⟨hb, h⟩
        exact ⟨hb, fun y hy hyb => h y hy hyb.symm⟩
      · rintro ⟨hb, h⟩
        exact ⟨hb, fun c hc hbc => h c hc hbc.symm⟩
    have h1t : (1 + t) * actQ t = t := by
      unfold actQ
      field_simp
    have hq : (1 + t) * (1 - actQ t + actQ t * z) = 1 + t * z := by
      calc (1 + t) * (1 - actQ t + actQ t * z) =
          (1 + t) - (1 + t) * actQ t + (1 + t) * actQ t * z := by ring
        _ = 1 + t * z := by rw [h1t]; ring
    rw [hfree, ← hq, mul_pow]
    ring

/-- **The fallback (mixture form), needing only `q m = W`.** -/
theorem laplace_fallback' (hW : WeightIdentity) (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t z : ℝ} (ht : 0 < t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) :
    (forestMixture F B t).expect (fun M _ => (1 - actQ t + actQ t * z) ^ M) ≤
      Real.exp (-(actQ t * (1 - actQ t) * rFallback t z) * (forestMixture F B t).meanM) :=
  laplace_fallback laplaceIdentity hW F B hB ht hz0 hz1

/-- **Theorem T3-2 (repaired, mixture form), needing only `q m = W`.** -/
theorem t3_reduction' (hW : WeightIdentity) (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (hleaf : LeafCondition F.graph B)
    {lam z a ell : ℝ} (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (ha : 0 ≤ a) (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z)))
    (hU : T3UNonneg lam z a ell) :
    (forestMixture F B lam).expect (fun M _ => (1 - actQ lam + actQ lam * z) ^ M) ≤
      Real.exp (-ell * (forestMixture F B lam).meanM) :=
  t3_reduction laplaceIdentity hW F B hB hleaf hlam0 hlam6 hz0 hz1 ha hiso hU

/-- **Theorem T3-1 (per-unit form, mixture form), needing only `q m = W`.** -/
theorem t31_reduction' (hW : WeightIdentity) (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {lam z ell : ℝ} (hlam0 : 0 < lam)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hR : PerUnitRate lam z ell) :
    (forestMixture F B lam).expect (fun M _ => (1 - actQ lam + actQ lam * z) ^ M) ≤
      Real.exp (-ell * (forestMixture F B lam).meanM) :=
  t31_reduction laplaceIdentity hW F B hB hlam0 hz0 hz1 hell hiso hR

end Erdos993Lean.Analytic.Tail
