module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.Laplace

/-!
# The tail input T3, part 14: `q m = W` (the field `weight_eq` of `MixtureFacts`), proved

Source: Zhang (46), T23 §1
(`m = E M = W/q`); this is the field `weight_eq` of `MixtureFacts`,
proved here so that the mixture forms of the tail theorems are unconditional.

Proof: with the decomposition `S = J ∪ K` of an independent set (`sum_indep_decomposition`,
`J = S \ B` independent, `K ⊆ avail(J)`), `∑_{b ∈ B} π_b Z = ∑_S |S ∩ B| t^{|S|} =
∑_J t^{|J|} ∑_{K ⊆ avail J} |K| t^{|K|}` and `(1 + t) ∑_{K ⊆ A} |K| t^{|K|} = |A| t (1 + t)^{|A|}`
(`sum_powerset_card_mul_pow`), while `(1 + t) q E M Z = ∑_J t^{|J|} M(J) t (1 + t)^{M(J)}`.

Main results: `weightIdentity : WeightIdentity`, and the unconditional mixture forms
`laplace_fallback_mixture`, `t3_reduction_mixture`, `t31_reduction_mixture`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The decomposition of sums over independent sets**: for an independent `B ⊆ s`,
`∑_{S ⊆ s indep} f(S \ B, S ∩ B) = ∑_{J ⊆ s \ B indep} ∑_{K ⊆ avail(J)} f(J, K)`. -/
theorem sum_indep_decomposition {B s : Finset V} (hB : IsIndepFinset G B) (hBs : B ⊆ s)
    (f : Finset V → Finset V → ℝ) :
    ∑ S ∈ s.powerset.filter (IsIndepFinset G), f (S \ B) (S ∩ B) =
      ∑ J ∈ (s \ B).powerset.filter (IsIndepFinset G),
        ∑ K ∈ (Zhang.avail G B J).powerset, f J K := by
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
    obtain ⟨h1, h2⟩ := Zhang.decomposition_unique hJs (hK.trans (Zhang.avail_subset G B J))
    rw [h1, h2]

/-- `(1 + x) ∑_{K ⊆ A} |K| x^{|K|} = |A| x (1 + x)^{|A|}`. -/
theorem sum_powerset_card_mul_pow (A : Finset V) (x : ℝ) :
    (1 + x) * ∑ K ∈ A.powerset, (K.card : ℝ) * x ^ K.card = (A.card : ℝ) * x * (1 + x) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
    have hc : ∀ K ∈ A.powerset, (insert a K).card = K.card + 1 := fun K hK =>
      Finset.card_insert_of_notMem (fun h => ha (Finset.mem_powerset.mp hK h))
    have hins : ∑ K ∈ A.powerset, ((insert a K).card : ℝ) * x ^ (insert a K).card =
        ∑ K ∈ A.powerset, ((K.card + 1 : ℕ) : ℝ) * x ^ (K.card + 1) :=
      Finset.sum_congr rfl (fun K hK => by rw [hc K hK])
    rw [hins]
    have hP : ∑ K ∈ A.powerset, x ^ K.card = (1 + x) ^ A.card := by
      have h := Finset.sum_pow_mul_eq_add_pow x 1 A
      simp only [one_pow, mul_one] at h
      rw [h, add_comm]
    have hsplit : ∑ K ∈ A.powerset, ((K.card + 1 : ℕ) : ℝ) * x ^ (K.card + 1) =
        x * ∑ K ∈ A.powerset, (K.card : ℝ) * x ^ K.card + x * ∑ K ∈ A.powerset, x ^ K.card := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro K _
      push_cast
      ring
    rw [hsplit, hP]
    push_cast
    linear_combination (1 + x) * ih

/-- **`q m = W`** (Zhang (46); the field `weight_eq` of `MixtureFacts`). -/
theorem weightIdentity : WeightIdentity := by
  intro F t B ht hB
  classical
  have hBf := isIndepFinset_of_isIndepSet hB
  have h1t : (1 + t) ≠ 0 := by linarith
  have hq : actQ t * (1 + t) = t := by
    unfold actQ
    field_simp
  -- the common value `S₀ = ∑_J t^{|J|} M(J) t (1 + t)^{M(J)}`
  set T := (Finset.univ \ B).powerset.filter (IsIndepFinset F.graph) with hT
  set S0 := ∑ J ∈ T, t ^ J.card * (((Zhang.avail F.graph B J).card : ℝ) * t *
    (1 + t) ^ (Zhang.avail F.graph B J).card) with hS0
  -- the hard-core side: `(1 + t) W Z = S₀`
  have hW : (1 + t) * weightW F t B = S0 / partitionFn F t := by
    unfold weightW marginal
    rw [← Finset.sum_div, mul_div_assoc']
    congr 1
    -- swap the sums: `∑_b ∑_{S ∋ b} t^{|S|} = ∑_S |S ∩ B| t^{|S|}`
    have hswap : ∑ b ∈ B, ∑ S ∈ (indepSets F).filter (fun S => b ∈ S), t ^ S.card =
        ∑ S ∈ indepSets F, ((S \ B ∪ S ∩ B) ∩ B).card * t ^ ((S \ B).card + (S ∩ B).card) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.sdiff_union_inter,
        Finset.card_sdiff_add_card_inter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    rw [hswap, indepSets_eq]
    rw [sum_indep_decomposition (f := fun J K => ((J ∪ K) ∩ B).card * t ^ (J.card + K.card)) hBf
      (Finset.subset_univ B)]
    rw [hS0, hT, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [Finset.mem_filter, Finset.mem_powerset] at hJ
    have hJB : ∀ K ∈ (Zhang.avail F.graph B J).powerset, ((J ∪ K) ∩ B).card = K.card := by
      intro K hK
      rw [Finset.mem_powerset] at hK
      rw [(Zhang.decomposition_unique hJ.1 (hK.trans (Zhang.avail_subset F.graph B J))).2]
    rw [Finset.sum_congr rfl (fun K hK => show ((((J ∪ K) ∩ B).card : ℕ) : ℝ) * t ^ (J.card + K.card)
      = t ^ J.card * ((K.card : ℝ) * t ^ K.card) by rw [hJB K hK, pow_add]; ring),
      ← Finset.mul_sum, ← sum_powerset_card_mul_pow]
    ring
  -- the mixture side: `(1 + t) q E M Z = S₀`
  have hM : (1 + t) * (actQ t * (forestMixture F B t).meanM) = S0 / partitionFn F t := by
    simp only [Mixture.meanM, Mixture.expect, forestMixture]
    rw [hS0, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr
    · rw [hT]
      ext σ
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
      rw [hfree]
      calc (1 + t) * (actQ t * (t ^ σ.card * (1 + t) ^ (Zhang.avail F.graph B σ).card /
            partitionFn F t * ((Zhang.avail F.graph B σ).card : ℝ))) =
          (actQ t * (1 + t)) * (t ^ σ.card * (1 + t) ^ (Zhang.avail F.graph B σ).card *
            ((Zhang.avail F.graph B σ).card : ℝ)) / partitionFn F t := by ring
        _ = t ^ σ.card * (((Zhang.avail F.graph B σ).card : ℝ) * t *
            (1 + t) ^ (Zhang.avail F.graph B σ).card) / partitionFn F t := by rw [hq]; ring
  exact mul_left_cancel₀ h1t (hM.trans hW.symm)

/-- **The fallback Laplace bound, mixture form, unconditional.**  For every forest `F`, every
independent set `B`, `t > 0` and `z ∈ [0, 1]`:
`E[(1 − q + q z)^M] ≤ exp(−q (1 − q) r(t, z) m)` for `forestMixture F B t`. -/
theorem laplace_fallback_mixture (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t z : ℝ} (ht : 0 < t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) :
    (forestMixture F B t).expect (fun M _ => (1 - actQ t + actQ t * z) ^ M) ≤
      Real.exp (-(actQ t * (1 - actQ t) * rFallback t z) * (forestMixture F B t).meanM) :=
  laplace_fallback laplaceIdentity weightIdentity F B hB ht hz0 hz1

/-- **Theorem T3-2 (repaired), mixture form**: the only hypothesis left is `T3UNonneg`. -/
theorem t3_reduction_mixture (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (hleaf : LeafCondition F.graph B)
    {lam z a ell : ℝ} (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (ha : 0 ≤ a) (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z)))
    (hU : T3UNonneg lam z a ell) :
    (forestMixture F B lam).expect (fun M _ => (1 - actQ lam + actQ lam * z) ^ M) ≤
      Real.exp (-ell * (forestMixture F B lam).meanM) :=
  t3_reduction laplaceIdentity weightIdentity F B hB hleaf hlam0 hlam6 hz0 hz1 ha hiso hU

/-- **Theorem T3-1 (per-unit form), mixture form**: the only hypothesis left is `PerUnitRate`. -/
theorem t31_reduction_mixture (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {lam z ell : ℝ} (hlam0 : 0 < lam)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hR : PerUnitRate lam z ell) :
    (forestMixture F B lam).expect (fun M _ => (1 - actQ lam + actQ lam * z) ^ M) ≤
      Real.exp (-ell * (forestMixture F B lam).meanM) :=
  t31_reduction laplaceIdentity weightIdentity F B hB hlam0 hz0 hz1 hell hiso hR

end Erdos993Lean.Analytic.Tail
