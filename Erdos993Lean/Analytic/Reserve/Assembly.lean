module

public import Mathlib
public import Erdos993Lean.Analytic.Reserve.Induction
public import Erdos993Lean.Analytic.Reserve.StepBand
public import Erdos993Lean.Analytic.HardCore.Variance
public import Erdos993Lean.Analytic.HardCore.Leaves

/-!
# O1 by the two-generation reserve: the assembly

Sources:
the two-generation reserve proof (leaf exchange, rooting, K1/K2, "At a component root, (R) is a
nonnegative credit ... so Var(K_B) ≤ A W", the conversion `W = q E M`,
`Var K_B = (1 − q) W + q² Var M`), with the sharp first-four and
lower sharp alternate reserves.


For an acyclic graph, an independent set `B` with the leaf property (`LeafProp`: every leaf of a
component of order at least three is selected; `IsMaxWeight.leaf_mem` gives it for every
maximum-weight `B`), and a step certificate at the activity `t`:

* `good_of_component`: in a component with a selected vertex, rooted at an unselected vertex (if
  any), every unselected vertex has a child (this covers K2 with one selected endpoint; a component
  without selected vertices has `U = V = 0`, and a component inside `B` is a single selected vertex,
  the leaf base);
* `varB_le_of_component`: on every component, the reserve (R) at the root and PSD give
  `V ≤ A U`, i.e. `Var K_B ≤ A W` (the reserve is a nonnegative credit);
* `varB_le_of_closed`, `varB_le_univ`: components add (product law), so `V ≤ A U` on every vertex set
  closed under adjacency, in particular on the whole vertex set;
* for a forest: `meanB_univ_eq_weightW` (`U = W`), `varB_univ_eq_varKB` (`V = Var K_B`),
  hence **`varKB_le_of_stepCert`**: `Var K_B ≤ A W`;
* `varM_le_of_varKB_le` (`forestMixture_varM` and `forestMixture_weight_eq`):
  `Var K_B ≤ (1 + (D − 1) q) W` gives `Var M ≤ D E M`; **`varM_le_of_stepCert`** (every reserve with a
  step certificate, including a signed one) and **`varM_le_of_band`** (the bands of
  `Reserve/Defs.lean`, every leaf-containing independent `B`);
* **`bandVar_of_ok`**: `BandSide c → EntropyOK → BoxOK c → TailOK c → LeafOK c → BandVar c`, and
  `bandVar_band0` … `bandVar_band3` (the side conditions of the four bands checked).

Scalarity check.  `U = meanB` and `V = varB` are the mean and variance of the selected count `K_B`
under the actual hard-core law; at the whole vertex set they are `W` and `Var K_B`.  The output `D`
bounds the variance of the free count `M` of the actual `forestMixture`, relative to its mean
`m = E M` (both outputs, consumed by `VarianceBound` and the no-valley lemma O4); `A = 1 + (D − 1) q`
is the same bound in `K_B` form, used only at the component roots.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve

open Finset Erdos993Lean.Analytic.Tail

section Graph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- **The leaf property** (the retained selector field): a vertex `v` whose only neighbour is
`u`, where `u` has another neighbour, is selected; that is, `B` contains every leaf of every component
of order at least three. -/
def LeafProp (B : Finset V) : Prop :=
  ∀ v u : V, G.Adj v u → (∀ x, G.Adj v x → x = u) → (∃ w, G.Adj u w ∧ w ≠ v) → v ∈ B

/-- **The rooting**: in a component `K` (connected, closed under adjacency) with a selected vertex
`b`, rooted at an unselected vertex `r`, every unselected vertex has a child. -/
theorem good_of_component {B : Finset V} (hleaf : LeafProp G B) {K : Finset V}
    (hK : ConnectedIn G K) (hKc : ∀ v ∈ K, ∀ w, G.Adj v w → w ∈ K) {r b : V} (hr : r ∈ K)
    (hrB : r ∉ B) (hb : b ∈ K) (hbB : b ∈ B) : Good G B K r := by
  intro v hv hvB
  refine ⟨fun _ => nbrsIn_nonempty_of_ne hK hv hb (by rintro rfl; exact hvB hbB), fun hvr => ?_⟩
  by_contra hcard
  push_neg at hcard
  obtain ⟨u, hu⟩ := nbrsIn_nonempty_of_ne hK hv hr hvr
  have hvu : G.Adj v u := (mem_nbrsIn.mp hu).2
  -- `v` is a leaf with neighbour `u`
  have hone : ∀ x, G.Adj v x → x = u := by
    intro x hvx
    have hx : x ∈ nbrsIn G K v := mem_nbrsIn.mpr ⟨hKc v hv x hvx, hvx⟩
    exact Finset.card_le_one.mp hcard x hx u hu
  -- `v` is unselected, so `u` has no other neighbour
  have huv : ∀ w, G.Adj u w → w = v := by
    intro w huw
    by_contra hwv
    exact hvB (hleaf v u hvu hone ⟨w, huw, hwv⟩)
  -- then the component is the edge `{u, v}`, which contains no selected vertex: contradiction
  have hsub : K ⊆ {u, v} := by
    refine subset_of_closed hK hv (by simp) fun y hy z hyz => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl
    · exact Or.inr (huv z hyz)
    · exact Or.inl (hone z hyz)
  have hr' := hsub hr
  have hb' := hsub hb
  rw [Finset.mem_insert, Finset.mem_singleton] at hr' hb'
  rcases hr' with hru | hrv
  · rcases hb' with hbu | hbv
    · exact hrB (hru.trans hbu.symm ▸ hbB)
    · exact hvB (hbv ▸ hbB)
  · exact hvr hrv.symm

/-- **The root conclusion on a component**: for a component `K` (connected, closed under adjacency)
of an acyclic graph, an independent `B` with the leaf property and a step certificate,
`V(K) ≤ A U(K)`. -/
theorem varB_le_of_component (hG : G.IsAcyclic) {B : Finset V} (hB : IsIndepFinset G B)
    (hleaf : LeafProp G B) {t α β γ A : ℝ} (hcert : StepCert γ t α β A) {K : Finset V}
    (hK : ConnectedIn G K) (hKc : ∀ v ∈ K, ∀ w, G.Adj v w → w ∈ K) :
    varB G B t K ≤ A * meanB G B t K := by
  have ht := hcert.lam_pos
  by_cases hKB : Disjoint K B
  · rw [varB_of_disjoint hKB, meanB_of_disjoint hKB, mul_zero]
  · obtain ⟨b, hbK, hbB⟩ := Finset.not_disjoint_iff.mp hKB
    obtain ⟨r, hr, hgood⟩ : ∃ r ∈ K, Good G B K r := by
      by_cases hex : ∃ r ∈ K, r ∉ B
      · obtain ⟨r, hr, hrB⟩ := hex
        exact ⟨r, hr, good_of_component hleaf hK hKc hr hrB hbK hbB⟩
      · push_neg at hex
        exact ⟨b, hbK, fun v hv hvB => absurd (hex v hv) hvB⟩
    have hR := reserveAt_of_good hG hB hcert K r hK hr hgood
    have hy := yLog_pos hG ht hK hr
    have h0 := reserve_nonneg (u := port G B t K r) hcert.gamma_pos hy hcert.psd
    unfold ReserveAt resF at hR
    linarith

/-- **`V ≤ A U` on every vertex set closed under adjacency** (components add). -/
theorem varB_le_of_closed (hG : G.IsAcyclic) {B : Finset V} (hB : IsIndepFinset G B)
    (hleaf : LeafProp G B) {t α β γ A : ℝ} (hcert : StepCert γ t α β A) :
    ∀ s : Finset V, (∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s) → varB G B t s ≤ A * meanB G B t s := by
  have ht := hcert.lam_pos
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro hsc
  rcases s.eq_empty_or_nonempty with hs0 | ⟨x, hx⟩
  · rw [hs0, varB_empty, meanB_empty, mul_zero]
  · have hKs : compIn G s x ⊆ s := compIn_subset _ _
    have hxK : x ∈ compIn G s x := self_mem_compIn hx
    have hKc : ∀ v ∈ compIn G s x, ∀ w, G.Adj v w → w ∈ compIn G s x := fun v hv w hvw =>
      mem_compIn_of_adjIn hv ⟨hKs hv, hsc v (hKs hv) w hvw, hvw⟩
    have hno : ∀ a ∈ compIn G s x, ∀ b ∈ s \ compIn G s x, ¬ G.Adj a b := by
      intro a ha b hb hab
      rw [Finset.mem_sdiff] at hb
      exact hb.2 (mem_compIn_of_adjIn ha ⟨hKs ha, hb.1, hab⟩)
    have hRc : ∀ v ∈ s \ compIn G s x, ∀ w, G.Adj v w → w ∈ s \ compIn G s x := by
      intro v hv w hvw
      rw [Finset.mem_sdiff] at hv ⊢
      refine ⟨hsc v hv.1 w hvw, fun hwK => hv.2 ?_⟩
      exact mem_compIn_of_adjIn hwK ⟨hKs hwK, hv.1, hvw.symm⟩
    have hK1 := varB_le_of_component hG hB hleaf hcert (connectedIn_compIn s x) hKc
    have hR1 := ih (s \ compIn G s x) (Finset.sdiff_ssubset hKs ⟨x, hxK⟩) hRc
    have hsplit : s = compIn G s x ∪ (s \ compIn G s x) := (Finset.union_sdiff_of_subset hKs).symm
    rw [hsplit, varB_union ht.le Finset.disjoint_sdiff hno,
      meanB_union ht.le Finset.disjoint_sdiff hno]
    linarith

/-- `V ≤ A U` on the whole vertex set of a finite acyclic graph. -/
theorem varB_le_univ [Fintype V] (hG : G.IsAcyclic) {B : Finset V} (hB : IsIndepFinset G B)
    (hleaf : LeafProp G B) {t α β γ A : ℝ} (hcert : StepCert γ t α β A) :
    varB G B t Finset.univ ≤ A * meanB G B t Finset.univ :=
  varB_le_of_closed hG hB hleaf hcert Finset.univ fun _ _ w _ => Finset.mem_univ w

end Graph

/-! ### The forest -/

section Forest

variable (F : FiniteForest)

theorem indepFinset_univ_eq [DecidableRel F.graph.Adj] :
    (Finset.univ : Finset (Fin F.n)).powerset.filter (IsIndepFinset F.graph) = indepSets F := by
  ext S
  rw [Finset.mem_filter, Finset.mem_powerset, HardCore.mem_indepSets']
  simp only [Finset.subset_univ, true_and]
  exact Iff.rfl

theorem momB_univ [DecidableRel F.graph.Adj] (B : Finset (Fin F.n)) (t : ℝ) (k : ℕ) :
    momB F.graph B t k Finset.univ = ∑ S ∈ indepSets F, ((S ∩ B).card : ℝ) ^ k * t ^ S.card := by
  unfold momB
  rw [indepFinset_univ_eq F]

/-- On the whole vertex set, `U` is Zhang's weight `W = ∑_{b ∈ B} π_b`. -/
theorem meanB_univ_eq_weightW [DecidableRel F.graph.Adj] (B : Finset (Fin F.n)) (t : ℝ) :
    meanB F.graph B t Finset.univ = weightW F t B := by
  rw [HardCore.weightW_eq_sum, meanB, momB_univ, momB_univ, HardCore.partitionFn_eq_sum]
  simp only [pow_one, pow_zero, one_mul]

/-- On the whole vertex set, `V` is `Var K_B`. -/
theorem varB_univ_eq_varKB [DecidableRel F.graph.Adj] (B : Finset (Fin F.n)) {t : ℝ}
    (ht : 0 ≤ t) : varB F.graph B t Finset.univ = HardCore.varKB F t B := by
  have hZ := (HardCore.partitionFn_pos F ht).ne'
  have hW := meanB_univ_eq_weightW F B t
  have hM1 : ∑ S ∈ indepSets F, ((S ∩ B).card : ℝ) * t ^ S.card =
      weightW F t B * partitionFn F t := by
    rw [HardCore.weightW_eq_sum, div_mul_cancel₀ _ hZ]
  have hexp : ∑ S ∈ indepSets F, (((S ∩ B).card : ℝ) - weightW F t B) ^ 2 * t ^ S.card =
      ∑ S ∈ indepSets F, ((S ∩ B).card : ℝ) ^ 2 * t ^ S.card -
        2 * weightW F t B * ∑ S ∈ indepSets F, ((S ∩ B).card : ℝ) * t ^ S.card +
        weightW F t B ^ 2 * ∑ S ∈ indepSets F, t ^ S.card := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  unfold HardCore.varKB varB
  rw [hW, hexp, hM1, momB_univ, momB_univ]
  simp only [pow_zero, one_mul]
  rw [← HardCore.partitionFn_eq_sum]
  field_simp
  ring

/-- **`Var K_B ≤ A W`** for every forest, every independent `B` with the leaf property and every
activity with a step certificate. -/
theorem varKB_le_of_stepCert {B : Finset (Fin F.n)} (hB : F.graph.IsIndepSet (B : Set (Fin F.n)))
    (hleaf : LeafProp F.graph B) {t α β γ A : ℝ} (hcert : StepCert γ t α β A) :
    HardCore.varKB F t B ≤ A * weightW F t B := by
  classical
  have ht := hcert.lam_pos
  rw [← varB_univ_eq_varKB F B ht.le, ← meanB_univ_eq_weightW F B t]
  exact varB_le_univ F.isForest ((HardCore.isIndepSet_coe_iff F).mp hB) hleaf hcert

/-- **The conversion** (`forestMixture_varM`, `forestMixture_weight_eq`):
`Var K_B ≤ (1 + (D − 1) q) W` gives `Var M ≤ D E M`. -/
theorem varM_le_of_varKB_le {B : Finset (Fin F.n)} (hB : F.graph.IsIndepSet (B : Set (Fin F.n)))
    {t D : ℝ} (ht : 0 < t) (h : HardCore.varKB F t B ≤ (1 + (D - 1) * actQ t) * weightW F t B) :
    (forestMixture F B t).varM ≤ D * (forestMixture F B t).meanM := by
  have hq := HardCore.actQ_pos ht
  have hW := HardCore.forestMixture_weight_eq F hB ht
  rw [HardCore.forestMixture_varM F hB ht, div_le_iff₀ (pow_pos hq 2), ← hW]
  rw [← hW] at h
  nlinarith [h, hq]

/-- **O1 from a step certificate**: for every forest, every independent `B` with the leaf property
and every activity `t` with a step certificate of cap `A = 1 + (D − 1) q` (any reserve
`α y + β u + γ u²/y`), `Var M ≤ D E M`. -/
theorem varM_le_of_stepCert {B : Finset (Fin F.n)} (hB : F.graph.IsIndepSet (B : Set (Fin F.n)))
    (hleaf : LeafProp F.graph B) {t α β γ D : ℝ}
    (hcert : StepCert γ t α β (1 + (D - 1) * actQ t)) :
    (forestMixture F B t).varM ≤ D * (forestMixture F B t).meanM :=
  varM_le_of_varKB_le F hB hcert.lam_pos (varKB_le_of_stepCert F hB hleaf hcert)

/-- The leaf property of a maximum-weight independent set (`IsMaxWeight.leaf_mem`). -/
theorem leafProp_of_isMaxWeight {t : ℝ} (ht : 0 < t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) : LeafProp F.graph B :=
  fun _ _ hvu hone hnot => (hB.leaf_mem ht hvu hone hnot).2

/-- **O1 on a band, the stronger statement**: for every forest, every activity of the band and
every independent `B` containing every leaf of every component of order at least three,
`Var M ≤ D E M`. -/
theorem varM_le_of_band (c : Band) (hc : BandSide c) (hE : EntropyOK) (hbox : BoxOK c)
    (htail : TailOK c) (hleafOK : LeafOK c) {t : ℝ} (hlo : (c.lo : ℝ) ≤ t) (hhi : t ≤ c.hi)
    {B : Finset (Fin F.n)} (hB : F.graph.IsIndepSet (B : Set (Fin F.n)))
    (hleaf : LeafProp F.graph B) :
    (forestMixture F B t).varM ≤ (c.D : ℝ) * (forestMixture F B t).meanM :=
  varM_le_of_stepCert F hB hleaf (stepCert_of_band hc hE hbox htail hleafOK hlo hhi)

end Forest

/-- **O1 by the two-generation reserve on a band**: given the band's side
conditions and the three numeric obligations (the entropy facts, the finite box, the analytic tails
and the selected-leaf base), `Var M ≤ D E M` for every forest, every activity of the band and every
maximum-weight independent set. -/
theorem bandVar_of_ok (c : Band) (hc : BandSide c) (hE : EntropyOK) (hbox : BoxOK c)
    (htail : TailOK c) (hleaf : LeafOK c) : BandVar c := by
  intro F t hlo hhi B hB
  have ht : 0 < t := lt_of_lt_of_le hc.lo_pos hlo
  exact varM_le_of_band F c hc hE hbox htail hleaf hlo hhi hB.1 (leafProp_of_isMaxWeight F ht hB)

/-! ### The four bands of `Reserve/Defs.lean` -/

/-- O1 on `band0` (`λ ∈ [1/3, 3/5]`, `D = 8/5`) from its numeric obligations. -/
theorem bandVar_band0 (hE : EntropyOK) (hbox : BoxOK band0) (htail : TailOK band0)
    (hleaf : LeafOK band0) : BandVar band0 :=
  bandVar_of_ok band0 (by norm_num [BandSide, band0]) hE hbox htail hleaf

/-- O1 on `band1` (`λ ∈ [3/5, 4/5]`, `D = 7/5`) from its numeric obligations. -/
theorem bandVar_band1 (hE : EntropyOK) (hbox : BoxOK band1) (htail : TailOK band1)
    (hleaf : LeafOK band1) : BandVar band1 :=
  bandVar_of_ok band1 (by norm_num [BandSide, band1]) hE hbox htail hleaf

/-- O1 on `band2` (`λ ∈ [4/5, 13/10]`, `D = 6/5`) from its numeric obligations. -/
theorem bandVar_band2 (hE : EntropyOK) (hbox : BoxOK band2) (htail : TailOK band2)
    (hleaf : LeafOK band2) : BandVar band2 :=
  bandVar_of_ok band2 (by norm_num [BandSide, band2]) hE hbox htail hleaf

/-- O1 on `band3` (`λ ∈ [13/10, 8/5]`, `D = 7/5`) from its numeric obligations. -/
theorem bandVar_band3 (hE : EntropyOK) (hbox : BoxOK band3) (htail : TailOK band3)
    (hleaf : LeafOK band3) : BandVar band3 :=
  bandVar_of_ok band3 (by norm_num [BandSide, band3]) hE hbox htail hleaf

end Erdos993Lean.Analytic.Reserve
