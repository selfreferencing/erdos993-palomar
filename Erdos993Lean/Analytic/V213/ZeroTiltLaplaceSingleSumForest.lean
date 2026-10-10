module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceLocalForest
public import Erdos993Lean.Analytic.HardCore.Leaves

/-!
The current conditional forest theorem follows from
the new single-sum telescope, including selected/outside singleton components.
The generic marginal and partition-factorization identities are reused, but
no generic completed T3 reduction or paired potential induction is applied.
The literal current unit nonnegativity remains the finite-analytic premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A connected adjacency-closed component, with both singleton cases explicit. -/
theorem component_partition_bound (hG : G.IsAcyclic) {A : Finset V}
    (hA : IsIndepFinset G A) (hleaf : Tail.LeafCondition G A)
    {lam : ℝ} (hd : ActivityDomain lam) (hU : UnitNonnegative lam)
    {K : Finset V} (hK : ConnectedIn G K) (hKcl : Tail.AdjClosed G K)
    {x : V} (hx : x ∈ K) :
    partitionRatio G A lam K ≤
      Real.exp (-(ellH lam/q lam)*(∑ v ∈ K.filter (· ∈ A), Tail.marg G lam K v)) := by
  have hlam : 0 < lam := by linarith [hd.1]
  have hq := q_pos hlam
  by_cases hout : ∃ c ∈ K, c ∉ A
  · obtain ⟨c,hc,hcA⟩ := hout
    by_cases hnt : ∃ y ∈ K, y ≠ c
    · exact rooted_partition_bound hG hA hd hU hK hc hcA
        (Tail.hasChildren_of_leaf hleaf hKcl hK hc hcA hnt)
    · push_neg at hnt
      have heq : K = {c} := by
        ext y
        rw [Finset.mem_singleton]
        exact ⟨fun hy => hnt y hy,fun hy => hy ▸ hc⟩
      rw [heq]
      have hfilt : ({c} : Finset V).filter (· ∈ A) = ∅ := by
        rw [Finset.filter_singleton,if_neg hcA]
      rw [hfilt,Finset.sum_empty,mul_zero,Real.exp_zero,
        partitionRatio_singleton_out A hlam.le hcA]
  · push_neg at hout
    have hKA : K ⊆ A := fun v hv => hout v hv
    have heq := Tail.eq_singleton_of_subset_indep hA hK hKA hx
    have hxA : x ∈ A := hKA hx
    rw [heq]
    have hnil : nbrsIn G {x} x = ∅ := by
      ext y
      simp only [mem_nbrsIn,Finset.mem_singleton,Finset.notMem_empty,iff_false,not_and]
      rintro rfl
      exact G.irrefl
    have hsum : (∑ v ∈ ({x} : Finset V).filter (· ∈ A), Tail.marg G lam {x} v) = q lam := by
      rw [Finset.filter_singleton,if_pos hxA,Finset.sum_singleton,
        Tail.marg_of_mem (Finset.mem_singleton_self x),
        Tail.rootProb_eq_actQ hlam.le (Finset.mem_singleton_self x) hnil]
      rfl
    rw [hsum,neg_mul,div_mul_cancel₀ _ hq.ne',partitionRatio_singleton_in A lam hxA]
    have hden : 0 < 1+lam := by linarith
    have hinv : 1/(1+lam) = Real.exp (-Real.log (1+lam)) := by
      rw [Real.exp_neg,Real.exp_log hden]
      simp only [one_div]
    rw [hinv]
    apply Real.exp_le_exp.mpr
    have hrate : ellH lam ≤ Real.log (1+lam) :=
      (activity_rate_bounds hd).2.1.trans (Tail.actQ_le_log hlam.le)
    linarith

/-- Multiply the component bounds; the empty forest is included. -/
theorem closed_partition_bound (hG : G.IsAcyclic) {A : Finset V}
    (hA : IsIndepFinset G A) (hleaf : Tail.LeafCondition G A)
    {lam : ℝ} (hd : ActivityDomain lam) (hU : UnitNonnegative lam)
    (s : Finset V) (hs : Tail.AdjClosed G s) :
    partitionRatio G A lam s ≤
      Real.exp (-(ellH lam/q lam)*(∑ v ∈ s.filter (· ∈ A), Tail.marg G lam s v)) := by
  have hlam : 0 < lam := by linarith [hd.1]
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hne : s.Nonempty
    · obtain ⟨x,hxs⟩ := hne
      let K := compIn G s x
      have hK : ConnectedIn G K := connectedIn_compIn _ _
      have hxK : x ∈ K := self_mem_compIn hxs
      have hKs : K ⊆ s := compIn_subset _ _
      have hsub : s \ K ⊂ s := Finset.sdiff_ssubset hKs ⟨x,hxK⟩
      have hsplit : s.filter (· ∈ A) = K.filter (· ∈ A) ∪ (s \ K).filter (· ∈ A) := by
        rw [← Finset.filter_union,Finset.union_sdiff_of_subset hKs]
      have hdisj : Disjoint (K.filter (· ∈ A)) ((s \ K).filter (· ∈ A)) :=
        Finset.disjoint_filter_filter Finset.disjoint_sdiff
      have hno1 : ∀ v ∈ K, ∀ w ∈ s \ K, ¬G.Adj v w :=
        fun v hv w hw => Tail.not_adj_compIn_sdiff hv hw
      have hno2 : ∀ v ∈ s \ K, ∀ w ∈ s \ (s \ K), ¬G.Adj v w := by
        intro v hv w hw hvw
        rw [Finset.sdiff_sdiff_eq_self hKs] at hw
        exact hno1 w hw v hv hvw.symm
      have hmass : (∑ v ∈ s.filter (· ∈ A), Tail.marg G lam s v) =
          (∑ v ∈ K.filter (· ∈ A), Tail.marg G lam K v)+
            ∑ v ∈ (s \ K).filter (· ∈ A), Tail.marg G lam (s \ K) v := by
        rw [hsplit,Finset.sum_union hdisj]
        congr 1
        · exact Finset.sum_congr rfl
            (fun v hv => Tail.marg_of_closed hlam.le hKs hno1 (Finset.mem_filter.mp hv).1)
        · exact Finset.sum_congr rfl
            (fun v hv => Tail.marg_of_closed hlam.le Finset.sdiff_subset hno2
              (Finset.mem_filter.mp hv).1)
      rw [partitionRatio_component A s lam x,hmass,mul_add,Real.exp_add]
      have hnonneg : 0 ≤ partitionRatio G A lam (s \ K) := by
        rw [partitionRatio_eq_phiF]
        exact Tail.phiF_nonneg hlam.le le_rfl _
      exact mul_le_mul
        (component_partition_bound hG hA hleaf hd hU hK (Tail.adjClosed_compIn hs x) hxK)
        (ih _ hsub (Tail.adjClosed_sdiff hs x)) hnonneg (Real.exp_pos _).le
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he,partitionRatio_empty,Finset.filter_empty,Finset.sum_empty,mul_zero,Real.exp_zero]

/-- Current Lemma 4.3 via the displayed product plus the single telescope. -/
theorem single_sum_forest_conditional (F : FiniteForest) (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) (hleaf : Tail.LeafCondition F.graph A)
    {lam : ℝ} (hd : ActivityDomain lam) (hU : UnitNonnegative lam) :
    (forestMixture F A lam).expect (fun M _ => (1-q lam)^M) ≤
      Real.exp (-ellH lam*(forestMixture F A lam).meanM) := by
  classical
  have hlam : 0 < lam := by linarith [hd.1]
  have hpart := closed_partition_bound F.isForest (Tail.isIndepFinset_of_isIndepSet hA)
    hleaf hd hU Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
  have hfilt : (Finset.univ : Finset (Fin F.n)).filter (· ∈ A) = A := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hweight : weightW F lam A =
      ∑ v ∈ (Finset.univ : Finset (Fin F.n)).filter (· ∈ A), Tail.marg F.graph lam Finset.univ v := by
    rw [hfilt]
    unfold weightW
    exact Finset.sum_congr rfl (fun v _ => Tail.marginal_eq_marg F lam v)
  have hmean : q lam*(forestMixture F A lam).meanM = weightW F lam A :=
    Tail.weightIdentity F lam A hlam hA
  have hLap : (forestMixture F A lam).expect (fun M _ => (1-q lam)^M) =
      partitionRatio F.graph A lam Finset.univ := by
    have hh := Tail.laplaceIdentity F A lam 0 hlam hA
    rw [Tail.lapSum_eq_Zw,Tail.partitionFn_eq_Zw] at hh
    rw [partitionRatio_eq_phiF]
    simpa only [mul_zero,add_zero,Tail.phiF,q_eq_actQ] using hh
  rw [hLap]
  have hexp : -(ellH lam/q lam)*
      (∑ v ∈ (Finset.univ : Finset (Fin F.n)).filter (· ∈ A), Tail.marg F.graph lam Finset.univ v) =
      -ellH lam*(forestMixture F A lam).meanM := by
    rw [← hweight,← hmean]
    calc
      -(ellH lam/q lam)*(q lam*(forestMixture F A lam).meanM) =
          -((ellH lam/q lam)*q lam)*(forestMixture F A lam).meanM := by ring
      _ = -ellH lam*(forestMixture F A lam).meanM := by
        rw [div_mul_cancel₀ _ (q_pos hlam).ne']
  rwa [hexp] at hpart

/-- Only the generic leaf/edge structure is reused in this maximum-weight specialization. -/
theorem maxWeight_generic_leaf_condition {F : FiniteForest} {lam : ℝ}
    (hlam : 0 < lam) {A : Finset (Fin F.n)} (hA : IsMaxWeight F lam A) :
    Tail.LeafCondition F.graph A := by
  intro c x hcA hcx
  by_cases h : ∃ y, y ≠ x ∧ F.graph.Adj c y
  · exact Or.inl h
  · right
    have hleaf : ∀ y, F.graph.Adj c y → y = x := fun y hy =>
      by_contra fun hne => h ⟨y,hne,hy⟩
    rcases Erdos993Lean.Analytic.IsMaxWeight.edge_mem (F := F) hlam hA hcx hleaf with ⟨hc,_⟩ | ⟨_,hx⟩
    · exact absurd hc hcA
    · refine ⟨hx,fun y hxy => ?_⟩
      by_contra hyc
      exact hcA (Erdos993Lean.Analytic.IsMaxWeight.leaf_mem (F := F) hlam hA hcx hleaf ⟨y,hxy,hyc⟩).2

theorem single_sum_maxWeight_conditional (F : FiniteForest) (A : Finset (Fin F.n))
    {lam : ℝ} (hd : ActivityDomain lam) (hA : IsMaxWeight F lam A)
    (hU : UnitNonnegative lam) :
    (forestMixture F A lam).expect (fun M _ => (1-q lam)^M) ≤
      Real.exp (-ellH lam*(forestMixture F A lam).meanM) :=
  single_sum_forest_conditional F A hA.1
    (maxWeight_generic_leaf_condition (by linarith [hd.1]) hA) hd hU

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.component_partition_bound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.component_partition_bound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.closed_partition_bound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.closed_partition_bound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.single_sum_forest_conditional
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.single_sum_forest_conditional
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.maxWeight_generic_leaf_condition
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.maxWeight_generic_leaf_condition
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.single_sum_maxWeight_conditional
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.single_sum_maxWeight_conditional
