module

public import Mathlib
public import Erdos993Lean.Analytic.Defs
public import Erdos993Lean.Ceiling.Join
public import Erdos993Lean.Zhang.Decomposition

/-!
# The hard-core model of a forest: independent sets, the decomposition over `B`, marginals

Sources: T. Zhang, *Exact Certificates
for Unimodality of Forest Independence Polynomials*, v1.1, Section 2.1 identity (2) and equations
(45)–(46); the note T23 §1.

For a forest `F` (only its graph is used here) and an independent set `B`, put `C = Bᶜ`.

* `mem_indepSets`, `mem_indepSets'`: membership in `indepSets F` (Mathlib's `IsIndepSet`, or the
  elementwise form).
* `freeSet F B σ = {b ∈ B : b has no neighbour in σ}`, with `freeCount F B σ = |freeSet F B σ|`
  (`freeCount_eq_card`) and the bridge `freeSet_eq_avail` to `Zhang.avail`.
* `states F B`: the independent subsets `σ` of `C`; it is `(forestMixture F B t).S`
  (`forestMixture_S`).
* **The decomposition** (`sum_indepSets_eq_sum_states`, Zhang (2) as a sum identity): every
  independent set is `S = σ ∪ T` with `σ = S \ B ∈ states F B` and `T = S ∩ B ⊆ freeSet F B σ`,
  uniquely, so `Σ_{S indep} f(S) = Σ_σ Σ_{T ⊆ free(σ)} f(σ ∪ T)` for every `f`.
* Sums over independent sets grouped by size (`sum_indepSets_card`): `partitionFn_eq_sum`,
  `hardCoreMean_eq_sum`, `hardCoreVar_eq_sum`.
* Marginals: `marginal_mul_partitionFn`, `sum_marginal` (`Σ_{v ∈ A} π_v = E|S ∩ A|`),
  `weightW_eq_sum`, `sum_univ_marginal` (`Σ_v π_v = μ`), `marginal_pos`.
* `exists_isMaxWeight`: a maximum-weight independent set exists (the independent sets form a
  finite nonempty family).

Namespace: `Erdos993Lean.Analytic.HardCore`.

Grade: PROVED IN LEAN (standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.HardCore

open Finset

variable (F : FiniteForest)

/-! ## Independent sets -/

theorem isIndepSet_coe_iff {S : Finset (Fin F.n)} :
    F.graph.IsIndepSet (S : Set (Fin F.n)) ↔ ∀ v ∈ S, ∀ w ∈ S, ¬ F.graph.Adj v w := by
  constructor
  · intro h v hv w hw hvw
    exact h hv hw (F.graph.ne_of_adj hvw) hvw
  · intro h v hv w hw _
    exact h v hv w hw

theorem mem_indepSets {S : Finset (Fin F.n)} :
    S ∈ indepSets F ↔ F.graph.IsIndepSet (S : Set (Fin F.n)) := by
  unfold indepSets
  simp

theorem mem_indepSets' {S : Finset (Fin F.n)} :
    S ∈ indepSets F ↔ ∀ v ∈ S, ∀ w ∈ S, ¬ F.graph.Adj v w := by
  rw [mem_indepSets, isIndepSet_coe_iff]

theorem empty_mem_indepSets : (∅ : Finset (Fin F.n)) ∈ indepSets F := by
  rw [mem_indepSets']
  simp

theorem singleton_mem_indepSets (v : Fin F.n) : ({v} : Finset (Fin F.n)) ∈ indepSets F := by
  rw [mem_indepSets']
  intro a ha b hb
  rw [Finset.mem_singleton] at ha hb
  subst ha hb
  exact F.graph.irrefl

theorem mem_indepSets_of_subset {S T : Finset (Fin F.n)} (hT : T ∈ indepSets F) (hST : S ⊆ T) :
    S ∈ indepSets F := by
  rw [mem_indepSets'] at hT ⊢
  exact fun v hv w hw => hT v (hST hv) w (hST hw)

/-! ## Sums over independent sets grouped by size -/

/-- The independent sets of size `k` are counted by `independenceCount F k`. -/
theorem card_filter_indepSets (k : ℕ) :
    ((indepSets F).filter (fun S => S.card = k)).card = independenceCount F k := by
  classical
  unfold independenceCount
  congr 1
  ext S
  simp only [Finset.mem_filter, mem_indepSets, SimpleGraph.mem_indepSetFinset_iff,
    SimpleGraph.isNIndepSet_iff]

/-- `Σ_{S indep} h(|S|) = Σ_{k ≤ n} i_k h(k)`. -/
theorem sum_indepSets_card (h : ℕ → ℝ) :
    ∑ S ∈ indepSets F, h S.card = ∑ k ∈ range (F.n + 1), (independenceCount F k : ℝ) * h k := by
  have hmaps : ∀ S ∈ indepSets F, S.card ∈ range (F.n + 1) := by
    intro S _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    simpa using Finset.card_le_univ S
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∀ S ∈ (indepSets F).filter (fun S => S.card = k), h S.card = h k :=
    fun S hS => by rw [(Finset.mem_filter.mp hS).2]
  rw [Finset.sum_congr rfl hk, Finset.sum_const, nsmul_eq_mul, card_filter_indepSets]

/-- `Σ_{S indep, |S| = i} t^|S| = i_i t^i`. -/
theorem sum_indepSets_card_eq (t : ℝ) (i : ℕ) :
    ∑ S ∈ indepSets F, (if S.card = i then t ^ S.card else 0) =
      (independenceCount F i : ℝ) * t ^ i := by
  rw [← Finset.sum_filter]
  have hk : ∀ S ∈ (indepSets F).filter (fun S => S.card = i), t ^ S.card = t ^ i :=
    fun S hS => by rw [(Finset.mem_filter.mp hS).2]
  rw [Finset.sum_congr rfl hk, Finset.sum_const, nsmul_eq_mul, card_filter_indepSets]

/-- `Z_F(t) = Σ_{S indep} t^|S|`. -/
theorem partitionFn_eq_sum (t : ℝ) : partitionFn F t = ∑ S ∈ indepSets F, t ^ S.card := by
  rw [sum_indepSets_card F (fun k => t ^ k)]
  rfl

theorem partitionFn_pos {t : ℝ} (ht : 0 ≤ t) : 0 < partitionFn F t :=
  lt_of_lt_of_le one_pos (Join.one_le_partitionFn F ht)

/-- `μ_F(t) = Σ_{S indep} |S| t^|S| / Z_F(t)`. -/
theorem hardCoreMean_eq_sum (t : ℝ) :
    hardCoreMean F t = (∑ S ∈ indepSets F, (S.card : ℝ) * t ^ S.card) / partitionFn F t := by
  unfold hardCoreMean
  rw [sum_indepSets_card F (fun k => (k : ℝ) * t ^ k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `V_F(t) = Σ_{S indep} (|S| − μ)² t^|S| / Z_F(t)`. -/
theorem hardCoreVar_eq_sum (t : ℝ) :
    hardCoreVar F t = (∑ S ∈ indepSets F, ((S.card : ℝ) - hardCoreMean F t) ^ 2 * t ^ S.card) /
      partitionFn F t := by
  unfold hardCoreVar
  rw [sum_indepSets_card F (fun k => ((k : ℝ) - hardCoreMean F t) ^ 2 * t ^ k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## Marginals and weights -/

theorem marginal_eq (t : ℝ) (v : Fin F.n) :
    marginal F t v =
      (∑ S ∈ (indepSets F).filter (fun S => v ∈ S), t ^ S.card) / partitionFn F t := by
  unfold marginal
  congr 1

theorem marginal_mul_partitionFn {t : ℝ} (ht : 0 ≤ t) (v : Fin F.n) :
    marginal F t v * partitionFn F t =
      ∑ S ∈ (indepSets F).filter (fun S => v ∈ S), t ^ S.card := by
  rw [marginal_eq, div_mul_cancel₀ _ (partitionFn_pos F ht).ne']

/-- `Σ_{v ∈ A} π_v = E|S ∩ A|`. -/
theorem sum_marginal (t : ℝ) (A : Finset (Fin F.n)) :
    ∑ v ∈ A, marginal F t v =
      (∑ S ∈ indepSets F, ((S ∩ A).card : ℝ) * t ^ S.card) / partitionFn F t := by
  simp only [marginal_eq, ← Finset.sum_div]
  congr 1
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- `W = Σ_{b ∈ B} π_b = E|S ∩ B|`. -/
theorem weightW_eq_sum (t : ℝ) (B : Finset (Fin F.n)) :
    weightW F t B = (∑ S ∈ indepSets F, ((S ∩ B).card : ℝ) * t ^ S.card) / partitionFn F t :=
  sum_marginal F t B

/-- `Σ_v π_v = μ_F(t)`. -/
theorem sum_univ_marginal (t : ℝ) : ∑ v, marginal F t v = hardCoreMean F t := by
  rw [sum_marginal, hardCoreMean_eq_sum]
  simp only [Finset.inter_univ]

theorem marginal_nonneg {t : ℝ} (ht : 0 ≤ t) (v : Fin F.n) : 0 ≤ marginal F t v := by
  rw [marginal_eq]
  exact div_nonneg (Finset.sum_nonneg fun S _ => pow_nonneg ht _) (partitionFn_pos F ht).le

theorem marginal_pos {t : ℝ} (ht : 0 < t) (v : Fin F.n) : 0 < marginal F t v := by
  rw [marginal_eq]
  refine div_pos (Finset.sum_pos' (fun S _ => pow_nonneg ht.le _) ⟨{v}, ?_, ?_⟩)
    (partitionFn_pos F ht.le)
  · rw [Finset.mem_filter]
    exact ⟨singleton_mem_indepSets F v, Finset.mem_singleton_self v⟩
  · positivity

/-- A maximum-weight independent set exists at every activity. -/
theorem exists_isMaxWeight (t : ℝ) : ∃ B, IsMaxWeight F t B := by
  obtain ⟨B, hB, hmax⟩ :=
    Finset.exists_max_image (indepSets F) (weightW F t) ⟨∅, empty_mem_indepSets F⟩
  exact ⟨B, (mem_indepSets F).mp hB, fun B' hB' => hmax B' ((mem_indepSets F).mpr hB')⟩

/-! ## Free vertices and the states of the mixture -/

/-- The free set `free(σ) = {b ∈ B : b has no neighbour in σ}`. -/
noncomputable def freeSet (B σ : Finset (Fin F.n)) : Finset (Fin F.n) := by
  classical
  exact B.filter fun b => ∀ c ∈ σ, ¬ F.graph.Adj b c

theorem mem_freeSet {B σ : Finset (Fin F.n)} {b : Fin F.n} :
    b ∈ freeSet F B σ ↔ b ∈ B ∧ ∀ c ∈ σ, ¬ F.graph.Adj b c := by
  unfold freeSet
  simp only [Finset.mem_filter]

theorem freeCount_eq_card (B σ : Finset (Fin F.n)) : freeCount F B σ = (freeSet F B σ).card :=
  rfl

theorem freeSet_subset (B σ : Finset (Fin F.n)) : freeSet F B σ ⊆ B :=
  fun _ hb => ((mem_freeSet F).mp hb).1

/-- The bridge to Zhang's available vertices: `free(σ) = avail G B σ`. -/
theorem freeSet_eq_avail [DecidableRel F.graph.Adj] (B σ : Finset (Fin F.n)) :
    freeSet F B σ = Zhang.avail F.graph B σ := by
  ext b
  rw [mem_freeSet, Zhang.mem_avail]
  exact and_congr_right fun _ => forall₂_congr fun c _ => by rw [F.graph.adj_comm]

theorem freeCount_eq_avail_card [DecidableRel F.graph.Adj] (B σ : Finset (Fin F.n)) :
    freeCount F B σ = (Zhang.avail F.graph B σ).card := by
  rw [freeCount_eq_card, freeSet_eq_avail]

/-- The states of the mixture: the independent subsets of `C = Bᶜ`. -/
noncomputable def states (B : Finset (Fin F.n)) : Finset (Finset (Fin F.n)) := by
  classical
  exact (univ \ B).powerset.filter fun σ => F.graph.IsIndepSet (σ : Set (Fin F.n))

theorem mem_states {B σ : Finset (Fin F.n)} :
    σ ∈ states F B ↔ Disjoint σ B ∧ ∀ v ∈ σ, ∀ w ∈ σ, ¬ F.graph.Adj v w := by
  unfold states
  simp only [Finset.mem_filter, Finset.mem_powerset]
  rw [isIndepSet_coe_iff]
  refine and_congr_left fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · rw [Finset.disjoint_left]
    exact fun a ha => (Finset.mem_sdiff.mp (h ha)).2
  · intro a ha
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, Finset.disjoint_left.mp h ha⟩

theorem empty_mem_states (B : Finset (Fin F.n)) : (∅ : Finset (Fin F.n)) ∈ states F B := by
  rw [mem_states]
  simp

@[simp] theorem forestMixture_S (B : Finset (Fin F.n)) (t : ℝ) :
    (forestMixture F B t).S = states F B := rfl

@[simp] theorem forestMixture_w (B : Finset (Fin F.n)) (t : ℝ) (σ : Finset (Fin F.n)) :
    (forestMixture F B t).w σ = t ^ σ.card * (1 + t) ^ freeCount F B σ / partitionFn F t := rfl

@[simp] theorem forestMixture_M (B : Finset (Fin F.n)) (t : ℝ) :
    (forestMixture F B t).M = freeCount F B := rfl

@[simp] theorem forestMixture_Y (B : Finset (Fin F.n)) (t : ℝ) :
    (forestMixture F B t).Y = Finset.card := rfl

/-- `|σ| + M(σ) ≤ n`: the parts `σ ⊆ C` and `free(σ) ⊆ B` are disjoint. -/
theorem card_add_freeCount_le {B σ : Finset (Fin F.n)} (hσ : σ ∈ states F B) :
    σ.card + freeCount F B σ ≤ F.n := by
  have hd : Disjoint σ (freeSet F B σ) :=
    Finset.disjoint_of_subset_right (freeSet_subset F B σ) ((mem_states F).mp hσ).1
  rw [freeCount_eq_card, ← Finset.card_union_of_disjoint hd]
  simpa using Finset.card_le_univ (σ ∪ freeSet F B σ)

/-! ## The decomposition over an independent set -/

/-- **The decomposition (Zhang, Section 2.1, (2); T23 §1).**  For an independent set `B`, every
independent set is `σ ∪ T` for a unique state `σ = S \ B` and a unique `T = S ∩ B ⊆ free(σ)`, and
every such pair gives an independent set; hence
`Σ_{S indep} f(S) = Σ_{σ ∈ states} Σ_{T ⊆ free(σ)} f(σ ∪ T)`. -/
theorem sum_indepSets_eq_sum_states {β : Type*} [AddCommMonoid β] {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (f : Finset (Fin F.n) → β) :
    ∑ S ∈ indepSets F, f S = ∑ σ ∈ states F B, ∑ T ∈ (freeSet F B σ).powerset, f (σ ∪ T) := by
  classical
  rw [isIndepSet_coe_iff] at hB
  have hmaps : ∀ S ∈ indepSets F, S \ B ∈ states F B := by
    intro S hS
    rw [mem_indepSets'] at hS
    rw [mem_states]
    exact ⟨Finset.sdiff_disjoint, fun v hv w hw =>
      hS v (Finset.mem_sdiff.mp hv).1 w (Finset.mem_sdiff.mp hw).1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  obtain ⟨hσB, hσi⟩ := (mem_states F).mp hσ
  symm
  refine Finset.sum_nbij' (fun T => σ ∪ T) (fun S => S ∩ B) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.mem_filter, mem_indepSets']
    constructor
    · intro v hv w hw
      rw [Finset.mem_union] at hv hw
      rcases hv with hv | hv <;> rcases hw with hw | hw
      · exact hσi v hv w hw
      · exact fun h => ((mem_freeSet F).mp (hT hw)).2 v hv h.symm
      · exact ((mem_freeSet F).mp (hT hv)).2 w hw
      · exact hB v (freeSet_subset F B σ (hT hv)) w (freeSet_subset F B σ (hT hw))
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxB⟩
        · exact hx
        · exact absurd (freeSet_subset F B σ (hT hx)) hxB
      · intro hx
        exact ⟨Or.inl hx, Finset.disjoint_left.mp hσB hx⟩
  · intro S hS
    rw [Finset.mem_filter, mem_indepSets'] at hS
    obtain ⟨hSi, hSσ⟩ := hS
    rw [Finset.mem_powerset]
    intro b hb
    rw [Finset.mem_inter] at hb
    rw [mem_freeSet]
    refine ⟨hb.2, fun c hc => ?_⟩
    rw [← hSσ, Finset.mem_sdiff] at hc
    exact hSi b hb.1 c hc.1
  · intro T hT
    rw [Finset.mem_powerset] at hT
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxB⟩
      · exact absurd hxB (Finset.disjoint_left.mp hσB hx)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, freeSet_subset F B σ (hT hx)⟩
  · intro S hS
    rw [Finset.mem_filter] at hS
    rw [← hS.2]
    exact Finset.sdiff_union_inter S B
  · intro T _
    rfl

/-- The parts of `σ ∪ T` for a state `σ` and `T ⊆ free(σ)`: `(σ ∪ T) \ B = σ`, `(σ ∪ T) ∩ B = T`,
`|σ ∪ T| = |σ| + |T|`. -/
theorem union_parts {B σ T : Finset (Fin F.n)} (hσ : σ ∈ states F B)
    (hT : T ⊆ freeSet F B σ) :
    (σ ∪ T) \ B = σ ∧ (σ ∪ T) ∩ B = T ∧ (σ ∪ T).card = σ.card + T.card := by
  have hσB := ((mem_states F).mp hσ).1
  have hTB : T ⊆ B := hT.trans (freeSet_subset F B σ)
  refine ⟨?_, ?_, Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hTB hσB)⟩
  · ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxB⟩
      · exact hx
      · exact absurd (hTB hx) hxB
    · intro hx
      exact ⟨Or.inl hx, Finset.disjoint_left.mp hσB hx⟩
  · ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxB⟩
      · exact absurd hxB (Finset.disjoint_left.mp hσB hx)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hTB hx⟩

end Erdos993Lean.Analytic.HardCore
