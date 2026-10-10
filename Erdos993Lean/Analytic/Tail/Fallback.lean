module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.Marginal
public import Erdos993Lean.Analytic.Tail.Scalar

/-!
# The tail input T3, part 6: the fallback Laplace bound

Source: the audit of the tail input O3,
section "Surviving analytic fallback (PROVED)", and
the per-unit proof; T23 §3 Lemma A.

For every forest, every activity `t > 0`, `q = t/(1+t)`, every independent set `B` and every
`z ∈ [0, 1]`:

  `E[(1 − q + q z)^M] = E[z^{K_B}] ≤ exp(−q (1 − q) r(t, z) m)`,
  `r(t, z) = log((1 + t)/(1 + t z)) / log(1 + t)`  (`rFallback`; `r(t, 0) = 1`).

Proof: Lemma A bounds `E[z^{K_B}]` by the product of the toy factors
`τ_c = p_c + (1 − p_c) e^{−Y_z(c)}`, `Y_z(c) = ∑_{b ∈ ch_B(c)} L_z(p_b)`; `Y_z ≥ r Y`
(`rFallback_mul_Lf_le_Lz`, `p_b ≤ q`); `p_c ≤ t e^{−Y}/(1 + t e^{−Y})` (`rootProb_le_unit`); one unit
gives `−log τ_c ≥ r (1 − q) Y(c)` (`unit_bound`).  On the other side `π_b = (1 − π_parent) p_b ≤ p_b
≤ L(p_b)`, so `q m = ∑_b π_b ≤ ∑_c Y(c)` plus `q` per isolated B-vertex (`massB_le`), and an isolated
B-vertex contributes `(1 + t z)/(1 + t) ≤ exp(−r (1 − q) q)` (`isolated_bound`).

Main results:
* `toy_le_exp`: `∏_{c ∈ C ∩ s} τ_c ≤ exp(−r (1 − q) ∑_c Y(c))` on a rooted tree;
* `massB_le`: `∑_{b ∈ B ∩ (s − r)} μ_b ≤ ∑_c Y(c)`;
* `fallback_set`: for every vertex set `s`, `E_{G[s]}[z^{K_B}] ≤ exp(−r (1 − q) ∑_{b ∈ B ∩ s} π_b(s))`;
* `laplace_fallback_hardcore` (**unconditional**, hard-core form on a `FiniteForest`):
  `(∑_{S indep} t^{|S \ B|} (t z)^{|S ∩ B|}) / Z_F(t) ≤ exp(−r (1 − q) W)`, `W = weightW F t B`;
* `laplace_fallback` (**the mixture form**): `E(1 − q + q z)^M ≤ exp(−q (1 − q) r m)` for
  `forestMixture F B t`, from the two identities `LaplaceIdentity` (item E2) and
  `WeightIdentity` (`MixtureFacts.weight_eq`), stated here as named propositions.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `treeSum` is linear. -/
theorem treeSum_const_mul (c : ℝ) (f : Finset V → V → ℝ) (s : Finset V) (r : V) :
    treeSum G (fun s r => c * f s r) s r = c * treeSum G f s r := by
  refine tree_induction (G := G)
    (P := fun s r => treeSum G (fun s r => c * f s r) s r = c * treeSum G f s r) ?_ ?_ s r
  · intro s r hr ih
    rw [treeSum_eq _ hr, treeSum_eq _ hr, Finset.sum_congr rfl ih, mul_add, Finset.mul_sum]
  · intro s r hr
    rw [treeSum, dif_neg hr, treeSum, dif_neg hr, mul_zero]

/-! ### The B-child mass of a unit -/

section Units

variable (B : Finset V) (t z : ℝ)

variable (G) in
/-- `Y(s, r) = ∑_{w ∈ ch_B(r)} L(p_w)`: the B-child mass of the unit at `r` (T23's `Y_B`). -/
noncomputable def unitY (s : Finset V) (r : V) : ℝ :=
  ∑ w ∈ nbrsIn G s r, if w ∈ B then Lf (rootProb G t (compIn G (s.erase r) w) w) else 0

variable (G) in
/-- `Y_z(s, r) = ∑_{w ∈ ch_B(r)} L_z(p_w)`. -/
noncomputable def unitYz (s : Finset V) (r : V) : ℝ :=
  ∑ w ∈ nbrsIn G s r, if w ∈ B then Lz z (rootProb G t (compIn G (s.erase r) w) w) else 0

variable {B t z}

theorem unitY_nonneg (ht : 0 ≤ t) (s : Finset V) (r : V) : 0 ≤ unitY G B t s r := by
  apply Finset.sum_nonneg
  intro w hw
  split_ifs
  · exact Lf_nonneg (rootProb_nonneg ht _ _) (rootProb_lt_one ht (self_mem_branch hw))
  · exact le_rfl

/-- `e^{−Y} = ∏_{w ∈ ch_B(r)} (1 − p_w)`. -/
theorem exp_neg_unitY (ht : 0 ≤ t) (s : Finset V) (r : V) :
    Real.exp (-unitY G B t s r) = ∏ w ∈ nbrsIn G s r,
      if w ∈ B then 1 - rootProb G t (compIn G (s.erase r) w) w else 1 := by
  rw [unitY, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro w hw
  split_ifs
  · exact exp_neg_Lf (rootProb_lt_one ht (self_mem_branch hw))
  · rw [neg_zero, Real.exp_zero]

/-- `β = e^{−Y_z}`. -/
theorem betaB_eq_exp (ht : 0 ≤ t) (hz0 : 0 ≤ z) (s : Finset V) (r : V) :
    betaB G B t z s r = Real.exp (-unitYz G B t z s r) := by
  rw [unitYz, ← Finset.sum_neg_distrib, Real.exp_sum, betaB]
  apply Finset.prod_congr rfl
  intro w hw
  split_ifs
  · have hp1 := rootProb_lt_one (G := G) ht (self_mem_branch hw)
    have hp0 := rootProb_nonneg (G := G) ht (compIn G (s.erase r) w) w
    rw [exp_neg_Lz (by nlinarith)]
  · rw [neg_zero, Real.exp_zero]

/-- `Y_z ≥ r Y` (`p_w ≤ q` and `L_z/L` decreasing). -/
theorem rFallback_mul_unitY_le (ht : 0 < t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (s : Finset V) (r : V) :
    rFallback t z * unitY G B t s r ≤ unitYz G B t z s r := by
  rw [unitY, unitYz, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  split_ifs
  · exact rFallback_mul_Lf_le_Lz ht hz0 hz1 (rootProb_nonneg ht.le _ _)
      (rootProb_le_actQ ht.le (self_mem_branch hw))
  · rw [mul_zero]

/-- `p_r ≤ t e^{−Y}/(1 + t e^{−Y})` (the odds `p/(1 − p) = t ∏_w (1 − p_w) ≤ t e^{−Y}`). -/
theorem rootProb_le_unit (hG : G.IsAcyclic) (ht : 0 < t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    rootProb G t s r ≤ t * Real.exp (-unitY G B t s r) / (1 + t * Real.exp (-unitY G B t s r)) := by
  have hodds := rootProb_odds hG ht hs hr
  have hprod : ∏ w ∈ nbrsIn G s r, (1 - rootProb G t (compIn G (s.erase r) w) w) ≤
      Real.exp (-unitY G B t s r) := by
    rw [exp_neg_unitY ht.le]
    apply Finset.prod_le_prod₀
    · intro w hw
      linarith [rootProb_lt_one (G := G) ht.le (self_mem_branch hw)]
    · intro w _
      split_ifs
      · exact le_rfl
      · linarith [rootProb_nonneg (G := G) ht.le (compIn G (s.erase r) w) w]
  have hp1 := rootProb_lt_one (G := G) ht.le hr
  have h1p : 0 < 1 - rootProb G t s r := by linarith
  have hE0 : 0 ≤ t * Real.exp (-unitY G B t s r) := by positivity
  have hle : rootProb G t s r ≤ t * Real.exp (-unitY G B t s r) * (1 - rootProb G t s r) := by
    have h := (div_le_iff₀ h1p).mp (hodds.le.trans (mul_le_mul_of_nonneg_left hprod ht.le))
    linarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- One unit: the local toy factor is at most `exp(−r (1 − q) Y)`. -/
theorem toyLocal_le_exp (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (ht : 0 < t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    toyLocal G B t z s r ≤ Real.exp (-(rFallback t z * (1 - actQ t)) * unitY G B t s r) := by
  unfold toyLocal
  by_cases hrB : r ∈ B
  · rw [if_pos hrB]
    have hY : unitY G B t s r = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      rw [if_neg]
      intro hwB
      exact hB r hrB w hwB (mem_nbrsIn.mp hw).2
    rw [hY, mul_zero, Real.exp_zero]
  · rw [if_neg hrB, tauC, betaB_eq_exp ht.le hz0]
    exact unit_bound ht (rFallback_nonneg ht hz0 hz1) (rFallback_le_one ht hz0)
      (unitY_nonneg ht.le s r) (rootProb_le_unit hG ht hs hr) (rFallback_mul_unitY_le ht hz0 hz1 s r)

/-- **The toy product is at most `exp(−r (1 − q) ∑_c Y(c))`.** -/
theorem toy_le_exp (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (ht : 0 < t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    toy G B t z s r ≤
      Real.exp (-(rFallback t z * (1 - actQ t)) * treeSum G (unitY G B t) s r) := by
  have h := treeProd_le_treeProd (G := G) hG (f := toyLocal G B t z)
    (g := fun s r => Real.exp (-(rFallback t z * (1 - actQ t)) * unitY G B t s r))
    (fun _ _ _ hr => toyLocal_nonneg ht.le hz0 hz1 hr)
    (fun _ _ hs hr => toyLocal_le_exp hG hB ht hz0 hz1 hs hr) hs hr
  rw [treeProd_exp, treeSum_const_mul] at h
  exact h

/-- **The mean side**: `∑_{b ∈ B ∩ (s − r)} μ_b ≤ ∑_c Y(c)` for every `ρ ∈ [0, 1]`
(`π_b = (1 − π_parent) p_b ≤ p_b ≤ L(p_b)`). -/
theorem massB_le (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s) {r : V}
    (hr : r ∈ s) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    massB G B t s r ρ ≤ treeSum G (unitY G B t) s r := by
  refine rooted_induction hG (P := fun s r => ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
    massB G B t s r ρ ≤ treeSum G (unitY G B t) s r) ?_ hs hr ρ hρ0 hρ1
  intro s r hs hr ih ρ hρ0 hρ1
  rw [massB_rec hG ht hs hr, treeSum_eq _ hr, unitY, ← Finset.sum_add_distrib]
  have hp0 := rootProb_nonneg (G := G) ht s r
  have hp1 := rootProb_le_one (G := G) ht hr
  have hρ'0 : 0 ≤ 1 - ρ * rootProb G t s r := by nlinarith
  have hρ'1 : 1 - ρ * rootProb G t s r ≤ 1 := by nlinarith
  apply Finset.sum_le_sum
  intro w hw
  apply add_le_add _ (ih w hw _ hρ'0 hρ'1)
  split_ifs
  · have hw0 := rootProb_nonneg (G := G) ht (compIn G (s.erase r) w) w
    have hw1 := rootProb_lt_one (G := G) ht (self_mem_branch hw)
    have := le_Lf hw1
    nlinarith
  · exact le_rfl

end Units

/-! ### Components and vertex sets -/

section Sets

variable {B : Finset V} {t z : ℝ}

/-- For a C-vertex `c` of `K`, the B-mass of `K` is `massB K c 1`. -/
theorem sum_marg_eq_massB {K : Finset V} {c : V} (hcB : c ∉ B) :
    ∑ b ∈ K.filter (· ∈ B), marg G t K b = massB G B t K c 1 := by
  unfold massB
  have hset : (K.erase c).filter (· ∈ B) = K.filter (· ∈ B) := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
    intro h
    exact hcB (Finset.mem_filter.mp h).2
  rw [hset]
  exact Finset.sum_congr rfl (fun b _ => (mu_one K c b).symm)

/-- **One component.** -/
theorem fallback_comp (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (ht : 0 < t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) {K : Finset V} (hK : ConnectedIn G K) {x : V} (hx : x ∈ K) :
    phiF G B t z K ≤
      Real.exp (-(rFallback t z * (1 - actQ t)) * ∑ b ∈ K.filter (· ∈ B), marg G t K b) := by
  have hκ : 0 ≤ rFallback t z * (1 - actQ t) :=
    mul_nonneg (rFallback_nonneg ht hz0 hz1) (by linarith [actQ_lt_one ht.le])
  by_cases h : ∃ c ∈ K, c ∉ B
  · obtain ⟨c, hcK, hcB⟩ := h
    refine (phiF_le_toy hG hB ht.le hz0 hz1 hK hcK).trans ((toy_le_exp hG hB ht hz0 hz1 hK hcK).trans ?_)
    apply Real.exp_le_exp.mpr
    rw [sum_marg_eq_massB hcB]
    have := massB_le (B := B) hG ht.le hK hcK zero_le_one le_rfl
    nlinarith
  · push_neg at h
    have hKB : K ⊆ B := fun c hc => h c hc
    have hKx := eq_singleton_of_subset_indep hB hK hKB hx
    subst hKx
    have hxB : x ∈ B := hKB (Finset.mem_singleton_self x)
    have hnil : nbrsIn G {x} x = ∅ := by
      ext y
      simp only [mem_nbrsIn, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      exact G.irrefl
    have hsum : ∑ b ∈ ({x} : Finset V).filter (· ∈ B), marg G t {x} b = actQ t := by
      rw [Finset.filter_singleton, if_pos hxB, Finset.sum_singleton,
        marg_of_mem (Finset.mem_singleton_self x),
        rootProb_eq_actQ ht.le (Finset.mem_singleton_self x) hnil]
    rw [hsum, phiF_singleton]
    unfold lapW
    rw [if_pos hxB]
    exact isolated_bound ht hz0 hz1

/-- **The fallback on a vertex set**: for every `s`,
`E_{G[s]}[z^{K_B}] ≤ exp(−r (1 − q) ∑_{b ∈ B ∩ s} π_b(s))`. -/
theorem fallback_set (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (ht : 0 < t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) (s : Finset V) :
    phiF G B t z s ≤
      Real.exp (-(rFallback t z * (1 - actQ t)) * ∑ b ∈ s.filter (· ∈ B), marg G t s b) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hne : s.Nonempty
    · obtain ⟨x, hxs⟩ := hne
      set K := compIn G s x with hK
      have hKc : ConnectedIn G K := connectedIn_compIn _ _
      have hxK : x ∈ K := self_mem_compIn hxs
      have hKs : K ⊆ s := compIn_subset _ _
      have hsub : s \ K ⊂ s := Finset.sdiff_ssubset hKs ⟨x, hxK⟩
      -- the B-mass splits
      have hsplit : s.filter (· ∈ B) = K.filter (· ∈ B) ∪ (s \ K).filter (· ∈ B) := by
        rw [← Finset.filter_union, Finset.union_sdiff_of_subset hKs]
      have hdisj : Disjoint (K.filter (· ∈ B)) ((s \ K).filter (· ∈ B)) :=
        Finset.disjoint_filter_filter Finset.disjoint_sdiff
      have hno1 : ∀ a ∈ K, ∀ b ∈ s \ K, ¬ G.Adj a b := fun a ha b hb => not_adj_compIn_sdiff ha hb
      have hno2 : ∀ a ∈ s \ K, ∀ b ∈ s \ (s \ K), ¬ G.Adj a b := by
        intro a ha b hb hab
        rw [Finset.sdiff_sdiff_eq_self hKs] at hb
        exact hno1 b hb a ha hab.symm
      have hmass : ∑ b ∈ s.filter (· ∈ B), marg G t s b =
          ∑ b ∈ K.filter (· ∈ B), marg G t K b + ∑ b ∈ (s \ K).filter (· ∈ B), marg G t (s \ K) b := by
        rw [hsplit, Finset.sum_union hdisj]
        congr 1
        · exact Finset.sum_congr rfl
            (fun b hb => marg_of_closed ht.le hKs hno1 (Finset.mem_filter.mp hb).1)
        · exact Finset.sum_congr rfl
            (fun b hb => marg_of_closed ht.le Finset.sdiff_subset hno2 (Finset.mem_filter.mp hb).1)
      rw [phiF_comp_split s x, hmass, mul_add, Real.exp_add]
      exact mul_le_mul (fallback_comp hG hB ht hz0 hz1 hKc hxK) (ih _ hsub)
        (phiF_nonneg ht.le hz0 _) (Real.exp_pos _).le
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [phiF_empty, Finset.filter_empty, Finset.sum_empty, mul_zero, Real.exp_zero]

end Sets

/-! ### The forest statements -/

section Forest

/-- An independent set in Mathlib's sense is an independent `Finset` in the package's sense. -/
theorem isIndepFinset_of_isIndepSet {W : Type*} {H : SimpleGraph W} [DecidableRel H.Adj]
    {B : Finset W} (hB : H.IsIndepSet (B : Set W)) : IsIndepFinset H B := by
  intro v hv w hw hvw
  by_cases h : v = w
  · subst h
    exact H.irrefl hvw
  · exact hB hv hw h hvw

variable (F : FiniteForest) [inst : DecidableRel F.graph.Adj]

/-- The independent sets of `F` are the independent subsets of `univ`. -/
theorem indepSets_eq :
    indepSets F = (Finset.univ : Finset (Fin F.n)).powerset.filter (IsIndepFinset F.graph) := by
  ext S
  simp only [indepSets, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
    Finset.subset_univ]
  constructor
  · exact isIndepFinset_of_isIndepSet
  · intro h v hv w hw _
    exact h v hv w hw

/-- The independence counts do not depend on the decidability instance. -/
theorem card_indepSetFinset_eq (k : ℕ) :
    (F.graph.indepSetFinset k).card = independenceCount F k := by
  obtain rfl : inst = fun a b => Classical.propDecidable (F.graph.Adj a b) :=
    Subsingleton.elim _ _
  rfl

/-- `Z_F(t) = Z(univ)`. -/
theorem partitionFn_eq_Zw (t : ℝ) :
    partitionFn F t = Zw F.graph (fun _ => t) Finset.univ := by
  rw [Zw_const_eq_sum_count, Finset.card_univ, Fintype.card_fin]
  unfold partitionFn
  apply Finset.sum_congr rfl
  intro k _
  rw [indepCount_univ, card_indepSetFinset_eq]

/-- The marginal of `Defs.lean` is `marg` on `univ`. -/
theorem marginal_eq_marg (t : ℝ) (v : Fin F.n) :
    marginal F t v = marg F.graph t Finset.univ v := by
  rw [marg_of_mem (Finset.mem_univ v), rootProb, ← sum_mem_eq (fun _ => t) (Finset.mem_univ v),
    ← partitionFn_eq_Zw]
  unfold marginal
  congr 1
  rw [indepSets_eq]
  apply Finset.sum_congr
  · ext S
    simp only [Finset.mem_filter]
  · intro S _
    rw [Finset.prod_const]

/-- The Laplace numerator of `Defs.lean`'s form is `Z(t on C, t z on B)(univ)`. -/
theorem lapSum_eq_Zw (B : Finset (Fin F.n)) (t z : ℝ) :
    ∑ S ∈ indepSets F, t ^ (S \ B).card * (t * z) ^ (S ∩ B).card =
      Zw F.graph (lapW B t z) Finset.univ := by
  rw [Zw, ← indepSets_eq]
  apply Finset.sum_congr rfl
  intro S _
  unfold lapW
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff,
    Finset.prod_const, Finset.prod_const]
  ring

end Forest

/-- **The Laplace identity** (T23 §1; item E2), as a named proposition:
`E[(1 − q + q z)^M] = (∑_{S indep} t^{|S \ B|} (t z)^{|S ∩ B|}) / Z_F(t)`. -/
def LaplaceIdentity : Prop :=
  ∀ (F : FiniteForest) (B : Finset (Fin F.n)) (t z : ℝ), 0 < t →
    F.graph.IsIndepSet (B : Set (Fin F.n)) →
    (forestMixture F B t).expect (fun M _ => (1 - actQ t + actQ t * z) ^ M) =
      (∑ S ∈ indepSets F, t ^ (S \ B).card * (t * z) ^ (S ∩ B).card) / partitionFn F t

/-- **`q m = W`** (Zhang (46)), as a named proposition: exactly the field `weight_eq` of
`MixtureFacts`. -/
def WeightIdentity : Prop :=
  ∀ (F : FiniteForest) (t : ℝ) (B : Finset (Fin F.n)), 0 < t →
    F.graph.IsIndepSet (B : Set (Fin F.n)) →
    actQ t * (forestMixture F B t).meanM = weightW F t B

theorem weightIdentity_of_mixtureFacts (h : MixtureFacts) : WeightIdentity := h.weight_eq

/-- **The fallback, hard-core form (unconditional).**  For every forest `F`, every independent
set `B`, `t > 0` and `z ∈ [0, 1]`:
`(∑_{S indep} t^{|S \ B|} (t z)^{|S ∩ B|}) / Z_F(t) ≤ exp(−r(t, z) (1 − q) W)`, `W = ∑_{b ∈ B} π_b`. -/
theorem laplace_fallback_hardcore (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t z : ℝ} (ht : 0 < t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) :
    (∑ S ∈ indepSets F, t ^ (S \ B).card * (t * z) ^ (S ∩ B).card) / partitionFn F t ≤
      Real.exp (-(rFallback t z * (1 - actQ t)) * weightW F t B) := by
  classical
  have h := fallback_set F.isForest (isIndepFinset_of_isIndepSet hB) ht hz0 hz1
    (Finset.univ : Finset (Fin F.n))
  have hfilt : (Finset.univ : Finset (Fin F.n)).filter (· ∈ B) = B := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilt] at h
  rw [lapSum_eq_Zw, partitionFn_eq_Zw]
  unfold weightW
  rw [Finset.sum_congr rfl (fun b _ => marginal_eq_marg F t b)]
  exact h

/-- **The fallback Laplace bound (mixture form).**  For every forest `F`, every independent
set `B`, `t > 0` and `0 ≤ z ≤ 1`:
`E[(1 − q + q z)^M] ≤ exp(−q (1 − q) r(t, z) m)`, `m = E M`, for `forestMixture F B t`.
The two identities are the Laplace identity E2 and `MixtureFacts.weight_eq`. -/
theorem laplace_fallback (hLap : LaplaceIdentity) (hW : WeightIdentity) (F : FiniteForest)
    (B : Finset (Fin F.n)) (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t z : ℝ} (ht : 0 < t)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (forestMixture F B t).expect (fun M _ => (1 - actQ t + actQ t * z) ^ M) ≤
      Real.exp (-(actQ t * (1 - actQ t) * rFallback t z) * (forestMixture F B t).meanM) := by
  rw [hLap F B t z ht hB]
  have hmean : (forestMixture F B t).meanM = weightW F t B / actQ t := by
    rw [← hW F t B ht hB]
    field_simp [(actQ_pos ht).ne']
  have h := laplace_fallback_hardcore F B hB ht hz0 hz1
  have hexp : -(actQ t * (1 - actQ t) * rFallback t z) * (weightW F t B / actQ t) =
      -(rFallback t z * (1 - actQ t)) * weightW F t B := by
    have hq : actQ t * (actQ t)⁻¹ = 1 := mul_inv_cancel₀ (actQ_pos ht).ne'
    rw [div_eq_mul_inv]
    calc -(actQ t * (1 - actQ t) * rFallback t z) * (weightW F t B * (actQ t)⁻¹)
        = -(rFallback t z * (1 - actQ t)) * weightW F t B * (actQ t * (actQ t)⁻¹) := by ring
      _ = -(rFallback t z * (1 - actQ t)) * weightW F t B := by rw [hq, mul_one]
  rw [hmean, hexp]
  exact h

end Erdos993Lean.Analytic.Tail
