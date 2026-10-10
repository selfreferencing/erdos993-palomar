module

public import Mathlib
public import Erdos993Lean.Ceiling.Statement

/-!
# The tail inequality B6 (ceiling proof, Appendix R4), and the ceiling from the window hypothesis alone

**B6.** For every forest `F` with matching number `ν` and `B_F(x) = (1 + 2x)^ν (1 + x)^(n - 2ν)`
(coefficients `b_s`): `i_s · b_{s-1} ≤ i_{s-1} · b_s` for every `s ≥ 1`.

Proof idea (ceiling proof, Appendix R4): relax the forest to a maximum matching `M` plus isolated vertices;
its independent sets are the sets meeting each "block" (a matching edge, or an unmatched vertex)
in at most one vertex, counted by `b_s`.  The independent sets of `F` form a down-closed family
inside.  For any down-closed family `𝒜` of such sets, `|𝒜_s| / b_s` is nonincreasing in `s`, by
induction on the blocks: splitting off the last block `W` (of size `w ∈ {1, 2}`) with prefix counts
`a_r`, `|𝒜_r| / b_r = q_r · A(r) + p_r · B(r - 1)`, where `p_r = w a_{r-1} / b_r` is the occupancy
of `W` at rank `r`, `q_r = 1 - p_r`, `A` is the ratio function of the part of `𝒜` avoiding `W`,
`B` the average of those of the parts through each vertex of `W`; `A`, `B` are nonincreasing by
induction, `B ≤ A` (containment), and `p_r` is nondecreasing because `a` is log-concave; then
`(p_{r+1} - p_r)(B(r) - A(r)) ≤ 0` closes the step.

With B6 proved, the ceiling depends only on the window hypothesis `R221Window` (R221 (ii)).

B6 is an instance of the normalized matching property for direct products of posets (W. N. Hsieh,
D. J. Kleitman, "Normalized matching in direct products of partial orders", *Stud. Appl. Math.*
52 (1973) 285–289; L. H. Harper, "The morphology of partially ordered sets", *J. Combin. Theory
Ser. A* 17 (1974) 44–58): the block product has normalized matching, so a down-closed family
inside it satisfies the ratio inequality.  It is not new; the Lean proof here follows the ceiling proof,
Appendix R4.  An equivalent form is the ratio inequality
`i_{k+1} / q_{k+1} ≤ i_k / q_k` with `q = I((n − α) K₂ ⊔ (2α − n) K₁)`, which is `B_F`
for forests since `n − α = ν`.

## Lean structure (namespace `Erdos993Lean.BlockNMP`)

* `block_nmp`: the normalized matching property for block products.  For a finset `bs` of blocks
  and a down-closed family `𝒜` of sets that lie in `⋃ bs` and meet every block at most once,
  `|𝒜_{r+1}| · b_r ≤ |𝒜_r| · b_{r+1}`, where `b` is the coefficient row of
  `blockPoly bs = ∏_{B ∈ bs} (1 + |B| x)`.  Induction on `bs`; the step splits `𝒜` into the part
  `𝒜⁰` avoiding the new block `W` and, for each `v ∈ W`, the link `𝒜ᵛ = {S ∈ 𝒜⁰ : S ∪ {v} ∈ 𝒜}`
  (`lvl_decomp`: `|𝒜_{k+1}| = x_{k+1} + y_k` with `x_k = |𝒜⁰_k|`, `y_k = Σ_v |𝒜ᵛ_k|`).  The
  ratio argument is carried out cross-multiplied (`nmp_arith`): with `a` the row of `bs` and
  `b_{k+1} = a_{k+1} + w a_k` the row of `insert W bs`, the defect
  `|𝒜_{r+1}| b_{r+2} - |𝒜_{r+2}| b_{r+1}` of the inequality at rank `r + 1`, times `a_{r+1}`, is
  `b_{r+1}(a_{r+2} x_{r+1} - a_{r+1} x_{r+2}) + (w x_{r+1} - y_{r+1})(a_{r+1}² - a_r a_{r+2})
    + b_{r+2}(a_{r+1} y_r - a_r y_{r+1})`,
  three nonnegative terms (induction hypothesis for `𝒜⁰`; containment `𝒜ᵛ ⊆ 𝒜⁰` with
  log-concavity of `a` from `Ceiling.GoodPoly`; induction hypothesis for the `𝒜ᵛ`).  Rank `0` and
  the case `a_{r+1} = 0` are handled directly.  No disjointness of the blocks is needed for this
  lemma.
* `tail_of_matching`: for a graph on `Fin n` and a matching `M`, the blocks are the edges of `M`
  and the singletons of the uncovered vertices; `blockPoly = (1 + 2x)^{|M|} (1 + x)^{n - 2|M|}`.
* `tail_inequality`: apply it to a maximum matching (`Ceiling.matchingNumber_mem`).
-/

@[expose] public section

namespace Erdos993Lean

namespace BlockNMP

open Finset Polynomial

variable {V : Type*} [DecidableEq V]

/-- `T` lies in the union of the blocks and meets each block in at most one vertex. -/
def BlockGood (bs : Finset (Finset V)) (T : Finset V) : Prop :=
  T ⊆ bs.biUnion id ∧ ∀ B ∈ bs, (T ∩ B).card ≤ 1

/-- The block polynomial `∏_B (1 + |B| x)`. -/
noncomputable def blockPoly (bs : Finset (Finset V)) : ℕ[X] :=
  ∏ B ∈ bs, (1 + C (B.card : ℕ) * X)

/-- The number of members of `𝒜` of size `r`. -/
def lvl (𝒜 : Finset (Finset V)) (r : ℕ) : ℕ := (𝒜.filter (fun T => T.card = r)).card

/-- A down-closed family. -/
def DownClosed (𝒜 : Finset (Finset V)) : Prop := ∀ T ∈ 𝒜, ∀ T' ⊆ T, T' ∈ 𝒜

theorem lvl_succ_eq_zero {𝒜 : Finset (Finset V)} (h : DownClosed 𝒜) {r : ℕ}
    (hr : lvl 𝒜 r = 0) : lvl 𝒜 (r + 1) = 0 := by
  unfold lvl at hr ⊢
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hr ⊢
  intro T hT hcard
  obtain ⟨v, hv⟩ : T.Nonempty := by
    rw [← Finset.card_pos]; omega
  exact hr (h T hT (T.erase v) (Finset.erase_subset v T))
    (by rw [Finset.card_erase_of_mem hv]; omega)

/-- The arithmetic of the induction step. -/
theorem nmp_arith (a b c x y : ℕ → ℕ) (w : ℕ)
    (hb0 : b 0 = a 0) (hbs : ∀ k, b (k + 1) = a (k + 1) + w * a k)
    (hc0 : c 0 = x 0) (hcs : ∀ k, c (k + 1) = x (k + 1) + y k)
    (hF1 : ∀ k, x (k + 1) * a k ≤ x k * a (k + 1))
    (hF3 : ∀ k, y (k + 1) * a k ≤ y k * a (k + 1))
    (hF5 : ∀ k, y k ≤ w * x k)
    (hF6 : ∀ k, a k * a (k + 2) ≤ a (k + 1) * a (k + 1))
    (hDZ : ∀ k, x k = 0 → x (k + 1) = 0) (r : ℕ) :
    c (r + 1) * b r ≤ c r * b (r + 1) := by
  rcases r with _ | k
  · rw [hcs 0, hb0, hc0, hbs 0]
    have h1 := hF1 0
    have h5 := hF5 0
    nlinarith
  · rw [hcs (k + 1), hcs k, hbs k, hbs (k + 1)]
    rcases Nat.eq_zero_or_pos (a (k + 1)) with h0 | hpos
    · rcases Nat.eq_zero_or_pos (a k) with h00 | hpos'
      · rw [h0, h00]; simp
      · have hx1 : x (k + 1) = 0 := by
          have := hF1 k
          rw [h0, mul_zero] at this
          rcases Nat.eq_zero_or_pos (x (k + 1)) with h | h
          · exact h
          · exact absurd this (not_le.mpr (Nat.mul_pos h hpos'))
        have hx2 : x (k + 1 + 1) = 0 := hDZ _ hx1
        have hy1 : y (k + 1) = 0 := by
          have := hF5 (k + 1); rw [hx1, mul_zero] at this; omega
        rw [hx2, hy1]; simp
    · apply Nat.le_of_mul_le_mul_left _ hpos
      have h1 : (x (k + 1 + 1) : ℤ) * a (k + 1) ≤ x (k + 1) * a (k + 1 + 1) := by
        exact_mod_cast hF1 (k + 1)
      have h3 : (y (k + 1) : ℤ) * a k ≤ y k * a (k + 1) := by exact_mod_cast hF3 k
      have h5 : (y (k + 1) : ℤ) ≤ w * x (k + 1) := by exact_mod_cast hF5 (k + 1)
      have h6 : (a k : ℤ) * a (k + 1 + 1) ≤ a (k + 1) * a (k + 1) := by exact_mod_cast hF6 k
      have hb1 : (0 : ℤ) ≤ a (k + 1) + w * a k := by positivity
      have hb2 : (0 : ℤ) ≤ a (k + 1 + 1) + w * a (k + 1) := by positivity
      have key : (a (k + 1) : ℤ) * ((x (k + 1 + 1) + y (k + 1)) * (a (k + 1) + w * a k)) ≤
          (a (k + 1) : ℤ) * ((x (k + 1) + y k) * (a (k + 1 + 1) + w * a (k + 1))) := by
        nlinarith [mul_nonneg hb1 (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 h6),
          mul_nonneg hb2 (sub_nonneg.2 h3)]
      exact_mod_cast key


/-- Splitting a family by its trace on a block `W` that every member meets at most once. -/
theorem lvl_decomp (𝒜 : Finset (Finset V)) (W : Finset V)
    (hW : ∀ T ∈ 𝒜, (T ∩ W).card ≤ 1) (hdown : DownClosed 𝒜) (r : ℕ) :
    lvl 𝒜 (r + 1) = lvl (𝒜.filter (fun T => Disjoint T W)) (r + 1) +
      ∑ v ∈ W, lvl ((𝒜.filter (fun T => Disjoint T W)).filter (fun S => insert v S ∈ 𝒜)) r := by
  unfold lvl
  rw [← Finset.card_filter_add_card_filter_not (s := 𝒜.filter (fun T => T.card = r + 1))
    (fun T => Disjoint T W)]
  congr 1
  · congr 1
    ext T
    simp only [Finset.mem_filter]
    tauto
  · have hsplit : (𝒜.filter (fun T => T.card = r + 1)).filter (fun T => ¬ Disjoint T W) =
        W.biUnion (fun v => 𝒜.filter (fun T => T.card = r + 1 ∧ v ∈ T)) := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.not_disjoint_iff]
      constructor
      · rintro ⟨⟨hT, hc⟩, v, hvT, hvW⟩
        exact ⟨v, hvW, hT, hc, hvT⟩
      · rintro ⟨v, hvW, hT, hc, hvT⟩
        exact ⟨⟨hT, hc⟩, v, hvT, hvW⟩
    rw [hsplit, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro v hv
      apply Finset.card_nbij' (fun T => T.erase v) (fun S => insert v S)
      · intro T hT
        simp only [Finset.mem_coe, Finset.mem_filter] at hT ⊢
        obtain ⟨hT𝒜, hc, hvT⟩ := hT
        refine ⟨⟨⟨hdown T hT𝒜 _ (Finset.erase_subset v T), ?_⟩, ?_⟩, ?_⟩
        · rw [Finset.disjoint_left]
          intro u hu huW
          rw [Finset.mem_erase] at hu
          exact hu.1 (Finset.card_le_one.mp (hW T hT𝒜) u (Finset.mem_inter.2 ⟨hu.2, huW⟩) v
            (Finset.mem_inter.2 ⟨hvT, hv⟩))
        · rw [Finset.insert_erase hvT]; exact hT𝒜
        · rw [Finset.card_erase_of_mem hvT, hc]; rfl
      · intro S hS
        simp only [Finset.mem_coe, Finset.mem_filter] at hS ⊢
        obtain ⟨⟨⟨_, hSW⟩, hins⟩, hc⟩ := hS
        have hvS : v ∉ S := fun h => Finset.disjoint_left.mp hSW h hv
        exact ⟨hins, by rw [Finset.card_insert_of_notMem hvS, hc], Finset.mem_insert_self v S⟩
      · intro T hT
        simp only [Finset.mem_coe, Finset.mem_filter] at hT
        exact Finset.insert_erase hT.2.2
      · intro S hS
        simp only [Finset.mem_coe, Finset.mem_filter] at hS
        have hvS : v ∉ S := fun h => Finset.disjoint_left.mp hS.1.1.2 h hv
        exact Finset.erase_insert hvS
    · intro v hv v' hv' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro T hT hT'
      simp only [Finset.mem_filter] at hT hT'
      exact hne (Finset.card_le_one.mp (hW T hT.1) v (Finset.mem_inter.2 ⟨hT.2.2, hv⟩) v'
        (Finset.mem_inter.2 ⟨hT'.2.2, hv'⟩))

theorem blockPoly_insert {W : Finset V} {bs : Finset (Finset V)} (hW : W ∉ bs) :
    blockPoly (insert W bs) = blockPoly bs * (1 + C (W.card : ℕ) * X) := by
  unfold blockPoly
  rw [Finset.prod_insert hW, mul_comm]

theorem coeff_mul_linear_zero (p : ℕ[X]) (w : ℕ) : (p * (1 + C w * X)).coeff 0 = p.coeff 0 := by
  rw [mul_add, mul_one, Polynomial.coeff_add, ← mul_assoc, Polynomial.coeff_mul_X_zero, add_zero]

theorem coeff_mul_linear_succ (p : ℕ[X]) (w : ℕ) (k : ℕ) :
    (p * (1 + C w * X)).coeff (k + 1) = p.coeff (k + 1) + w * p.coeff k := by
  rw [mul_add, mul_one, Polynomial.coeff_add, ← mul_assoc, Polynomial.coeff_mul_X,
    Polynomial.coeff_mul_C, mul_comm (p.coeff k)]

theorem blockPoly_good (bs : Finset (Finset V)) : ∃ D, Ceiling.GoodPoly (blockPoly bs) D := by
  induction bs using Finset.induction_on with
  | empty => exact ⟨0, by simpa [blockPoly] using Ceiling.goodPoly_one⟩
  | insert W bs hW ih =>
    obtain ⟨D, hD⟩ := ih
    rw [blockPoly_insert hW]
    rcases Nat.eq_zero_or_pos W.card with h0 | hpos
    · rw [h0]
      simp only [map_zero, zero_mul, add_zero, mul_one]
      exact ⟨D, hD⟩
    · exact ⟨D + 1, hD.mul (Ceiling.goodPoly_linear _ hpos)⟩

theorem blockGood_of_insert {W : Finset V} {bs : Finset (Finset V)} {T : Finset V}
    (hT : BlockGood (insert W bs) T) (hTW : Disjoint T W) : BlockGood bs T := by
  obtain ⟨hsub, hcard⟩ := hT
  refine ⟨?_, fun B hB => hcard B (Finset.mem_insert_of_mem hB)⟩
  intro u hu
  have hu' := hsub hu
  rw [Finset.biUnion_insert, Finset.mem_union] at hu'
  rcases hu' with hu' | hu'
  · exact absurd hu' (Finset.disjoint_left.mp hTW hu)
  · exact hu'

/-- **NMP for block products.**  For every down-closed family `𝒜` of block-good sets,
`|𝒜_{r+1}| · b_r ≤ |𝒜_r| · b_{r+1}`, where `b` is the coefficient row of `∏_B (1 + |B| x)`. -/
theorem block_nmp (bs : Finset (Finset V)) :
    ∀ 𝒜 : Finset (Finset V), (∀ T ∈ 𝒜, BlockGood bs T) → DownClosed 𝒜 →
      ∀ r, lvl 𝒜 (r + 1) * (blockPoly bs).coeff r ≤ lvl 𝒜 r * (blockPoly bs).coeff (r + 1) := by
  induction bs using Finset.induction_on with
  | empty =>
    intro 𝒜 hgood _ r
    have h : lvl 𝒜 (r + 1) = 0 := by
      unfold lvl
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro T hT hc
      have hsub := (hgood T hT).1
      rw [Finset.biUnion_empty, Finset.subset_empty] at hsub
      rw [hsub, Finset.card_empty] at hc
      omega
    rw [h, zero_mul]
    exact Nat.zero_le _
  | insert W bs hW ih =>
    intro 𝒜 hgood hdown r
    have hW1 : ∀ T ∈ 𝒜, (T ∩ W).card ≤ 1 :=
      fun T hT => (hgood T hT).2 W (Finset.mem_insert_self W bs)
    have hgood0 : ∀ T ∈ 𝒜.filter (fun T => Disjoint T W), BlockGood bs T := by
      intro T hT
      rw [Finset.mem_filter] at hT
      exact blockGood_of_insert (hgood T hT.1) hT.2
    have hdown0 : DownClosed (𝒜.filter (fun T => Disjoint T W)) := by
      intro T hT T' hT'
      rw [Finset.mem_filter] at hT ⊢
      exact ⟨hdown T hT.1 T' hT', Finset.disjoint_of_subset_left hT' hT.2⟩
    have hgoodv : ∀ v, ∀ T ∈ (𝒜.filter (fun T => Disjoint T W)).filter
        (fun S => insert v S ∈ 𝒜), BlockGood bs T :=
      fun v T hT => hgood0 T (Finset.mem_of_mem_filter T hT)
    have hdownv : ∀ v, DownClosed ((𝒜.filter (fun T => Disjoint T W)).filter
        (fun S => insert v S ∈ 𝒜)) := by
      intro v T hT T' hT'
      rw [Finset.mem_filter] at hT ⊢
      exact ⟨hdown0 T hT.1 T' hT', hdown _ hT.2 _ (Finset.insert_subset_insert v hT')⟩
    have hsubv : ∀ v k, lvl ((𝒜.filter (fun T => Disjoint T W)).filter
        (fun S => insert v S ∈ 𝒜)) k ≤ lvl (𝒜.filter (fun T => Disjoint T W)) k := by
      intro v k
      unfold lvl
      apply Finset.card_le_card
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    obtain ⟨D, hD⟩ := blockPoly_good bs
    refine nmp_arith (fun k => (blockPoly bs).coeff k) (fun k => (blockPoly (insert W bs)).coeff k)
      (lvl 𝒜) (lvl (𝒜.filter (fun T => Disjoint T W)))
      (fun k => ∑ v ∈ W, lvl ((𝒜.filter (fun T => Disjoint T W)).filter
        (fun S => insert v S ∈ 𝒜)) k) W.card ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ r
    · show (blockPoly (insert W bs)).coeff 0 = (blockPoly bs).coeff 0
      rw [blockPoly_insert hW, coeff_mul_linear_zero]
    · intro k
      show (blockPoly (insert W bs)).coeff (k + 1) =
        (blockPoly bs).coeff (k + 1) + W.card * (blockPoly bs).coeff k
      rw [blockPoly_insert hW, coeff_mul_linear_succ]
    · unfold lvl
      congr 1
      ext T
      simp only [Finset.mem_filter, Finset.card_eq_zero]
      constructor
      · rintro ⟨h1, rfl⟩
        exact ⟨⟨h1, Finset.disjoint_empty_left W⟩, rfl⟩
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
    · intro k
      exact lvl_decomp 𝒜 W hW1 hdown k
    · intro k
      exact ih _ hgood0 hdown0 k
    · intro k
      try simp only
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_le_sum (fun v _ => ih _ (hgoodv v) (hdownv v) k)
    · intro k
      try simp only
      calc ∑ v ∈ W, lvl ((𝒜.filter (fun T => Disjoint T W)).filter
            (fun S => insert v S ∈ 𝒜)) k
          ≤ ∑ v ∈ W, lvl (𝒜.filter (fun T => Disjoint T W)) k :=
            Finset.sum_le_sum (fun v _ => hsubv v k)
        _ = W.card * lvl (𝒜.filter (fun T => Disjoint T W)) k := by
            rw [Finset.sum_const, smul_eq_mul]
    · exact hD.1
    · intro k hk
      exact lvl_succ_eq_zero hdown0 hk

/-- For a graph on `Fin n` with a matching `M` (pairwise vertex-disjoint edges), the independent
sets satisfy `|𝒜_{r+1}| b_r ≤ |𝒜_r| b_{r+1}` with `b = (1 + 2x)^{|M|} (1 + x)^{n - 2|M|}`.
The blocks are the edges of `M` and the singletons of the uncovered vertices. -/
theorem tail_of_matching {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : Finset (Sym2 (Fin n)))
    (hM : ∀ e ∈ M, e ∈ G.edgeSet)
    (hMdisj : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f) (r : ℕ) :
    lvl (univ.filter (fun T : Finset (Fin n) => G.IsIndepSet (T : Set (Fin n)))) (r + 1) *
        bRow n M.card r ≤
      lvl (univ.filter (fun T : Finset (Fin n) => G.IsIndepSet (T : Set (Fin n)))) r *
        bRow n M.card (r + 1) := by
  classical
  set E : Finset (Finset (Fin n)) := M.image Sym2.toFinset with hE
  set Cov : Finset (Fin n) := M.biUnion Sym2.toFinset with hCov
  set S : Finset (Finset (Fin n)) := Covᶜ.image (fun u => ({u} : Finset (Fin n))) with hS
  have hEcard2 : ∀ B ∈ E, B.card = 2 := by
    intro B hB
    rw [hE, Finset.mem_image] at hB
    obtain ⟨e, he, rfl⟩ := hB
    exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (hM e he))
  have hScard1 : ∀ B ∈ S, B.card = 1 := by
    intro B hB
    rw [hS, Finset.mem_image] at hB
    obtain ⟨u, _, rfl⟩ := hB
    exact Finset.card_singleton u
  have hES : Disjoint E S := by
    rw [Finset.disjoint_left]
    intro B hBE hBS
    have h1 := hEcard2 B hBE
    have h2 := hScard1 B hBS
    omega
  have hEcard : E.card = M.card := by
    rw [hE]
    apply Finset.card_image_of_injective
    intro e f hef
    apply Sym2.ext
    intro v
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset]
    exact Iff.of_eq (congrArg (v ∈ ·) hef)
  have hCovcard : Cov.card = 2 * M.card := by
    rw [hCov, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun e he =>
        Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (hM e he)))]
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · intro e he f hf hef
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro v hve hvf
      rw [Sym2.mem_toFinset] at hve hvf
      exact hMdisj e he f hf hef v hve hvf
  have hScard : S.card = n - 2 * M.card := by
    rw [hS, Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_compl,
      Fintype.card_fin, hCovcard]
  have hpoly : blockPoly (E ∪ S) =
      (1 + 2 * X : ℕ[X]) ^ M.card * (1 + X) ^ (n - 2 * M.card) := by
    unfold blockPoly
    rw [Finset.prod_union hES]
    have h1 : ∏ B ∈ E, (1 + C (B.card : ℕ) * X : ℕ[X]) = ∏ B ∈ E, (1 + 2 * X : ℕ[X]) := by
      apply Finset.prod_congr rfl
      intro B hB
      rw [hEcard2 B hB]
      rfl
    have h2 : ∏ B ∈ S, (1 + C (B.card : ℕ) * X : ℕ[X]) = ∏ B ∈ S, (1 + X : ℕ[X]) := by
      apply Finset.prod_congr rfl
      intro B hB
      rw [hScard1 B hB, map_one, one_mul]
    rw [h1, h2, Finset.prod_const, Finset.prod_const, hEcard, hScard]
  have hgood : ∀ T ∈ univ.filter (fun T : Finset (Fin n) => G.IsIndepSet (T : Set (Fin n))),
      BlockGood (E ∪ S) T := by
    intro T hT
    rw [Finset.mem_filter] at hT
    have hind := hT.2
    refine ⟨?_, ?_⟩
    · intro v _
      rw [Finset.mem_biUnion]
      by_cases hv : v ∈ Cov
      · rw [hCov, Finset.mem_biUnion] at hv
        obtain ⟨e, he, hve⟩ := hv
        exact ⟨e.toFinset, Finset.mem_union_left _ (Finset.mem_image_of_mem _ he), hve⟩
      · exact ⟨{v}, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_compl.2 hv)),
          Finset.mem_singleton_self v⟩
    · intro B hB
      rw [Finset.mem_union] at hB
      rcases hB with hB | hB
      · rw [hE, Finset.mem_image] at hB
        obtain ⟨e, he, rfl⟩ := hB
        rw [Finset.card_le_one]
        intro x hx y hy
        rw [Finset.mem_inter, Sym2.mem_toFinset] at hx hy
        by_contra hxy
        have hexy : e = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp ⟨hx.2, hy.2⟩
        have hadj : G.Adj x y := by
          have := hM e he
          rw [hexy, SimpleGraph.mem_edgeSet] at this
          exact this
        exact hind (Finset.mem_coe.2 hx.1) (Finset.mem_coe.2 hy.1) hxy hadj
      · rw [hS, Finset.mem_image] at hB
        obtain ⟨u, _, rfl⟩ := hB
        calc (T ∩ {u}).card ≤ ({u} : Finset (Fin n)).card :=
              Finset.card_le_card Finset.inter_subset_right
          _ = 1 := Finset.card_singleton u
  have hdown : DownClosed (univ.filter (fun T : Finset (Fin n) =>
      G.IsIndepSet (T : Set (Fin n)))) := by
    intro T hT T' hT'
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨Finset.mem_univ _, Set.Pairwise.mono (Finset.coe_subset.2 hT') hT.2⟩
  have h := block_nmp (E ∪ S) _ hgood hdown r
  rw [hpoly] at h
  exact h

end BlockNMP

/-- **B6**: the matching-block deletion inequality for every forest. -/
theorem tail_inequality (F : FiniteForest) (s : ℕ) (hs : 1 ≤ s) :
    independenceCount F s * bRow F.n (matchingNumber F.graph) (s - 1) ≤
      independenceCount F (s - 1) * bRow F.n (matchingNumber F.graph) s := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨M, hM, hMcard, hMfin, hMdisj⟩ := Ceiling.matchingNumber_mem F.graph
  have hcount : ∀ k, independenceCount F k = BlockNMP.lvl (Finset.univ.filter
      (fun T : Finset (Fin F.n) => F.graph.IsIndepSet (T : Set (Fin F.n)))) k := by
    intro k
    unfold independenceCount BlockNMP.lvl
    congr 1
    ext T
    simp [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff]
  have hν : matchingNumber F.graph = hMfin.toFinset.card := by
    rw [← hMcard, Set.ncard_eq_toFinset_card M hMfin]
  rw [hcount, hcount, hν]
  apply BlockNMP.tail_of_matching F.graph hMfin.toFinset
  · intro e he
    rw [Set.Finite.mem_toFinset] at he
    exact hM he
  · intro e he f hf hef v hve
    rw [Set.Finite.mem_toFinset] at he hf
    exact hMdisj he hf hef v hve

/-- R221's window input (R221 (ii), with the positivity stated by R221A).  In the
proof it combines the analytic curvature R221A (certificate-backed) with the combinatorial join
lemmas B2, B5, B7, B8 (paper proofs); **none of this is proved in Lean**. -/
def R221Window : Prop :=
  ∀ F : FiniteForest, 8400000 ≤ F.n → ∀ k, (F.n + 3) / 4 ≤ k → k ≤ hB F →
    0 < independenceCount F (k - 1) ∧ 0 < independenceCount F k ∧
      0 < independenceCount F (k + 1) ∧
      independenceCount F (k - 1) * independenceCount F (k + 1) <
        independenceCount F k * independenceCount F k

/-- **R221, conditional only on the window hypothesis `R221Window`.** -/
theorem ceiling_of_R221Window (h : R221Window) : CeilingStatement 8400000 :=
  ceiling_of_R221Inputs ⟨h, fun F s hs => tail_inequality F s hs⟩

end Erdos993Lean
