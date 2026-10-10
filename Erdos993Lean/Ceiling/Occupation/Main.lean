module

public import Mathlib
public import Erdos993Lean.Ceiling.HardCore
public import Erdos993Lean.Ceiling.Occupation.Paths

/-!
# B5: occupation at activity `7/3`

**Theorem** (`occupationAt73 : OccupationAt73`;
the ceiling proof,
Appendix R3).
For every finite forest `F`, `μ_F(7/3) ≥ W(F) + cc(F)/7`, where
`W(F) = n/2 - ν(F)/3` and `cc(F)` counts the connected components, isolated vertices included.

Proof: induction on the vertex sets of the fixed forest (`Occupation.surplus_nonneg`).
* A vertex set with an isolated vertex: `surplus_isolated`.
* Otherwise `exists_leafStem` gives a vertex `v` with `t ≥ 1` leaf neighbours and at most one
  other neighbour `u`.  (The paper takes `v` next to an endpoint of a longest path; here `v = y` for
  a pair of adjacent `x, y` minimizing the size of the branch of `y` at `x` among branches with at
  least two vertices, or `v` on an isolated edge.)
* `surplus_leafStem`: without `u` the component is a star, paid by `star_surplus_nonneg`
  (edge `5/63`, two-leaf star `107/378`, i.e. the paper's `5/357` and `107/5082` after
  normalizing by `Z`); with `u`,
  `Φ(s) = b^t Φ(H) + λ Φ(J) + b^t Z(H) (t/5 - 1/6) + λ Z(J) (k/7 + m/3 - t/2 + 4/21)`
  (`b = 10/3`, `λ = 7/3`, `k = deg_H u ≥ 1`, `m = ν(H) - ν(J) ∈ {0, 1}`), which pays every case
  using `Z(J) ≤ Z(H)` (the paper's `w ≤ 7/17`, `w ≤ 21/121`), except `t = 1, k = 1, m = 0`: the
  pendant path `ℓ - v - u` at the matching-essential `x`, paid by `surplus_tail3`
  (`Occupation/Paths.lean`).
* The bridge to `FiniteForest`: `Zq_eq_sum_count`, `Sq_eq_sum_count` (the two sums of
  `hardCoreMean`), `nuIn_univ` (`matchingNumber` via `sSup`), `ccIn_univ` (`Nat.card` of
  `ConnectedComponent`).
-/

@[expose] public section

namespace Erdos993Lean
namespace Occupation

open Finset

section Induction

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### A vertex next to the end of a longest path -/

/-- If the branch of `b` at `a` has at most one vertex, then `b` is a leaf of `s` hanging at `a`. -/
theorem nbrsIn_eq_of_small_branch {s : Finset V} {a b : V} (has : a ∈ s)
    (hb : b ∈ nbrsIn G s a) (hsmall : (compIn G (s.erase a) b).card < 2) :
    nbrsIn G s b = {a} := by
  obtain ⟨hbs, hab⟩ := mem_nbrsIn.mp hb
  ext q
  rw [mem_nbrsIn, Finset.mem_singleton]
  constructor
  · rintro ⟨hqs, hbq⟩
    by_contra hqa
    have hbE : b ∈ s.erase a := Finset.mem_erase.mpr ⟨(G.ne_of_adj hab).symm, hbs⟩
    have hqE : q ∈ s.erase a := Finset.mem_erase.mpr ⟨hqa, hqs⟩
    have h1 : b ∈ compIn G (s.erase a) b := self_mem_compIn hbE
    have h2 : q ∈ compIn G (s.erase a) b := mem_compIn_of_adjIn h1 ⟨hbE, hqE, hbq⟩
    have h3 : 1 < (compIn G (s.erase a) b).card :=
      Finset.one_lt_card.mpr ⟨b, h1, q, h2, (G.ne_of_adj hbq)⟩
    omega
  · rintro rfl
    exact ⟨has, hab.symm⟩

/-- **Existence of a leaf-stem vertex.**  If every vertex of the nonempty set `s` has a neighbour
in `s`, some `v ∈ s` has at least one leaf neighbour and at most one non-leaf neighbour (a vertex
next to an endpoint of a longest path; here found by minimizing the size of a branch). -/
theorem exists_leafStem (hG : G.IsAcyclic) {s : Finset V}
    (hs : ∀ x ∈ s, (nbrsIn G s x).Nonempty) (hne : s.Nonempty) :
    ∃ v ∈ s, (leavesAt G s v).Nonempty ∧ (stemsAt G s v).card ≤ 1 := by
  classical
  set E := (s ×ˢ s).filter
    (fun p : V × V => G.Adj p.1 p.2 ∧ 2 ≤ (compIn G (s.erase p.1) p.2).card) with hE
  by_cases hEne : E.Nonempty
  · obtain ⟨⟨x, y⟩, hp, hmin⟩ := Finset.exists_min_image E
      (fun p : V × V => (compIn G (s.erase p.1) p.2).card) hEne
    simp only [hE, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hxs, hys⟩, hxy, h2⟩ := hp
    have hyN : y ∈ nbrsIn G s x := mem_nbrsIn.mpr ⟨hys, hxy⟩
    have hyE : y ∈ s.erase x := Finset.mem_erase.mpr ⟨(G.ne_of_adj hxy).symm, hys⟩
    -- every other neighbour of `y` is a leaf
    have claim : ∀ z ∈ nbrsIn G s y, z ≠ x → nbrsIn G s z = {y} := by
      intro z hz hzx
      obtain ⟨hzs, hyz⟩ := mem_nbrsIn.mp hz
      have hzE : z ∈ s.erase x := Finset.mem_erase.mpr ⟨hzx, hzs⟩
      have hzC : z ∈ compIn G (s.erase x) y :=
        mem_compIn_of_adjIn (self_mem_compIn hyE) ⟨hyE, hzE, hyz⟩
      have hsub : compIn G (s.erase y) z ⊆ (compIn G (s.erase x) y).erase y := by
        intro b hb
        obtain ⟨hbs, hzb⟩ := mem_compIn.mp hb
        exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hbs,
          (mem_branch_iff_of_reachIn hG hyN hzb).mp hzC⟩
      have hlt : (compIn G (s.erase y) z).card < (compIn G (s.erase x) y).card :=
        (Finset.card_le_card hsub).trans_lt
          (Finset.card_erase_lt_of_mem (self_mem_compIn hyE))
      apply nbrsIn_eq_of_small_branch hys hz
      by_contra hge
      push_neg at hge
      have hmem : (y, z) ∈ E := by
        simp only [hE, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hys, hzs⟩, hyz, hge⟩
      have := hmin (y, z) hmem
      simp only at this
      omega
    refine ⟨y, hys, ?_, ?_⟩
    · -- a leaf neighbour: the first step from `y` inside its branch
      obtain ⟨z, hzC, hzy⟩ := Finset.exists_mem_ne (by omega : 1 < (compIn G (s.erase x) y).card) y
      obtain ⟨-, hreach⟩ := mem_compIn.mp hzC
      rcases Relation.ReflTransGen.cases_head hreach with h | ⟨c, hyc, _⟩
      · exact absurd h.symm hzy
      · have hcN : c ∈ nbrsIn G s y := mem_nbrsIn.mpr ⟨Finset.mem_of_mem_erase hyc.2.1, hyc.2.2⟩
        exact ⟨c, mem_leavesAt.mpr ⟨hcN, claim c hcN (Finset.ne_of_mem_erase hyc.2.1)⟩⟩
    · -- the only possible non-leaf neighbour is `x`
      apply Finset.card_le_one.mpr
      intro u hu u' hu'
      obtain ⟨huN, hun⟩ := mem_stemsAt.mp hu
      obtain ⟨hu'N, hu'n⟩ := mem_stemsAt.mp hu'
      have h1 : u = x := by
        by_contra h
        exact hun (claim u huN h)
      have h2 : u' = x := by
        by_contra h
        exact hu'n (claim u' hu'N h)
      rw [h1, h2]
  · -- no large branch: `s` contains an isolated edge
    rw [Finset.not_nonempty_iff_eq_empty] at hEne
    obtain ⟨x, hxs⟩ := hne
    obtain ⟨y, hyN⟩ := hs x hxs
    obtain ⟨hys, hxy⟩ := mem_nbrsIn.mp hyN
    have hsmall : ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → (compIn G (s.erase a) b).card < 2 := by
      intro a ha b hb hab
      by_contra hge
      push_neg at hge
      have hmem : (a, b) ∈ E := by
        simp only [hE, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha, hb⟩, hab, hge⟩
      rw [hEne] at hmem
      exact Finset.notMem_empty _ hmem
    have hyleaf : nbrsIn G s y = {x} :=
      nbrsIn_eq_of_small_branch hxs hyN (hsmall x hxs y hys hxy)
    have hxleaf : nbrsIn G s x = {y} :=
      nbrsIn_eq_of_small_branch hys (mem_nbrsIn.mpr ⟨hxs, hxy.symm⟩) (hsmall y hys x hxs hxy.symm)
    refine ⟨x, hxs, ⟨y, mem_leavesAt.mpr ⟨hyN, hyleaf⟩⟩, ?_⟩
    apply Finset.card_le_one.mpr
    intro u hu u' _
    obtain ⟨huN, hun⟩ := mem_stemsAt.mp hu
    rw [hxleaf, Finset.mem_singleton] at huN
    subst huN
    exact absurd hyleaf hun

/-- The neighbours of `v` in `s - a`. -/
theorem nbrsIn_erase (s : Finset V) (a v : V) :
    nbrsIn G (s.erase a) v = (nbrsIn G s v).erase a := by
  ext w
  simp only [nbrsIn, Finset.mem_filter, Finset.mem_erase]
  tauto

/-- The star surplus `b^t (t/5 - 13/42) + λ (29/42 - t/2) ≥ 0` for `t ≥ 1` (edge `5/63`,
two-leaf star `107/378`, `t ≥ 3` from `b^t ≥ 1000/27`). -/
theorem star_surplus_nonneg {t : ℕ} (ht : 1 ≤ t) :
    0 ≤ (10 / 3 : ℚ) ^ t * (t / 5 - 13 / 42) + 7 / 3 * (29 / 42 - t / 2) := by
  rcases Nat.lt_or_ge t 3 with h | h
  · interval_cases t <;> norm_num
  · have htq : (3 : ℚ) ≤ t := by exact_mod_cast h
    have hB : (1000 / 27 : ℚ) ≤ (10 / 3) ^ t := by
      calc (1000 / 27 : ℚ) = (10 / 3) ^ 3 := by norm_num
        _ ≤ (10 / 3) ^ t := pow_le_pow_right₀ (by norm_num) h
    have h1 : (0 : ℚ) ≤ t / 5 - 13 / 42 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hB h1]

/-- **The leaf-stem step** (ceiling proof, App. R3): at a vertex `v` with `t ≥ 1` leaf neighbours and at
most one other neighbour `u`, the surplus of `s` is paid by the surpluses of `H = s - v - leaves`
and `J = H - u`, except for `t = 1`, `deg_H u = 1`, `ν(H) = ν(J)`, the length-three tail. -/
theorem surplus_leafStem (hG : G.IsAcyclic) {s : Finset V} {v : V} (hv : v ∈ s)
    (hΛ : (leavesAt G s v).Nonempty) (hU : (stemsAt G s v).card ≤ 1)
    (ih : ∀ t ⊂ s, 0 ≤ surplus G t) : 0 ≤ surplus G s := by
  have hZ := Zq_leafStem (G := G) hv
  have hS := Sq_leafStem (G := G) hv
  have hcard := card_eq_residualAt G hv
  obtain ⟨ℓ, hℓ⟩ := hΛ
  have hnu := nuIn_leafStem hℓ
  have hcc := ccIn_leafStem hG hv
  have hHs : residualAt G s v ⊂ s := by
    unfold residualAt
    rw [Finset.ssubset_iff_of_subset ((Finset.sdiff_subset).trans (Finset.erase_subset v s))]
    exact ⟨v, hv, fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl⟩
  have ihH := ih _ hHs
  have ht1 : 1 ≤ (leavesAt G s v).card := Finset.card_pos.mpr ⟨ℓ, hℓ⟩
  set t := (leavesAt G s v).card with htdef
  set H := residualAt G s v with hHdef
  have hB0 : (0 : ℚ) < (10 / 3) ^ t := by positivity
  rcases Nat.lt_or_ge (stemsAt G s v).card 1 with hU0 | hU1
  · -- no stem: a star component
    have hUe : stemsAt G s v = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hUe, Finset.sdiff_empty] at hZ hS
    rw [hUe, Finset.card_empty] at hcc
    have key : surplus G s = ((10 / 3) ^ t + 7 / 3) * surplus G H +
        Zq G H * ((10 / 3 : ℚ) ^ t * (t / 5 - 13 / 42) + 7 / 3 * (29 / 42 - t / 2)) := by
      have e1 : (s.card : ℚ) = H.card + t + 1 := by exact_mod_cast hcard
      have e2 : (nuIn G s : ℚ) = nuIn G H + 1 := by exact_mod_cast hnu
      have e3 : (ccIn G s : ℚ) = ccIn G H + 1 := by
        have : (ccIn G s : ℚ) + 0 = ccIn G H + 1 := by exact_mod_cast hcc
        linarith
      unfold surplus target
      rw [hZ, hS, e1, e2, e3]
      ring
    rw [key]
    have h1 := star_surplus_nonneg ht1
    have h2 := Zq_pos G H
    have h3 : 0 ≤ ((10 / 3 : ℚ) ^ t + 7 / 3) * surplus G H := mul_nonneg (by positivity) ihH
    nlinarith [mul_nonneg h2.le h1]
  · -- one stem `u`
    have hU1' : (stemsAt G s v).card = 1 := by omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hU1'
    have huU : u ∈ stemsAt G s v := by rw [hu]; exact Finset.mem_singleton_self u
    obtain ⟨huN, hun⟩ := mem_stemsAt.mp huU
    have huH : u ∈ H := by
      refine Finset.mem_sdiff.mpr ⟨nbrsIn_subset_erase G s v huN, fun h => ?_⟩
      exact hun (mem_leavesAt.mp h).2
    rw [hu, Finset.sdiff_singleton_eq_erase] at hZ hS
    rw [hU1'] at hcc
    set J := H.erase u with hJdef
    set k := (nbrsIn G H u).card with hkdef
    have hJcc := ccIn_erase hG huH
    rw [← hJdef, ← hkdef] at hJcc
    have hJcard := Finset.card_erase_add_one huH
    rw [← hJdef] at hJcard
    have hJs : J ⊂ s := (Finset.erase_ssubset huH).trans hHs
    have ihJ := ih _ hJs
    have hmono : Zq G J ≤ Zq G H := Zq_mono G (Finset.erase_subset u H)
    have hZJ := Zq_pos G J
    have hm1 : nuIn G J ≤ nuIn G H := nuIn_mono (Finset.erase_subset u H)
    have hm2 : nuIn G H ≤ nuIn G J + 1 := nuIn_le_erase_add_one H u
    -- `k ≥ 1`: `u` has a neighbour in `H`
    have hk1 : 1 ≤ k := by
      have hvu : v ∈ nbrsIn G s u := mem_nbrsIn.mpr ⟨hv, (mem_nbrsIn.mp huN).2.symm⟩
      obtain ⟨y, hy, hyv⟩ : ∃ y ∈ nbrsIn G s u, y ≠ v := by
        by_contra hcon
        push_neg at hcon
        apply hun
        ext y
        rw [Finset.mem_singleton]
        exact ⟨hcon y, fun h => h ▸ hvu⟩
      obtain ⟨hys, huy⟩ := mem_nbrsIn.mp hy
      have hyH : y ∈ H := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hyv, hys⟩, fun hyl => ?_⟩
        have := eq_of_adj_leaf hyl (mem_nbrsIn.mp huN).1 huy.symm
        exact G.ne_of_adj (mem_nbrsIn.mp huN).2 this.symm
      exact Finset.card_pos.mpr ⟨y, mem_nbrsIn.mpr ⟨hyH, huy⟩⟩
    have key : surplus G s = (10 / 3) ^ t * surplus G H + 7 / 3 * surplus G J +
        (10 / 3) ^ t * Zq G H * (t / 5 - 1 / 6) +
        7 / 3 * Zq G J * (k / 7 + ((nuIn G H : ℚ) - nuIn G J) / 3 - t / 2 + 4 / 21) := by
      have e1 : (s.card : ℚ) = H.card + t + 1 := by exact_mod_cast hcard
      have e2 : (nuIn G s : ℚ) = nuIn G H + 1 := by exact_mod_cast hnu
      have e3 : (ccIn G s : ℚ) = ccIn G H := by
        have : (ccIn G s : ℚ) + 1 = ccIn G H + 1 := by exact_mod_cast hcc
        linarith
      have e4 : (J.card : ℚ) = H.card - 1 := by
        have : (J.card : ℚ) + 1 = H.card := by exact_mod_cast hJcard
        linarith
      have e5 : (ccIn G J : ℚ) = ccIn G H + k - 1 := by
        have : (ccIn G J : ℚ) + 1 = ccIn G H + k := by exact_mod_cast hJcc
        linarith
      unfold surplus target
      rw [hZ, hS, e1, e2, e3, e4, e5]
      ring
    rw [key]
    have hA : 0 ≤ (10 / 3 : ℚ) ^ t * surplus G H := mul_nonneg hB0.le ihH
    have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk1
    rcases Nat.lt_or_ge t 2 with ht2 | ht2
    · -- `t = 1`
      have ht1' : t = 1 := by omega
      have htq : (t : ℚ) = 1 := by exact_mod_cast ht1'
      have hBt : (10 / 3 : ℚ) ^ t = 10 / 3 := by rw [ht1']; norm_num
      rw [htq, hBt]
      rw [hBt] at hA
      rcases Nat.lt_or_ge (nuIn G J) (nuIn G H) with hm | hm
      · -- `m = 1`
        have hmq : (nuIn G H : ℚ) - nuIn G J = 1 := by
          have : nuIn G H = nuIn G J + 1 := by omega
          rw [this]; push_cast; ring
        rw [hmq]
        have h1 : 0 ≤ Zq G J * ((k : ℚ) / 7 + 1 / 3 - 1 / 2 + 4 / 21) :=
          mul_nonneg hZJ.le (by linarith)
        have h2 := Zq_pos G H
        linarith
      · -- `m = 0`
        have hmeq : nuIn G H = nuIn G J := le_antisymm hm hm1
        have hmq : (nuIn G H : ℚ) - nuIn G J = 0 := by rw [hmeq]; ring
        rw [hmq]
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · -- `k = 1`: the length-three tail `ℓ - v - u - x`
          have hk1' : k = 1 := by omega
          obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hk1'
          have hΛ1 : leavesAt G s v = {ℓ} := by
            obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (show (leavesAt G s v).card = 1 from ht1')
            rw [ha] at hℓ ⊢
            rw [Finset.mem_singleton.mp hℓ]
          have hℓs : ℓ ∈ s := Finset.mem_of_mem_erase (leavesAt_subset G s v hℓ)
          have hℓv : ℓ ≠ v := (Finset.mem_erase.mp (leavesAt_subset G s v hℓ)).1
          have hvℓ : v ∈ s.erase ℓ := Finset.mem_erase.mpr ⟨hℓv.symm, hv⟩
          have hHeq : (s.erase ℓ).erase v = H := by
            rw [hHdef, residualAt, hΛ1, Finset.sdiff_singleton_eq_erase, Finset.erase_right_comm]
          have huℓ : u ≠ ℓ := fun h => hun (h ▸ (mem_leavesAt.mp hℓ).2)
          have hnbv : nbrsIn G (s.erase ℓ) v = {u} := by
            rw [nbrsIn_erase, nbrsIn_eq_union G s v, hΛ1, hu]
            ext y
            simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
            constructor
            · rintro ⟨hyℓ, hy | hy⟩
              · exact absurd hy hyℓ
              · exact hy
            · rintro rfl
              exact ⟨huℓ, Or.inr rfl⟩
          have hxJ : x ∈ J :=
            nbrsIn_subset_erase G H u (by rw [hx]; exact Finset.mem_singleton_self x)
          have htail : IsTail G s x [ℓ, v, u] := by
            refine ⟨hℓs, (mem_leavesAt.mp hℓ).2, hvℓ, hnbv, ?_, ?_, ?_⟩
            · rw [hHeq]; exact huH
            · rw [hHeq]; exact hx
            · rw [hHeq]; exact hxJ
          have hrest : tailRest s [ℓ, v, u] = J := by
            simp only [tailRest_cons, tailRest_nil]
            rw [hHeq]
          have hess : nuIn G (tailRest s [ℓ, v, u]) =
              nuIn G ((tailRest s [ℓ, v, u]).erase x) + 1 := by
            rw [hrest, ← hmeq]
            exact nuIn_pendant huH hx
          have h3 := surplus_tail3 hG htail rfl hess ih
          rw [key] at h3
          rw [htq, hBt, hmq] at h3
          exact h3
        · -- `k ≥ 2`
          have hkq2 : (2 : ℚ) ≤ k := by exact_mod_cast hk2
          have h1 : 0 ≤ Zq G J * ((k : ℚ) / 7 + 0 / 3 - 1 / 2 + 4 / 21 + 1 / 42) :=
            mul_nonneg hZJ.le (by linarith)
          linarith
    · -- `t ≥ 2`
      have htq : (2 : ℚ) ≤ t := by exact_mod_cast ht2
      have hB : (100 / 9 : ℚ) ≤ (10 / 3) ^ t := by
        calc (100 / 9 : ℚ) = (10 / 3) ^ 2 := by norm_num
          _ ≤ (10 / 3) ^ t := pow_le_pow_right₀ (by norm_num) ht2
      have hmq0 : (0 : ℚ) ≤ (nuIn G H : ℚ) - nuIn G J := by
        have : (nuIn G J : ℚ) ≤ nuIn G H := by exact_mod_cast hm1
        linarith
      set c := (k : ℚ) / 7 + ((nuIn G H : ℚ) - nuIn G J) / 3 - t / 2 + 4 / 21 with hc
      have hc0 : 1 / 3 - (t : ℚ) / 2 ≤ c := by rw [hc]; linarith
      have hJ0 : 0 ≤ 7 / 3 * surplus G J := mul_nonneg (by norm_num) ihJ
      rcases le_total 0 c with hcpos | hcneg
      · have h1 : 0 ≤ (10 / 3 : ℚ) ^ t * Zq G H * (t / 5 - 1 / 6) :=
          mul_nonneg (mul_nonneg hB0.le (Zq_pos G H).le) (by linarith)
        have h2 : 0 ≤ 7 / 3 * Zq G J * c := mul_nonneg (by positivity) hcpos
        linarith
      · have h1 : Zq G H * c ≤ Zq G J * c := mul_le_mul_of_nonpos_right hmono hcneg
        have h2 : 0 ≤ ((10 / 3 : ℚ) ^ t - 100 / 9) * (Zq G H * (t / 5 - 1 / 6)) :=
          mul_nonneg (by linarith) (mul_nonneg (Zq_pos G H).le (by linarith))
        have h3 : Zq G H * (1 / 3 - (t : ℚ) / 2) ≤ Zq G H * c :=
          mul_le_mul_of_nonneg_left hc0 (Zq_pos G H).le
        have h4 : 0 ≤ Zq G H * (19 * (t : ℚ) / 18 - 29 / 27) :=
          mul_nonneg (Zq_pos G H).le (by linarith)
        linarith

/-- **B5 at the level of vertex sets**: `Φ(s) ≥ 0`, i.e. `S(s) ≥ (|s|/2 - ν(s)/3 + cc(s)/7) Z(s)`
at activity `7/3`, for every vertex set `s` of a forest. -/
theorem surplus_nonneg (hG : G.IsAcyclic) (s : Finset V) : 0 ≤ surplus G s := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hiso : ∃ x ∈ s, nbrsIn G s x = ∅
    · obtain ⟨x, hx, hxn⟩ := hiso
      rw [surplus_isolated hG hx hxn]
      have h1 := ih _ (Finset.erase_ssubset hx)
      have h2 := Zq_pos G (s.erase x)
      linarith
    · push_neg at hiso
      rcases s.eq_empty_or_nonempty with rfl | hne
      · rw [surplus_empty]
      · obtain ⟨v, hv, hΛ, hU⟩ := exists_leafStem hG hiso hne
        exact surplus_leafStem hG hv hΛ hU ih

end Induction

section FinBridge

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The Finset-level matching number of the whole vertex set is `matchingNumber`. -/
theorem nuIn_univ : nuIn G Finset.univ = matchingNumber G := by
  symm
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨M, hM, hMc⟩ := exists_isMatchingIn_card_eq G Finset.univ
    refine ⟨(M : Set (Sym2 (Fin n))), fun e he => (hM.1 e he).1, ?_, M.finite_toSet, ?_⟩
    · rw [Set.ncard_coe_finset, hMc]
    · intro e he f hf hef
      exact hM.2 e he f hf hef
  · rintro k ⟨M, hMsub, rfl, hMfin, hMdisj⟩
    have h : IsMatchingIn G Finset.univ hMfin.toFinset := by
      refine ⟨fun e he => ?_, fun e he f hf hef => ?_⟩
      · rw [Set.Finite.mem_toFinset] at he
        exact ⟨hMsub he, fun a _ => Finset.mem_univ a⟩
      · rw [Set.Finite.mem_toFinset] at he hf
        exact hMdisj he hf hef
    rw [Set.ncard_eq_toFinset_card M hMfin]
    exact le_nuIn h

omit [DecidableRel G.Adj] in
theorem reachIn_univ_iff {x y : Fin n} : ReachIn G Finset.univ x y ↔ G.Reachable x y := by
  constructor
  · intro h
    obtain ⟨p, _⟩ := h.exists_walk (Finset.mem_univ y)
    exact ⟨p⟩
  · rintro ⟨p⟩
    exact reachIn_of_walk p (fun v _ => Finset.mem_univ v)

/-- The Finset-level component count of the whole vertex set is the number of connected
components. -/
theorem ccIn_univ : ccIn G Finset.univ = Nat.card G.ConnectedComponent := by
  classical
  let f : G.ConnectedComponent → Finset (Fin n) :=
    fun c => Finset.univ.filter (fun y => G.connectedComponentMk y = c)
  have hf : ∀ x, f (G.connectedComponentMk x) = compIn G Finset.univ x := by
    intro x
    ext y
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and, mem_compIn]
    rw [reachIn_univ_iff, SimpleGraph.ConnectedComponent.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hinj : Function.Injective f := by
    intro c c' h
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h x =>
      have hx : x ∈ f (G.connectedComponentMk x) := by simp [f]
      rw [h] at hx
      simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
  have himage : Finset.univ.image (compIn G Finset.univ) = Finset.univ.image f := by
    ext C
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨G.connectedComponentMk x, hf x⟩
    · rintro ⟨c, rfl⟩
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h x => exact ⟨x, (hf x).symm⟩
  unfold ccIn
  rw [himage, Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]

end FinBridge

end Occupation

open Occupation Finset in
/-- **B5 (occupation at activity 7/3), ceiling proof, Appendix R3**: for every finite forest,
`W(F) + cc(F)/7 ≤ μ_F(7/3)`, where `W(F) = n/2 - ν(F)/3` and `cc` counts components including
isolated vertices. -/
theorem occupationAt73 : OccupationAt73 := by
  intro F
  classical
  have hG := F.isForest
  have key := surplus_nonneg (G := F.graph) hG Finset.univ
  have hcount : ∀ k, (indepCount F.graph Finset.univ k : ℝ) = (independenceCount F k : ℝ) := by
    intro k
    rw [indepCount_univ]
    unfold independenceCount
    rfl
  have hcard : (Finset.univ : Finset (Fin F.n)).card = F.n := by simp
  have hZ : ((Zq F.graph Finset.univ : ℚ) : ℝ) = partitionFn F (7 / 3) := by
    rw [Zq_eq_sum_count, hcard]
    unfold partitionFn
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [hcount k]
  have hS : ((Sq F.graph Finset.univ : ℚ) : ℝ) =
      ∑ k ∈ range (F.n + 1), (k : ℝ) * (independenceCount F k : ℝ) * (7 / 3 : ℝ) ^ k := by
    rw [Sq_eq_sum_count, hcard]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [hcount k]
  have hT : ((target F.graph Finset.univ : ℚ) : ℝ) =
      matchingEnvelopeMean F + (numComponents F : ℝ) / 7 := by
    unfold target matchingEnvelopeMean numComponents
    rw [hcard, nuIn_univ, ccIn_univ]
    push_cast
    ring
  have hZpos : 0 < partitionFn F (7 / 3) := by
    rw [← hZ]
    exact_mod_cast Zq_pos F.graph Finset.univ
  unfold hardCoreMean
  rw [le_div_iff₀ hZpos, ← hZ, ← hS, ← hT]
  unfold surplus at key
  have key' : ((0 : ℚ) : ℝ) ≤ ((Sq F.graph Finset.univ - target F.graph Finset.univ *
      Zq F.graph Finset.univ : ℚ) : ℝ) := by exact_mod_cast key
  push_cast at key'
  linarith

end Erdos993Lean
