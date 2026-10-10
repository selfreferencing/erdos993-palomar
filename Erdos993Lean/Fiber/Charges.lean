module

public import Mathlib
public import Erdos993Lean.Zhang.Decomposition

/-!
# The matching-excess inequality (the blocker-charge payment)

Source: the note *A matching-excess consumer for forest-generated
binomial fibers* (29 September 2026),
Section 3: Theorem 3.1 and
its exact decomposition (5).

## Setting

A simple graph `G` on a vertex type `V`; finite vertex sets `A` (in the application a maximum
independent set of a forest) and `C` (in the application the complement of `A`), `a = |A|`,
`c = |C|`; and a map `μ : V → V` that matches `C` into `A`: `μ` is injective on `C`, and
`μ v ∈ A`, `v ~ μ v` for `v ∈ C`.  **No acyclicity, no independence of `A` and no disjointness
of `A` and `C` is used**: the statements below hold in this generality (in the application all of
them are true and may simply be dropped).  The hypothesis `U ≤ a - c` is the exposed-leaf lemma
(Lemma 2.2 of the source), supplied here as a hypothesis; `unmatchedExcess_le_of_exposed` derives
it from "every unmatched vertex of `A` has at most one neighbour in `C`", and
`unmatchedExcess_le_of_degree_le_one` from "every unmatched vertex of `A` has degree at most 1"
(the form of Lemma 2.2 proved in the `Fiber` namespace); `matchingExcess_nonneg_of_exposedLeaves` is
Theorem 3.1 with that hypothesis.

## Objects (the names of the source)

* `crossEdges G A C`: the cross edges `(v, b)`, `v ∈ C`, `b ∈ A`, `v ~ b`; `D = |crossEdges|`,
  and `card_crossEdges`: `D = Σ_{v ∈ C} |N(v) ∩ A|`.
* `excessEdges G A C μ` = `E*`: the cross edges `(v, b)` with `b ≠ μ v`;
  `card_excessEdges_add`: `|E*| + c = D`.
* `unmatchedExcess G A C μ` = `U`: the edges of `E*` whose `A`-endpoint lies outside `μ(C)`.
* `Eligible C μ J (v, b)`: `v ∈ J` and (`b ∉ μ(C)` or `μ⁻¹(b) ∉ J`), with `μ⁻¹(b) ∉ J` read as
  "no `w ∈ C` with `μ w = b` lies in `J`"; `eligibleEdges G A C μ J` = `E*(J)`.
* `nbhdIn G A J` = `N_A(J)` = `A \ Zhang.avail G A J`, the blockers of `J` (so
  `|N_A(J)| = a - m(J)` with Zhang's `m(J) = |avail G A J|`, `card_nbhdIn`).
* `indepSubsets G C h`: the independent `h`-subsets of `C`; `card_indepSubsets`:
  its cardinality is the package's `indepCount G C h` (`N_h`).
* `blockerCharge G A C h` = `R_h = Σ_{J} (|N_A(J)| - h)` over the independent `h`-subsets of `C`
  (`= Σ_m (a - m - h) N[h, m]` of the source).
* `matchingExcess G A C h` = `S^M_h = (D - c) C(c-2, h-1) + (a - c) C(c-2, h-2) - R_h` (in `ℤ`).

## Main results

* `step1_injectiveCharge` (**Step 1**, the injective charge): for every `J ⊆ C`,
  `|N_A(J)| - |J| = |N_A(J) \ μ(J)| ≤ |E*(J)|`; `card_le_card_nbhdIn`: `|J| ≤ |N_A(J)|`.
  (The source states it for independent `J`; independence is not needed.)
* `sum_card_eligible_eq`, `step2_totalEligibility` (**Step 2**, total eligibility):
  `Σ_{J ⊆ C, |J| = h} |E*(J)| = U C(c-1, h-1) + (|E*| - U) C(c-2, h-1)
    = (D - c) C(c-2, h-1) + U C(c-2, h-2)`  (`2 ≤ h ≤ c`).
* `blockerCharge_le`, `matchingExcess_nonneg` (**Theorem 3.1**): `R_h ≤ (D - c) C(c-2, h-1) +
  (a - c) C(c-2, h-2)`, i.e. `S^M_h ≥ 0`, for `2 ≤ h ≤ c`, given `U ≤ a - c`.
* `matchingExcess_eq` (**the exact decomposition (5)**): `S^M_h = (a - c - U) C(c-2, h-2)
  + Σ_{|J| = h, J not independent} |E*(J)| + Σ_{|J| = h, J independent} (|E*(J)| - |N_A(J) \ μ(J)|)`,
  each term an object-level count (unused exposed capacity, charges on forbidden `J`, unassigned
  eligible edges).

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean
namespace Fiber

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The objects -/

variable (G) in
/-- The cross edges `(v, b)` with `v ∈ C`, `b ∈ A` and `v ~ b`.  `D = |crossEdges G A C|`. -/
def crossEdges (A C : Finset V) : Finset (V × V) :=
  (C ×ˢ A).filter (fun p => G.Adj p.1 p.2)

variable (G) in
/-- `E*`: the cross edges that are not matching edges, `(v, b)` with `b ≠ μ v`. -/
def excessEdges (A C : Finset V) (μ : V → V) : Finset (V × V) :=
  (crossEdges G A C).filter (fun p => p.2 ≠ μ p.1)

variable (G) in
/-- `U`: the number of edges of `E*` whose `A`-endpoint is unmatched (lies outside `μ(C)`). -/
def unmatchedExcess (A C : Finset V) (μ : V → V) : ℕ :=
  ((excessEdges G A C μ).filter (fun p => p.2 ∉ C.image μ)).card

/-- Eligibility (Theorem 3.1 of the source): an edge `(v, b)` is eligible for `J` if `v ∈ J` and
either `b` is unmatched (`b ∉ μ(C)`) or its matching partner `μ⁻¹(b)` lies outside `J` (no
`w ∈ C` with `μ w = b` lies in `J`). -/
def Eligible (C : Finset V) (μ : V → V) (J : Finset V) (p : V × V) : Prop :=
  p.1 ∈ J ∧ (p.2 ∉ C.image μ ∨ ∀ w ∈ C, μ w = p.2 → w ∉ J)

instance (C : Finset V) (μ : V → V) (J : Finset V) : DecidablePred (Eligible C μ J) :=
  fun _ => by unfold Eligible; infer_instance

variable (G) in
/-- `E*(J)`: the edges of `E*` eligible for `J`. -/
def eligibleEdges (A C : Finset V) (μ : V → V) (J : Finset V) : Finset (V × V) :=
  (excessEdges G A C μ).filter (Eligible C μ J)

variable (G) in
/-- `N_A(J)`: the vertices of `A` with a neighbour in `J` (the blockers of `J`), i.e.
`A \ Zhang.avail G A J`. -/
def nbhdIn (A J : Finset V) : Finset V :=
  A \ Zhang.avail G A J

variable (G) in
/-- The independent `h`-subsets of `C`; their number is `N_h = indepCount G C h`
(`card_indepSubsets`). -/
def indepSubsets (C : Finset V) (h : ℕ) : Finset (Finset V) :=
  (C.powersetCard h).filter (IsIndepFinset G)

variable (G) in
/-- The blocker charge `R_h = Σ_J (|N_A(J)| - h)`, the sum over the independent `h`-subsets `J`
of `C` (the subtraction is exact, `card_le_card_nbhdIn`). -/
def blockerCharge (A C : Finset V) (h : ℕ) : ℕ :=
  ∑ J ∈ indepSubsets G C h, ((nbhdIn G A J).card - h)

variable (G) in
/-- The matching excess `S^M_h = (D - c) C(c-2, h-1) + (a - c) C(c-2, h-2) - R_h`, in `ℤ`, with
`D = |crossEdges G A C|`, `a = |A|`, `c = |C|` and `R_h` summed in `ℤ`. -/
def matchingExcess (A C : Finset V) (h : ℕ) : ℤ :=
  (((crossEdges G A C).card : ℤ) - C.card) * ((C.card - 2).choose (h - 1) : ℕ) +
    ((A.card : ℤ) - C.card) * ((C.card - 2).choose (h - 2) : ℕ) -
    ∑ J ∈ indepSubsets G C h, (((nbhdIn G A J).card : ℤ) - h)

/-! ### Basic facts -/

section Basic

variable {A C J : Finset V} {μ : V → V}

omit [DecidableEq V] in
theorem mem_crossEdges {p : V × V} :
    p ∈ crossEdges G A C ↔ p.1 ∈ C ∧ p.2 ∈ A ∧ G.Adj p.1 p.2 := by
  unfold crossEdges
  rw [mem_filter, mem_product, and_assoc]

theorem mem_excessEdges {p : V × V} :
    p ∈ excessEdges G A C μ ↔ p.1 ∈ C ∧ p.2 ∈ A ∧ G.Adj p.1 p.2 ∧ p.2 ≠ μ p.1 := by
  unfold excessEdges
  rw [mem_filter, mem_crossEdges, and_assoc, and_assoc]

theorem mem_nbhdIn {b : V} : b ∈ nbhdIn G A J ↔ b ∈ A ∧ ∃ v ∈ J, G.Adj v b := by
  unfold nbhdIn
  rw [mem_sdiff, Zhang.mem_avail]
  constructor
  · rintro ⟨hb, hn⟩
    refine ⟨hb, ?_⟩
    by_contra hc
    push_neg at hc
    exact hn ⟨hb, hc⟩
  · rintro ⟨hb, v, hv, hvb⟩
    exact ⟨hb, fun h => h.2 v hv hvb⟩

/-- `|N_A(J)| = a - m(J)`, with Zhang's `m(J) = |A \ N_A(J)| = |avail G A J|`. -/
theorem card_nbhdIn : (nbhdIn G A J).card = A.card - (Zhang.avail G A J).card := by
  unfold nbhdIn
  exact card_sdiff_of_subset (Zhang.avail_subset G A J)

omit [DecidableEq V] in
/-- `D = Σ_{v ∈ C} |N(v) ∩ A|`. -/
theorem card_crossEdges : (crossEdges G A C).card = ∑ v ∈ C, (A.filter (G.Adj v)).card := by
  unfold crossEdges
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun v _ => ?_)
  rw [card_filter]

omit [DecidableEq V] in
/-- `N_h`: the number of independent `h`-subsets of `C` is the package's `indepCount G C h`. -/
theorem card_indepSubsets (h : ℕ) : (indepSubsets G C h).card = indepCount G C h := by
  unfold indepSubsets indepCount
  congr 1
  ext J
  simp only [mem_filter, mem_powersetCard, mem_powerset]
  tauto

/-- For `J ⊆ C`, eligibility of `(v, b)` means `v ∈ J` and `b ∉ μ(J)`. -/
theorem eligible_iff (hJC : J ⊆ C) {p : V × V} :
    Eligible C μ J p ↔ p.1 ∈ J ∧ p.2 ∉ J.image μ := by
  unfold Eligible
  apply and_congr_right
  intro _
  constructor
  · rintro (h | h)
    · exact fun hJ => h (image_subset_image hJC hJ)
    · intro hJ
      obtain ⟨w, hw, hwp⟩ := mem_image.mp hJ
      exact h w (hJC hw) hwp hw
  · intro h
    right
    intro w _ hwp hwJ
    exact h (mem_image.mpr ⟨w, hwJ, hwp⟩)

theorem mem_eligibleEdges (hJC : J ⊆ C) {p : V × V} :
    p ∈ eligibleEdges G A C μ J ↔ p ∈ excessEdges G A C μ ∧ p.1 ∈ J ∧ p.2 ∉ J.image μ := by
  unfold eligibleEdges
  rw [mem_filter, eligible_iff hJC]

/-- A matching of `C` into `A` gives `c ≤ a`. -/
theorem card_le_card_of_matching (hμA : ∀ v ∈ C, μ v ∈ A) (hμinj : Set.InjOn μ C) :
    C.card ≤ A.card := by
  rw [← card_image_of_injOn hμinj]
  apply card_le_card
  intro b hb
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
  exact hμA v hv

/-- `|E*| + c = D`: the cross edges split into `E*` and the `c` matching edges. -/
theorem card_excessEdges_add (hμA : ∀ v ∈ C, μ v ∈ A) (hμadj : ∀ v ∈ C, G.Adj v (μ v)) :
    (excessEdges G A C μ).card + C.card = (crossEdges G A C).card := by
  have hmatch : (crossEdges G A C).filter (fun p => ¬ p.2 ≠ μ p.1) =
      C.image (fun v => (v, μ v)) := by
    ext p
    rw [mem_filter, mem_crossEdges, mem_image, not_ne_iff]
    constructor
    · rintro ⟨⟨hpC, -, -⟩, hp⟩
      exact ⟨p.1, hpC, Prod.ext rfl hp.symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨hv, hμA v hv, hμadj v hv⟩, rfl⟩
  have hcard : (C.image (fun v => (v, μ v))).card = C.card :=
    card_image_of_injective _ (fun x y hxy => congrArg Prod.fst hxy)
  rw [← card_filter_add_card_filter_not (s := crossEdges G A C) (fun p => p.2 ≠ μ p.1), hmatch,
    hcard]
  rfl

/-- `c ≤ D`. -/
theorem card_le_card_crossEdges (hμA : ∀ v ∈ C, μ v ∈ A) (hμadj : ∀ v ∈ C, G.Adj v (μ v)) :
    C.card ≤ (crossEdges G A C).card := by
  rw [← card_excessEdges_add hμA hμadj]
  exact Nat.le_add_left _ _

/-- `U ≤ |E*|`. -/
theorem unmatchedExcess_le_card : unmatchedExcess G A C μ ≤ (excessEdges G A C μ).card := by
  unfold unmatchedExcess
  exact card_filter_le _ _

end Basic

/-! ### Counting `h`-subsets through prescribed vertices -/

section Counting

/-- The `h`-subsets of `S` containing a fixed `P ⊆ S` number `C(|S| - |P|, h - |P|)`. -/
theorem card_powersetCard_filter_superset {S P : Finset V} (hPS : P ⊆ S) {h : ℕ}
    (hPh : P.card ≤ h) :
    ((S.powersetCard h).filter (fun J => P ⊆ J)).card = (S.card - P.card).choose (h - P.card) := by
  rw [← card_sdiff_of_subset hPS, ← card_powersetCard]
  have hdisj : ∀ K : Finset V, K ⊆ S \ P → Disjoint K P := by
    intro K hK
    rw [disjoint_left]
    intro x hxK hxP
    exact (mem_sdiff.mp (hK hxK)).2 hxP
  refine card_nbij' (fun J => J \ P) (fun K => K ∪ P) ?_ ?_ ?_ ?_
  · intro J hJ
    simp only [coe_filter, mem_powersetCard, Set.mem_setOf_eq, mem_coe] at hJ ⊢
    obtain ⟨⟨hJS, hJc⟩, hPJ⟩ := hJ
    exact ⟨sdiff_subset_sdiff hJS subset_rfl, by rw [card_sdiff_of_subset hPJ, hJc]⟩
  · intro K hK
    simp only [coe_filter, mem_powersetCard, Set.mem_setOf_eq, mem_coe] at hK ⊢
    obtain ⟨hKS, hKc⟩ := hK
    refine ⟨⟨union_subset (hKS.trans sdiff_subset) hPS, ?_⟩, subset_union_right⟩
    rw [card_union_of_disjoint (hdisj K hKS), hKc]
    omega
  · intro J hJ
    simp only [coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hJ
    exact sdiff_union_of_subset hJ.2
  · intro K hK
    simp only [mem_powersetCard, mem_coe] at hK
    exact union_sdiff_cancel_right (hdisj K hK.1)

/-- The `h`-subsets of `S` containing a fixed `v ∈ S` number `C(|S| - 1, h - 1)`. -/
theorem card_powersetCard_filter_mem {S : Finset V} {v : V} (hv : v ∈ S) {h : ℕ} (hh : 1 ≤ h) :
    ((S.powersetCard h).filter (fun J => v ∈ J)).card = (S.card - 1).choose (h - 1) := by
  have hP : ({v} : Finset V) ⊆ S := singleton_subset_iff.mpr hv
  have h1 := card_powersetCard_filter_superset hP (h := h) (by rw [card_singleton]; exact hh)
  rw [card_singleton] at h1
  rw [← h1]
  congr 1
  ext J
  simp only [mem_filter, singleton_subset_iff]

/-- The `h`-subsets of `S` containing `v ∈ S` and avoiding `w ∈ S`, `w ≠ v`, number
`C(|S| - 2, h - 1)`. -/
theorem card_powersetCard_filter_mem_not_mem {S : Finset V} {v w : V} (hv : v ∈ S) (hw : w ∈ S)
    (hvw : v ≠ w) {h : ℕ} (hh : 1 ≤ h) :
    ((S.powersetCard h).filter (fun J => v ∈ J ∧ w ∉ J)).card = (S.card - 2).choose (h - 1) := by
  have heq : (S.powersetCard h).filter (fun J => v ∈ J ∧ w ∉ J) =
      ((S.erase w).powersetCard h).filter (fun J => v ∈ J) := by
    ext J
    simp only [mem_filter, mem_powersetCard, subset_erase]
    tauto
  rw [heq, card_powersetCard_filter_mem (mem_erase.mpr ⟨hvw, hv⟩) hh, card_erase_of_mem hw,
    show S.card - 1 - 1 = S.card - 2 by omega]

end Counting

/-! ### Step 1: the injective charge -/

section Step1

variable {A C J : Finset V} {μ : V → V}

/-- `μ(J) ⊆ N_A(J)` for `J ⊆ C`. -/
theorem image_subset_nbhdIn (hJC : J ⊆ C) (hμA : ∀ v ∈ C, μ v ∈ A)
    (hμadj : ∀ v ∈ C, G.Adj v (μ v)) : J.image μ ⊆ nbhdIn G A J := by
  intro b hb
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
  exact mem_nbhdIn.mpr ⟨hμA v (hJC hv), v, hv, hμadj v (hJC hv)⟩

/-- `|J| ≤ |N_A(J)|` for `J ⊆ C` (so the subtraction in `R_h` is exact). -/
theorem card_le_card_nbhdIn (hJC : J ⊆ C) (hμA : ∀ v ∈ C, μ v ∈ A)
    (hμadj : ∀ v ∈ C, G.Adj v (μ v)) (hμinj : Set.InjOn μ C) :
    J.card ≤ (nbhdIn G A J).card := by
  rw [← card_image_of_injOn (hμinj.mono (coe_subset.mpr hJC))]
  exact card_le_card (image_subset_nbhdIn hJC hμA hμadj)

/-- `|N_A(J) \ μ(J)| = |N_A(J)| - |J|` for `J ⊆ C`. -/
theorem card_nbhdIn_sdiff_image (hJC : J ⊆ C) (hμA : ∀ v ∈ C, μ v ∈ A)
    (hμadj : ∀ v ∈ C, G.Adj v (μ v)) (hμinj : Set.InjOn μ C) :
    (nbhdIn G A J \ J.image μ).card = (nbhdIn G A J).card - J.card := by
  rw [card_sdiff_of_subset (image_subset_nbhdIn hJC hμA hμadj),
    card_image_of_injOn (hμinj.mono (coe_subset.mpr hJC))]

/-- Every excess blocker `b ∈ N_A(J) \ μ(J)` is the `A`-endpoint of an eligible edge of `J`. -/
theorem sdiff_image_subset_image_eligibleEdges (hJC : J ⊆ C) :
    nbhdIn G A J \ J.image μ ⊆ (eligibleEdges G A C μ J).image Prod.snd := by
  intro b hb
  rw [mem_sdiff, mem_nbhdIn] at hb
  obtain ⟨⟨hbA, v, hvJ, hvb⟩, hbJ⟩ := hb
  refine mem_image.mpr ⟨(v, b), ?_, rfl⟩
  rw [mem_eligibleEdges hJC, mem_excessEdges]
  refine ⟨⟨hJC hvJ, hbA, hvb, ?_⟩, hvJ, hbJ⟩
  intro heq
  exact hbJ (mem_image.mpr ⟨v, hvJ, heq.symm⟩)

/-- **Step 1 (the injective charge).**  For every `J ⊆ C` (independent or not),
`|N_A(J) \ μ(J)| ≤ |E*(J)|`: distinct excess blockers are endpoints of distinct eligible edges. -/
theorem card_nbhdIn_sdiff_image_le (hJC : J ⊆ C) :
    (nbhdIn G A J \ J.image μ).card ≤ (eligibleEdges G A C μ J).card :=
  (card_le_card (sdiff_image_subset_image_eligibleEdges hJC)).trans card_image_le

/-- **Step 1 (the injective charge), counted form**: `|N_A(J)| - |J| ≤ |E*(J)|` for `J ⊆ C`. -/
theorem step1_injectiveCharge (hJC : J ⊆ C) (hμA : ∀ v ∈ C, μ v ∈ A)
    (hμadj : ∀ v ∈ C, G.Adj v (μ v)) (hμinj : Set.InjOn μ C) :
    (nbhdIn G A J).card - J.card ≤ (eligibleEdges G A C μ J).card := by
  rw [← card_nbhdIn_sdiff_image hJC hμA hμadj hμinj]
  exact card_nbhdIn_sdiff_image_le hJC

end Step1

/-! ### Step 2: total eligibility -/

section Step2

variable {A C : Finset V} {μ : V → V}

/-- **Step 2 (total eligibility), first form**: an edge of `E*` ending at an unmatched vertex is
eligible for the `C(c-1, h-1)` subsets containing its `C`-endpoint, one ending at `μ v'` for the
`C(c-2, h-1)` subsets containing its `C`-endpoint and not `v'`.  Hence, for `1 ≤ h`,
`Σ_{J ⊆ C, |J| = h} |E*(J)| = U C(c-1, h-1) + (|E*| - U) C(c-2, h-1)`. -/
theorem sum_card_eligible_eq (hμinj : Set.InjOn μ C) {h : ℕ} (hh : 1 ≤ h) :
    ∑ J ∈ C.powersetCard h, (eligibleEdges G A C μ J).card =
      unmatchedExcess G A C μ * (C.card - 1).choose (h - 1) +
        ((excessEdges G A C μ).card - unmatchedExcess G A C μ) * (C.card - 2).choose (h - 1) := by
  have hswap : ∑ J ∈ C.powersetCard h, (eligibleEdges G A C μ J).card =
      ∑ p ∈ excessEdges G A C μ, ((C.powersetCard h).filter (fun J => Eligible C μ J p)).card := by
    simp only [eligibleEdges, card_filter]
    exact sum_comm
  have hcount : ∀ p ∈ excessEdges G A C μ,
      ((C.powersetCard h).filter (fun J => Eligible C μ J p)).card =
        if p.2 ∉ C.image μ then (C.card - 1).choose (h - 1) else (C.card - 2).choose (h - 1) := by
    intro p hp
    rw [mem_excessEdges] at hp
    obtain ⟨hpC, _, _, hne⟩ := hp
    split_ifs with hin
    · -- an edge to `μ w`, `w ≠ v`: eligible iff `v ∈ J` and `w ∉ J`
      obtain ⟨w, hwC, hwp⟩ := mem_image.mp hin
      have hvw : p.1 ≠ w := fun heq => hne (by rw [← hwp, heq])
      rw [← card_powersetCard_filter_mem_not_mem hpC hwC hvw hh]
      congr 1
      apply filter_congr
      intro J hJ
      rw [mem_powersetCard] at hJ
      rw [eligible_iff hJ.1]
      apply and_congr_right
      intro _
      constructor
      · intro hn hwJ
        exact hn (mem_image.mpr ⟨w, hwJ, hwp⟩)
      · intro hwJ hmem
        obtain ⟨x, hxJ, hx⟩ := mem_image.mp hmem
        have hxw : x = w := hμinj (mem_coe.mpr (hJ.1 hxJ)) (mem_coe.mpr hwC) (hx.trans hwp.symm)
        exact hwJ (hxw ▸ hxJ)
    · -- an edge to an unmatched vertex: eligible iff its `C`-endpoint is in `J`
      rw [← card_powersetCard_filter_mem hpC hh]
      congr 1
      apply filter_congr
      intro J hJ
      rw [mem_powersetCard] at hJ
      rw [eligible_iff hJ.1]
      exact ⟨fun h => h.1, fun h => ⟨h, fun hJ' => hin (image_subset_image hJ.1 hJ')⟩⟩
  rw [hswap, sum_congr rfl hcount, sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
  have hsplit := card_filter_add_card_filter_not (s := excessEdges G A C μ)
    (fun p => p.2 ∉ C.image μ)
  unfold unmatchedExcess
  rw [← hsplit, Nat.add_sub_cancel_left]

/-- **Step 2 (total eligibility)**: for `2 ≤ h ≤ c`,
`Σ_{J ⊆ C, |J| = h} |E*(J)| = (D - c) C(c-2, h-1) + U C(c-2, h-2)` (Pascal). -/
theorem step2_totalEligibility (hμA : ∀ v ∈ C, μ v ∈ A) (hμadj : ∀ v ∈ C, G.Adj v (μ v))
    (hμinj : Set.InjOn μ C) {h : ℕ} (h2 : 2 ≤ h) (hhc : h ≤ C.card) :
    ∑ J ∈ C.powersetCard h, (eligibleEdges G A C μ J).card =
      ((crossEdges G A C).card - C.card) * (C.card - 2).choose (h - 1) +
        unmatchedExcess G A C μ * (C.card - 2).choose (h - 2) := by
  rw [sum_card_eligible_eq hμinj (by omega : 1 ≤ h)]
  have hE : (crossEdges G A C).card - C.card = (excessEdges G A C μ).card := by
    rw [← card_excessEdges_add hμA hμadj, Nat.add_sub_cancel]
  rw [hE]
  have hp : (C.card - 1).choose (h - 1) =
      (C.card - 2).choose (h - 2) + (C.card - 2).choose (h - 1) := by
    obtain ⟨c', hc'⟩ : ∃ c', C.card = c' + 2 := ⟨C.card - 2, by omega⟩
    obtain ⟨h', hh'⟩ : ∃ h', h = h' + 2 := ⟨h - 2, by omega⟩
    rw [hc', hh', show c' + 2 - 1 = c' + 1 by omega, show h' + 2 - 1 = h' + 1 by omega,
      show c' + 2 - 2 = c' by omega, show h' + 2 - 2 = h' by omega]
    exact Nat.choose_succ_succ' c' h'
  rw [hp]
  obtain ⟨R, hR⟩ := Nat.exists_eq_add_of_le (unmatchedExcess_le_card (G := G) (A := A) (C := C)
    (μ := μ))
  rw [hR, Nat.add_sub_cancel_left]
  ring

end Step2

/-! ### Theorem 3.1 -/

section Theorem

variable {A C : Finset V} {μ : V → V}

/-- **Theorem 3.1 (the matching-excess inequality), natural-number form.**  Let `μ` match `C`
into `A` (`μ` injective on `C`, `μ v ∈ A`, `v ~ μ v`) with at most `a - c` excess edges to
unmatched vertices (`U ≤ a - c`).  Then for `2 ≤ h ≤ c`,
`R_h ≤ (D - c) C(c-2, h-1) + (a - c) C(c-2, h-2)`. -/
theorem blockerCharge_le (hμA : ∀ v ∈ C, μ v ∈ A) (hμadj : ∀ v ∈ C, G.Adj v (μ v))
    (hμinj : Set.InjOn μ C) (hU : unmatchedExcess G A C μ ≤ A.card - C.card) {h : ℕ}
    (h2 : 2 ≤ h) (hhc : h ≤ C.card) :
    blockerCharge G A C h ≤
      ((crossEdges G A C).card - C.card) * (C.card - 2).choose (h - 1) +
        (A.card - C.card) * (C.card - 2).choose (h - 2) := by
  calc blockerCharge G A C h
      ≤ ∑ J ∈ indepSubsets G C h, (eligibleEdges G A C μ J).card := by
        unfold blockerCharge
        apply sum_le_sum
        intro J hJ
        simp only [indepSubsets, mem_filter, mem_powersetCard] at hJ
        have h1 := step1_injectiveCharge hJ.1.1 hμA hμadj hμinj (G := G)
        rw [hJ.1.2] at h1
        exact h1
    _ ≤ ∑ J ∈ C.powersetCard h, (eligibleEdges G A C μ J).card :=
        sum_le_sum_of_subset (filter_subset _ _)
    _ = ((crossEdges G A C).card - C.card) * (C.card - 2).choose (h - 1) +
          unmatchedExcess G A C μ * (C.card - 2).choose (h - 2) :=
        step2_totalEligibility hμA hμadj hμinj h2 hhc
    _ ≤ ((crossEdges G A C).card - C.card) * (C.card - 2).choose (h - 1) +
          (A.card - C.card) * (C.card - 2).choose (h - 2) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hU) _

/-- `R_h` in `ℤ`: `(R_h : ℤ) = Σ_J (|N_A(J)| - h)` with the subtraction in `ℤ`. -/
theorem blockerCharge_cast (hμA : ∀ v ∈ C, μ v ∈ A) (hμadj : ∀ v ∈ C, G.Adj v (μ v))
    (hμinj : Set.InjOn μ C) (h : ℕ) :
    ((blockerCharge G A C h : ℕ) : ℤ) =
      ∑ J ∈ indepSubsets G C h, (((nbhdIn G A J).card : ℤ) - h) := by
  unfold blockerCharge
  rw [Nat.cast_sum]
  apply sum_congr rfl
  intro J hJ
  simp only [indepSubsets, mem_filter, mem_powersetCard] at hJ
  have hJh : h ≤ (nbhdIn G A J).card := by
    rw [← hJ.1.2]
    exact card_le_card_nbhdIn hJ.1.1 hμA hμadj hμinj
  rw [Nat.cast_sub hJh]

/-- **Theorem 3.1 (the matching-excess inequality).**  Let `μ` match `C` into `A` (`μ` injective
on `C`, `μ v ∈ A` and `v ~ μ v` for `v ∈ C`) with `U ≤ a - c` (the exposed-leaf lemma).  Then for
every `2 ≤ h ≤ c`, `S^M_h = (D - c) C(c-2, h-1) + (a - c) C(c-2, h-2) - R_h ≥ 0`.
(Neither the independence of `A` nor acyclicity is needed.) -/
theorem matchingExcess_nonneg (hμA : ∀ v ∈ C, μ v ∈ A) (hμadj : ∀ v ∈ C, G.Adj v (μ v))
    (hμinj : Set.InjOn μ C) (hU : unmatchedExcess G A C μ ≤ A.card - C.card) {h : ℕ}
    (h2 : 2 ≤ h) (hhc : h ≤ C.card) :
    0 ≤ matchingExcess G A C h := by
  have hmain := blockerCharge_le hμA hμadj hμinj hU h2 hhc
  have hcD := card_le_card_crossEdges hμA hμadj (G := G)
  have hca := card_le_card_of_matching hμA hμinj
  have hmainZ : ((blockerCharge G A C h : ℕ) : ℤ) ≤
      ((((crossEdges G A C).card - C.card) * (C.card - 2).choose (h - 1) +
        (A.card - C.card) * (C.card - 2).choose (h - 2) : ℕ) : ℤ) := by
    exact_mod_cast hmain
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hcD, Nat.cast_sub hca] at hmainZ
  unfold matchingExcess
  rw [← blockerCharge_cast hμA hμadj hμinj h, sub_nonneg]
  exact hmainZ

/-- **The exact decomposition (5) of the matching excess.**  For `2 ≤ h ≤ c`,
`S^M_h = (a - c - U) C(c-2, h-2) + Σ_{|J| = h, J not independent} |E*(J)|
  + Σ_{|J| = h, J independent} (|E*(J)| - |N_A(J) \ μ(J)|)`
(`J` ranging over subsets of `C`): unused exposed capacity, charges on forbidden `J`, and
unassigned eligible edges.  Each term is nonnegative when `U ≤ a - c` (Step 1). -/
theorem matchingExcess_eq (hμA : ∀ v ∈ C, μ v ∈ A) (hμadj : ∀ v ∈ C, G.Adj v (μ v))
    (hμinj : Set.InjOn μ C) {h : ℕ} (h2 : 2 ≤ h) (hhc : h ≤ C.card) :
    matchingExcess G A C h =
      ((A.card : ℤ) - C.card - unmatchedExcess G A C μ) * ((C.card - 2).choose (h - 2) : ℕ) +
        ∑ J ∈ (C.powersetCard h).filter (fun J => ¬ IsIndepFinset G J),
          ((eligibleEdges G A C μ J).card : ℤ) +
        ∑ J ∈ indepSubsets G C h,
          (((eligibleEdges G A C μ J).card : ℤ) - (nbhdIn G A J \ J.image μ).card) := by
  have hcD := card_le_card_crossEdges hμA hμadj (G := G)
  have hT : ∑ J ∈ C.powersetCard h, ((eligibleEdges G A C μ J).card : ℤ) =
      (((crossEdges G A C).card : ℤ) - C.card) * ((C.card - 2).choose (h - 1) : ℕ) +
        (unmatchedExcess G A C μ : ℤ) * ((C.card - 2).choose (h - 2) : ℕ) := by
    rw [← Nat.cast_sum, step2_totalEligibility hμA hμadj hμinj h2 hhc, Nat.cast_add, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_sub hcD]
  have hsplit : ∑ J ∈ C.powersetCard h, ((eligibleEdges G A C μ J).card : ℤ) =
      ∑ J ∈ (C.powersetCard h).filter (fun J => ¬ IsIndepFinset G J),
          ((eligibleEdges G A C μ J).card : ℤ) +
        ∑ J ∈ indepSubsets G C h, ((eligibleEdges G A C μ J).card : ℤ) := by
    rw [add_comm]
    exact (sum_filter_add_sum_filter_not _ _ _).symm
  have hR : ∑ J ∈ indepSubsets G C h, (((nbhdIn G A J).card : ℤ) - h) =
      ∑ J ∈ indepSubsets G C h, ((nbhdIn G A J \ J.image μ).card : ℤ) := by
    apply sum_congr rfl
    intro J hJ
    simp only [indepSubsets, mem_filter, mem_powersetCard] at hJ
    rw [card_nbhdIn_sdiff_image hJ.1.1 hμA hμadj hμinj, hJ.1.2,
      Nat.cast_sub (by rw [← hJ.1.2]; exact card_le_card_nbhdIn hJ.1.1 hμA hμadj hμinj)]
  unfold matchingExcess
  rw [hR, sum_sub_distrib]
  linear_combination hsplit - hT

end Theorem

/-! ### The exposed-leaf hypothesis -/

section Exposed

variable {A C : Finset V} {μ : V → V}

/-- `U ≤ a - c` when every unmatched vertex of `A` (outside `μ(C)`) has at most one neighbour in
`C` (in the application: the unmatched vertices are leaves or isolated, Lemma 2.2 of the source). -/
theorem unmatchedExcess_le_of_exposed (hμA : ∀ v ∈ C, μ v ∈ A) (hμinj : Set.InjOn μ C)
    (hexp : ∀ b ∈ A, b ∉ C.image μ → ∀ v ∈ C, ∀ w ∈ C, G.Adj v b → G.Adj w b → v = w) :
    unmatchedExcess G A C μ ≤ A.card - C.card := by
  have himg : C.image μ ⊆ A := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    exact hμA v hv
  rw [← card_image_of_injOn hμinj, ← card_sdiff_of_subset himg]
  unfold unmatchedExcess
  apply card_le_card_of_injOn Prod.snd
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_excessEdges] at hp
    rw [mem_coe, mem_sdiff]
    exact ⟨hp.1.2.1, hp.2⟩
  · intro p hp q hq hpq
    simp only [coe_filter, Set.mem_setOf_eq, mem_excessEdges] at hp hq
    have h1 : p.1 = q.1 := hexp p.2 hp.1.2.1 hp.2 p.1 hp.1.1 q.1 hq.1.1 hp.1.2.2.1
      (hpq ▸ hq.1.2.2.1)
    exact Prod.ext h1 hpq

/-- `U ≤ a - c` when every unmatched vertex of `A` has degree at most 1 (the form of Lemma 2.2 of
the source, as in `Fiber.exists_saturating_matching_exposedLeaves`). -/
theorem unmatchedExcess_le_of_degree_le_one [Fintype V] (hμA : ∀ v ∈ C, μ v ∈ A)
    (hμinj : Set.InjOn μ C) (hdeg : ∀ b ∈ A \ C.image μ, G.degree b ≤ 1) :
    unmatchedExcess G A C μ ≤ A.card - C.card := by
  apply unmatchedExcess_le_of_exposed hμA hμinj
  intro b hbA hbC v _ w _ hvb hwb
  have hd := hdeg b (mem_sdiff.mpr ⟨hbA, hbC⟩)
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
  have hv : v ∈ G.neighborFinset b := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hvb.symm
  have hw : w ∈ G.neighborFinset b := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hwb.symm
  exact card_le_one.mp hd v hv w hw

/-- **Theorem 3.1 with the exposed-leaf hypothesis in degree form**: if `μ` matches `C` into `A`
(`μ v ∈ A`, `v ~ μ v`, `μ` injective on `C`) and every vertex of `A \ μ(C)` has degree at most 1,
then `S^M_h ≥ 0` for `2 ≤ h ≤ c`.  (With `C = Aᶜ` the hypotheses are exactly the output of
`Fiber.exists_saturating_matching_exposedLeaves` for a maximum independent `A` of a
forest.) -/
theorem matchingExcess_nonneg_of_exposedLeaves [Fintype V]
    (hμ : ∀ v ∈ C, μ v ∈ A ∧ G.Adj v (μ v)) (hμinj : Set.InjOn μ C)
    (hdeg : ∀ b ∈ A \ C.image μ, G.degree b ≤ 1) {h : ℕ} (h2 : 2 ≤ h) (hhc : h ≤ C.card) :
    0 ≤ matchingExcess G A C h :=
  matchingExcess_nonneg (fun v hv => (hμ v hv).1) (fun v hv => (hμ v hv).2) hμinj
    (unmatchedExcess_le_of_degree_le_one (fun v hv => (hμ v hv).1) hμinj hdeg) h2 hhc

end Exposed

end Fiber
end Erdos993Lean
