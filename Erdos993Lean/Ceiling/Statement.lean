module

public import Mathlib
public import Erdos993Lean.Statement
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Hoggar

/-!
# The ceiling: every forest with at least 8,400,000 vertices is unimodal (R221), conditionally

**Honest grade.** R221 is a computer-assisted theorem of this project,
not externally reviewed.  Its proof has a combinatorial boundary layer
(prefix, tail, join, assembly) and an analytic core (curvature near the hard-core means via a
quantitative local limit theorem, with exact-rational certificates).  Formalized here: the
prefix, the tail and the assembly.  **Not** formalized: the analytic core, and the combinatorial
join lemmas (B2, B5 with its 428-case exact check, B7, B8) that turn the analytic core into the
window statement; both sit inside the `window` hypothesis.

This file:
* states the ceiling claim `CeilingStatement N0` and the glue `floor + ceiling → #993`;
* packages R221's two remaining inputs as the named hypothesis `R221Inputs`:
  - `window`: curvature on `[⌈n/4⌉, h_B]` for `n ≥ 8,400,000` (R221 (ii), with the positivity of
    the three entries that R221A states); its proof combines the analytic curvature
    R221A (certificate-backed) with the combinatorial join lemmas B2, B5, B7, B8 (paper proofs);
    **none of this is formalized**;
  - `tail`: the matching-block deletion inequality `i_s b_{s-1} ≤ i_{s-1} b_s` for every forest
    (ceiling proof, Appendix R4 / B6); this input is **proved in Lean** in `Erdos993Lean.Ceiling.Tail`
    (`tail_inequality`), so `ceiling_of_R221Window` there needs only the window;
* proves `ceiling_of_R221Inputs : R221Inputs → CeilingStatement 8400000`, using the rising prefix
  L394 (`Erdos993Lean.Ceiling.Prefix`, proved in Lean) and an elementary assembly lemma.

Scope fence: R221 asserts curvature only on `[⌈n/4⌉, h_B]` plus a nonincreasing tail,
not log-concavity on the whole support.
-/

@[expose] public section

namespace Erdos993Lean

open Finset

/-! ## Floor, ceiling, and the glue -/

/-- The ceiling claim at threshold `N0`: every forest with at least `N0` vertices has a unimodal
independence sequence. -/
def CeilingStatement (N0 : ℕ) : Prop :=
  ∀ F : FiniteForest, N0 ≤ F.n → independenceSequenceUnimodal F

/-- The floor claim below `N0`: every forest with fewer than `N0` vertices has a unimodal
independence sequence. -/
def FloorStatement (N0 : ℕ) : Prop :=
  ∀ F : FiniteForest, F.n < N0 → independenceSequenceUnimodal F

/-- A floor and a ceiling at the same threshold give Erdős #993. -/
theorem erdos993_of_floor_of_ceiling {N0 : ℕ} (hF : FloorStatement N0)
    (hC : CeilingStatement N0) : Erdos993Statement := by
  intro F
  rcases lt_or_ge F.n N0 with h | h
  · exact hF F h
  · exact hC F h

/-! ## The objects in R221 -/

/-- The matching number `ν(G)`: the largest number of pairwise disjoint edges. -/
noncomputable def matchingNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ M : Set (Sym2 V), M ⊆ G.edgeSet ∧ M.ncard = k ∧ M.Finite ∧
    M.Pairwise (fun e f => ∀ v, v ∈ e → v ∉ f)}

/-- Coefficients of `B_F(x) = (1 + 2x)^ν (1 + x)^(n - 2ν)`. -/
noncomputable def bRow (n ν : ℕ) (s : ℕ) : ℕ :=
  (((1 + 2 * Polynomial.X : Polynomial ℕ) ^ ν * (1 + Polynomial.X) ^ (n - 2 * ν))).coeff s

/-- The first mode of a finitely supported sequence (the least index of a maximal entry);
`0` for the zero sequence. -/
noncomputable def firstMode (b : ℕ → ℕ) : ℕ := by
  classical
  exact if h : ∃ m, ∀ j, b j ≤ b m then Nat.find h else 0

/-- `h_B` of a forest: the first mode of `B_F`. -/
noncomputable def hB (F : FiniteForest) : ℕ :=
  firstMode (bRow F.n (matchingNumber F.graph))

/-- The two inputs of R221 that are not proved in Lean. -/
structure R221Inputs : Prop where
  /-- R221 (ii): window curvature for `n ≥ 8,400,000`, with the positivity stated by R221A
  (analytic curvature plus the combinatorial join; outside Lean). -/
  window : ∀ F : FiniteForest, 8400000 ≤ F.n → ∀ k, (F.n + 3) / 4 ≤ k → k ≤ hB F →
    0 < independenceCount F (k - 1) ∧ 0 < independenceCount F k ∧
      0 < independenceCount F (k + 1) ∧
      independenceCount F (k - 1) * independenceCount F (k + 1) <
        independenceCount F k * independenceCount F k
  /-- R221 (iii)/B6: the matching-block deletion inequality (proved in Lean as
  `Erdos993Lean.tail_inequality`, file `Ceiling/Tail.lean`). -/
  tail : ∀ F : FiniteForest, ∀ s, 1 ≤ s →
    independenceCount F s * bRow F.n (matchingNumber F.graph) (s - 1) ≤
      independenceCount F (s - 1) * bRow F.n (matchingNumber F.graph) s

/-! ## Auxiliary material for the ceiling

Proved here, in the namespace `Erdos993Lean.Ceiling`:
* the row `B_F` is log-concave (Hoggar's theorem applied to the factors `1 + 2x` and `1 + x`) and
  positive exactly on `[0, ν + (n - 2ν)]`, hence unimodal and nonincreasing from its first mode
  `h_B` (`bRow_good`, `firstMode_antitone`);
* the easy half of König's theorem: every independent set of a graph on `n` vertices has at most
  `n - ν` vertices (`card_add_matchingNumber_le`), so the independence counts vanish where `B_F`
  does. -/

namespace Ceiling

/-- `b` is positive on `[0, D]` and vanishes beyond `D`. -/
def PosUpTo (b : ℕ → ℕ) (D : ℕ) : Prop :=
  (∀ k, k ≤ D → 0 < b k) ∧ (∀ k, D < k → b k = 0)

theorem PosUpTo.noInternalZeros {b : ℕ → ℕ} {D : ℕ} (h : PosUpTo b D) : NoInternalZeros b := by
  intro i j k _ hjk _ hk
  have hkD : k ≤ D := by
    by_contra hcon
    exact hk (h.2 k (by omega))
  exact (h.1 j (by omega)).ne'

theorem PosUpTo.finitelySupported {b : ℕ → ℕ} {D : ℕ} (h : PosUpTo b D) :
    FinitelySupported b :=
  ⟨D + 1, fun k hk => h.2 k (by omega)⟩

theorem PosUpTo.cauchyProduct {a b : ℕ → ℕ} {D E : ℕ} (ha : PosUpTo a D) (hb : PosUpTo b E) :
    PosUpTo (cauchyProduct a b) (D + E) := by
  constructor
  · intro k hk
    unfold Erdos993Lean.cauchyProduct
    have hi : min k D ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    calc 0 < a (min k D) * b (k - min k D) :=
          Nat.mul_pos (ha.1 _ (by omega)) (hb.1 _ (by omega))
      _ ≤ ∑ i ∈ Finset.range (k + 1), a i * b (k - i) :=
          Finset.single_le_sum (f := fun i => a i * b (k - i)) (fun i _ => Nat.zero_le _) hi
  · intro k hk
    unfold Erdos993Lean.cauchyProduct
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hiD : D < i
    · rw [ha.2 i hiD, zero_mul]
    · rw [hb.2 (k - i) (by omega), mul_zero]

theorem coeff_mul_eq_cauchyProduct (p q : Polynomial ℕ) :
    (fun k => (p * q).coeff k) = cauchyProduct (fun k => p.coeff k) (fun k => q.coeff k) := by
  funext k
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

/-- A polynomial over `ℕ` whose coefficient sequence is log-concave and positive exactly on
`[0, D]`. -/
def GoodPoly (p : Polynomial ℕ) (D : ℕ) : Prop :=
  LogConcave (fun k => p.coeff k) ∧ PosUpTo (fun k => p.coeff k) D

theorem GoodPoly.mul {p q : Polynomial ℕ} {D E : ℕ} (hp : GoodPoly p D) (hq : GoodPoly q E) :
    GoodPoly (p * q) (D + E) := by
  unfold GoodPoly
  rw [coeff_mul_eq_cauchyProduct]
  exact ⟨logConcave_cauchyProduct hp.1 hq.1 hp.2.noInternalZeros hq.2.noInternalZeros
    hp.2.finitelySupported hq.2.finitelySupported, hp.2.cauchyProduct hq.2⟩

theorem goodPoly_one : GoodPoly 1 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp [Polynomial.coeff_one]
  · intro k hk
    have : k = 0 := by omega
    subst this
    simp
  · intro k hk
    simp only [Polynomial.coeff_one]
    rw [if_neg (by omega)]

theorem GoodPoly.pow {p : Polynomial ℕ} {D : ℕ} (hp : GoodPoly p D) (m : ℕ) :
    GoodPoly (p ^ m) (m * D) := by
  induction m with
  | zero => rw [pow_zero, zero_mul]; exact goodPoly_one
  | succ m ih => rw [pow_succ, Nat.succ_mul]; exact ih.mul hp

theorem goodPoly_linear (c : ℕ) (hc : 0 < c) :
    GoodPoly (1 + Polynomial.C c * Polynomial.X) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp [Polynomial.coeff_one, Polynomial.coeff_X]
  · intro k hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · simp
    · simp [Polynomial.coeff_one, hc]
  · intro k hk
    simp [Polynomial.coeff_one, Polynomial.coeff_X]
    omega

/-- The row `B_F` is log-concave and positive exactly on `[0, ν + (n - 2ν)]`. -/
theorem bRow_good (n ν : ℕ) :
    LogConcave (bRow n ν) ∧ PosUpTo (bRow n ν) (ν + (n - 2 * ν)) := by
  have h1 : GoodPoly ((1 + 2 * Polynomial.X : Polynomial ℕ) ^ ν) (ν * 1) := by
    have h := goodPoly_linear 2 (by norm_num)
    rw [show (Polynomial.C 2 : Polynomial ℕ) = 2 from rfl] at h
    exact h.pow ν
  have h2 : GoodPoly ((1 + Polynomial.X : Polynomial ℕ) ^ (n - 2 * ν)) ((n - 2 * ν) * 1) := by
    have h := goodPoly_linear 1 (by norm_num)
    rw [Polynomial.C_1, one_mul] at h
    exact h.pow (n - 2 * ν)
  have h := h1.mul h2
  rw [mul_one, mul_one] at h
  exact h

/-- A unimodal sequence is nonincreasing from its first mode on. -/
theorem firstMode_antitone {b : ℕ → ℕ} (hb : Unimodal b) :
    ∀ k, firstMode b ≤ k → b (k + 1) ≤ b k := by
  classical
  obtain ⟨p, hup, hdown⟩ := hb
  have hmax : ∀ j, b j ≤ b p := by
    intro j
    rcases le_total j p with hjp | hpj
    · exact hup j p hjp le_rfl
    · exact hdown p j le_rfl hpj
  have hex : ∃ m, ∀ j, b j ≤ b m := ⟨p, hmax⟩
  have hfm : (∀ j, b j ≤ b (firstMode b)) ∧ firstMode b ≤ p := by
    unfold firstMode
    rw [dif_pos hex]
    exact ⟨Nat.find_spec hex, Nat.find_min' hex hmax⟩
  intro k hk
  by_cases hpk : p ≤ k
  · exact hdown k (k + 1) hpk (Nat.le_succ k)
  · calc b (k + 1) ≤ b (firstMode b) := hfm.1 (k + 1)
      _ ≤ b k := hup _ k hk (by omega)

/-- The easy half of König: a matching `M` and an independent set `t` in a graph on `n`
vertices satisfy `|M| + |t| ≤ n` (each edge of `M` has an end outside `t`, and these ends are
distinct). -/
theorem matching_ncard_add_card_le {n : ℕ} (G : SimpleGraph (Fin n)) (t : Finset (Fin n))
    (ht : G.IsIndepSet (t : Set (Fin n))) (M : Set (Sym2 (Fin n))) (hM : M ⊆ G.edgeSet)
    (hMfin : M.Finite) (hMdisj : M.Pairwise (fun e f => ∀ v, v ∈ e → v ∉ f)) :
    M.ncard + t.card ≤ n := by
  classical
  have hout : ∀ e ∈ M, ∃ v, v ∈ e ∧ v ∉ t := by
    intro e he
    have hadj := hM he
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeSet] at hadj
      by_cases hx : x ∈ t
      · refine ⟨y, Sym2.mem_mk_right x y, fun hy => ?_⟩
        exact ht (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hadj.ne hadj
      · exact ⟨x, Sym2.mem_mk_left x y, hx⟩
  let f : Sym2 (Fin n) → Fin n := fun e =>
    if h : ∃ v, v ∈ e ∧ v ∉ t then Classical.choose h else (Quot.out e).1
  have hf : ∀ e ∈ M, f e ∈ e ∧ f e ∉ t := by
    intro e he
    have h := hout e he
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  have hcard : hMfin.toFinset.card ≤ tᶜ.card := by
    apply Finset.card_le_card_of_injOn f
    · intro e he
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he
      rw [Finset.mem_coe, Finset.mem_compl]
      exact (hf e he).2
    · intro e he e' he' hee'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he he'
      by_contra hne
      have h := hMdisj he he' hne (f e) (hf e he).1
      rw [hee'] at h
      exact h (hf e' he').1
  rw [Set.ncard_eq_toFinset_card M hMfin]
  have := Finset.card_add_card_compl t
  rw [Fintype.card_fin] at this
  omega

/-- The matching number is attained. -/
theorem matchingNumber_mem {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ M : Set (Sym2 (Fin n)), M ⊆ G.edgeSet ∧ M.ncard = matchingNumber G ∧ M.Finite ∧
      M.Pairwise (fun e f => ∀ v, v ∈ e → v ∉ f) := by
  have h : matchingNumber G ∈ {k | ∃ M : Set (Sym2 (Fin n)), M ⊆ G.edgeSet ∧ M.ncard = k ∧
      M.Finite ∧ M.Pairwise (fun e f => ∀ v, v ∈ e → v ∉ f)} := by
    unfold matchingNumber
    apply Nat.sSup_mem
    · exact ⟨0, ∅, Set.empty_subset _, Set.ncard_empty _, Set.finite_empty, Set.pairwise_empty _⟩
    · refine ⟨n, ?_⟩
      rintro k ⟨M, hM, rfl, hMfin, hMdisj⟩
      have h := matching_ncard_add_card_le G ∅ (by simp) M hM hMfin hMdisj
      simpa using h
  exact h

/-- Every independent set of a graph on `n` vertices has at most `n - ν` vertices. -/
theorem card_add_matchingNumber_le {n : ℕ} (G : SimpleGraph (Fin n)) (t : Finset (Fin n))
    (ht : G.IsIndepSet (t : Set (Fin n))) : matchingNumber G + t.card ≤ n := by
  obtain ⟨M, hM, hMcard, hMfin, hMdisj⟩ := matchingNumber_mem G
  rw [← hMcard]
  exact matching_ncard_add_card_le G t ht M hM hMfin hMdisj

end Ceiling

/-- The assembly lemma (ceiling proof, §10, "ASM"): a sequence that is nondecreasing up to `L`,
log-concave with positive entries across `[L, H]`, and nonincreasing from `H` on is unimodal. -/
theorem unimodal_of_prefix_window_tail {a : ℕ → ℕ} {L H : ℕ}
    (hpre : ∀ k, k < L → a k ≤ a (k + 1))
    (hwin : ∀ k, L ≤ k → k ≤ H → 0 < a (k - 1) ∧ 0 < a k ∧ 0 < a (k + 1) ∧
      a (k - 1) * a (k + 1) ≤ a k * a k)
    (htail : ∀ k, H ≤ k → a (k + 1) ≤ a k) : Unimodal a := by
  classical
  -- `m` is the first descent at or after `L`; it exists (at `max L H` at the latest).
  have hex : ∃ k, L ≤ k ∧ a (k + 1) ≤ a k :=
    ⟨max L H, le_max_left _ _, htail _ (le_max_right _ _)⟩
  obtain ⟨hLm, hm⟩ := Nat.find_spec hex
  have hbefore : ∀ k, k < Nat.find hex → a k ≤ a (k + 1) := by
    intro k hk
    by_cases hkL : k < L
    · exact hpre k hkL
    · have h := Nat.find_min hex hk
      push_neg at h
      exact (h (by omega)).le
  have hafter : ∀ k, Nat.find hex ≤ k → a (k + 1) ≤ a k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hm
    | succ k hmk ih =>
      by_cases hHk : H ≤ k + 1
      · exact htail _ hHk
      · obtain ⟨h0, -, -, hlc⟩ := hwin (k + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at h0 hlc
        have h2 : a (k + 1) * a (k + 1) ≤ a k * a (k + 1) := Nat.mul_le_mul_right _ ih
        exact Nat.le_of_mul_le_mul_left (le_trans hlc h2) h0
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro i j hij hjm
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans (ih (by omega)) (hbefore j (by omega))
  · intro i j hmi hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans (hafter j (by omega)) ih

/-- **R221, conditional form**: the named inputs imply the ceiling at 8,400,000. -/
theorem ceiling_of_R221Inputs (h : R221Inputs) : CeilingStatement 8400000 := by
  classical
  intro F hF
  have hcount : independenceCount F = fun k => (F.graph.indepSetFinset k).card := by
    funext k
    unfold independenceCount
    rfl
  -- counts vanish above `n - ν`
  have hzero : ∀ j, F.n - matchingNumber F.graph < j → independenceCount F j = 0 := by
    intro j hj
    rw [hcount]
    show (F.graph.indepSetFinset j).card = 0
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    rw [SimpleGraph.mem_indepSetFinset_iff] at ht
    have h1 := Ceiling.card_add_matchingNumber_le F.graph t ht.isIndepSet
    rw [ht.card_eq] at h1
    omega
  -- the row `B_F`
  obtain ⟨hbLC, hbPos⟩ := Ceiling.bRow_good F.n (matchingNumber F.graph)
  have hbU : Unimodal (bRow F.n (matchingNumber F.graph)) :=
    unimodal_of_logConcave hbLC hbPos.noInternalZeros hbPos.finitelySupported
  have hbanti := Ceiling.firstMode_antitone hbU
  have hU : Unimodal (independenceCount F) := by
    apply unimodal_of_prefix_window_tail (L := (F.n + 3) / 4) (H := hB F)
    · -- the rising prefix
      intro k hk
      have h4 : 4 * k + 1 ≤ (Finset.univ : Finset (Fin F.n)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      have h5 := indepCount_le_succ_of_prefix F.isForest Finset.univ h4
      rw [indepCount_univ, indepCount_univ] at h5
      rw [hcount]
      exact h5
    · -- the window (R221 (ii))
      intro k hLk hkH
      obtain ⟨h1, h2, h3, h4⟩ := h.window F hF k hLk hkH
      exact ⟨h1, h2, h3, h4.le⟩
    · -- the tail (R221 (iii)) against the nonincreasing tail of `B_F`
      intro k hk
      have ht := h.tail F (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at ht
      have hbk : bRow F.n (matchingNumber F.graph) (k + 1) ≤ bRow F.n (matchingNumber F.graph) k :=
        hbanti k hk
      rcases Nat.eq_zero_or_pos (bRow F.n (matchingNumber F.graph) k) with h0 | hpos
      · have hkD : matchingNumber F.graph + (F.n - 2 * matchingNumber F.graph) < k := by
          by_contra hcon
          push_neg at hcon
          exact (hbPos.1 k hcon).ne' h0
        rw [hzero (k + 1) (by omega)]
        exact Nat.zero_le _
      · exact Nat.le_of_mul_le_mul_right (le_trans ht (Nat.mul_le_mul_left _ hbk)) hpos
  unfold independenceSequenceUnimodal
  exact unimodalUpTo_of_unimodal hU

end Erdos993Lean
