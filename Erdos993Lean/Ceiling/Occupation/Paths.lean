module

public import Mathlib
public import Erdos993Lean.Ceiling.Occupation.Surplus
public import Erdos993Lean.Ceiling.Occupation.Arith

/-!
# B5, part 6: odd pendant paths at a matching-essential vertex

The ceiling proof, Appendix R3 (the case `t = 1, k = 1, m = 0`).
A pendant path `q₁ - … - q_L - x` (`IsTail G s x [q₁, …, q_L]`) with residual `J = tailRest s qs`,
the vertex `x` matching-essential in `J` (`ν(J) = ν(J - x) + 1`), `J' = J - x`, `M = J - N[x]`,
`k = deg_J(x)`, `d_w = deg_{J'}(w)` for the neighbours `w` of `x`, `D = ∑ d_w`:

* `IsTail.decomp`: `Z(s) = Z(P_L) Z(J') + λ Z(P_{L-1}) Z(M)` and the companion formula for `S`
  (the exact partition at the bit of `x`; path values `tA`, `tB`, `tC`, `tE`, e.g.
  `Z(P_3) = 121/9`, `λ Z(P_2) = 119/9`, `Z(P_5) = 1567/27`, `λ Z(P_4) = 560/9`);
* `IsTail.nuIn_eq`: `ν(s) = ν(J) + (L - 1)/2` ("the two matching options agree");
  `IsTail.card_eq`, `IsTail.ccIn_eq`;
* `removal_chain`, `essential_facts`: `cc(J') + 1 = cc(J) + k`, `cc(M) + k = cc(J') + D`,
  `ν(M) ≤ ν(J')`, and the ratio bounds `∏ f(d_w) · Z(M) ≤ Z(J') ≤ (10/3)^k Z(M)` (the paper's
  `P ≤ Q ≤ (10/3)^k`, by deleting the neighbours of `x` one at a time; a forest has no triangles);
* `surplus_tail5`, `surplus_tail3`: `189 Φ(s)` (resp. `378 Φ(s)`) equals a nonnegative
  combination of `Φ(J')`, `Φ(M)`, `(ν(J) - 1 - ν(M)) Z(M)`, plus `N₅(Q) Z(M)` (resp. `N₃(Q) Z(M)`),
  where `N₅`, `N₃` are exactly the numerators (R5), (R4) of the paper.  For `k ≥ 2` the lower
  ratio bound and `N5_nonneg` (`N3_nonneg`) pay; for `k = 1` the upper ratio bound pays `D ≥ 1`
  (resp. `D ≥ 2`); `k = 1, D = 0` is a whole `P₇` (resp. `P₅`) component, paid by the isolate
  surplus of the last vertex; and `L = 3, k = 1, D = 1` is the length-five path of the same forest
  at the next vertex (`IsTail.append`), paid by `surplus_tail5`.
-/

@[expose] public section

namespace Erdos993Lean
namespace Occupation

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Pendant paths -/

variable (G) in
/-- `IsTail G s x [q₁, …, q_L]`: a pendant path of `G[s]` hanging at `x`.  The vertex `q₁ ∈ s` has
the single neighbour `q₂` in `s`; in `s - q₁` the vertex `q₂` has the single neighbour `q₃`; …;
`q_L` has the single neighbour `x`; and `x` is not deleted. -/
def IsTail : Finset V → V → List V → Prop
  | s, x, [] => x ∈ s
  | s, x, q :: qs => q ∈ s ∧ nbrsIn G s q = {qs.headD x} ∧ IsTail (s.erase q) x qs

/-- The residual of a tail: `s` with the path vertices deleted one by one. -/
def tailRest (s : Finset V) (qs : List V) : Finset V := qs.foldl (fun t q => t.erase q) s

@[simp] theorem tailRest_nil (s : Finset V) : tailRest s [] = s := rfl

@[simp] theorem tailRest_cons (s : Finset V) (q : V) (qs : List V) :
    tailRest s (q :: qs) = tailRest (s.erase q) qs := rfl

theorem tailRest_subset (s : Finset V) (qs : List V) : tailRest s qs ⊆ s := by
  induction qs generalizing s with
  | nil => exact Finset.Subset.refl s
  | cons q qs ih => exact (ih (s.erase q)).trans (Finset.erase_subset q s)

theorem IsTail.mem {s : Finset V} {x : V} {qs : List V} (h : IsTail G s x qs) :
    x ∈ tailRest s qs := by
  induction qs generalizing s with
  | nil => exact h
  | cons q qs ih => exact ih h.2.2

theorem IsTail.card_eq {s : Finset V} {x : V} {qs : List V} (h : IsTail G s x qs) :
    s.card = (tailRest s qs).card + qs.length := by
  induction qs generalizing s with
  | nil => simp
  | cons q qs ih =>
    rw [tailRest_cons, List.length_cons, ← add_assoc, ← ih h.2.2, Finset.card_erase_add_one h.1]

theorem IsTail.ccIn_eq (hG : G.IsAcyclic) {s : Finset V} {x : V} {qs : List V}
    (h : IsTail G s x qs) : ccIn G s = ccIn G (tailRest s qs) := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
    rw [tailRest_cons, ← ih h.2.2]
    have h1 := ccIn_erase hG h.1
    rw [h.2.1, Finset.card_singleton] at h1
    omega

/-- Peeling an odd pendant path at a matching-essential vertex: `ν(s) = ν(J) + (L - 1)/2`. -/
theorem IsTail.nuIn_eq : ∀ (r : ℕ) {s : Finset V} {x : V} {qs : List V}, IsTail G s x qs →
    qs.length = 2 * r + 1 →
    nuIn G (tailRest s qs) = nuIn G ((tailRest s qs).erase x) + 1 →
    nuIn G s = nuIn G (tailRest s qs) + r := by
  intro r
  induction r with
  | zero =>
    intro s x qs h hlen hess
    match qs, h, hlen with
    | [q], h, _ =>
      rw [tailRest_cons, tailRest_nil] at hess ⊢
      rw [nuIn_pendant h.1 h.2.1, hess]
      rfl
  | succ r ih =>
    intro s x qs h hlen hess
    match qs, h, hlen with
    | q₁ :: q₂ :: rest, h, hlen =>
      have h2 : IsTail G (s.erase q₁) x (q₂ :: rest) := h.2.2
      have h3 : IsTail G ((s.erase q₁).erase q₂) x rest := h2.2.2
      rw [tailRest_cons, tailRest_cons] at hess ⊢
      rw [nuIn_pendant h.1 h.2.1, List.headD_cons, ih h3 (by simp at hlen; omega) hess]
      ring

/-! Path coefficients: with `J` the residual, `J' = J - x`, `M = J - N[x]`,
`Z(s) = tA L · Z(J') + (7/3) tB L · Z(M)` and
`S(s) = tA L · S(J') + tC L · Z(J') + (7/3) tB L · S(M) + tE L · Z(M)`. -/

/-- `tA L = Z(P_L)` at `7/3`. -/
def tA : ℕ → ℚ
  | 0 => 1
  | 1 => 10 / 3
  | n + 2 => tA (n + 1) + 7 / 3 * tA n

/-- `tB L = Z(P_{L-1})` at `7/3` (`tB 0 = 1`). -/
def tB : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | n + 2 => tB (n + 1) + 7 / 3 * tB n

/-- `tC L = S(P_L)` at `7/3`. -/
def tC : ℕ → ℚ
  | 0 => 0
  | 1 => 7 / 3
  | n + 2 => tC (n + 1) + 7 / 3 * (tA n + tC n)

/-- `tE L = (7/3)(Z(P_{L-1}) + S(P_{L-1}))` at `7/3` (`tE 0 = 7/3`). -/
def tE : ℕ → ℚ
  | 0 => 7 / 3
  | 1 => 7 / 3
  | n + 2 => tE (n + 1) + 7 / 3 * (7 / 3 * tB n + tE n)

example : tA 3 = 121 / 9 ∧ tB 3 = 17 / 3 ∧ tC 3 = 161 / 9 ∧ tE 3 = 217 / 9 := by
  norm_num [tA, tB, tC, tE]

example : tA 5 = 1567 / 27 ∧ tB 5 = 80 / 3 ∧ tC 5 = 1036 / 9 ∧ tE 5 = 1442 / 9 := by
  norm_num [tA, tB, tC, tE]

/-- **Path decomposition.**  For a pendant path of length `L` hanging at `x`, with residual `J`,
`Z(s) = tA L · Z(J - x) + (7/3) tB L · Z(J - N[x])` and
`S(s) = tA L · S(J - x) + tC L · Z(J - x) + (7/3) tB L · S(J - N[x]) + tE L · Z(J - N[x])`. -/
theorem IsTail.decomp : ∀ (n : ℕ) {s : Finset V} {x : V} {qs : List V}, IsTail G s x qs →
    qs.length = n →
    Zq G s = tA n * Zq G ((tailRest s qs).erase x) +
        7 / 3 * tB n * Zq G (outsideClosedNbhd G (tailRest s qs) x) ∧
    Sq G s = tA n * Sq G ((tailRest s qs).erase x) + tC n * Zq G ((tailRest s qs).erase x) +
        7 / 3 * tB n * Sq G (outsideClosedNbhd G (tailRest s qs) x) +
        tE n * Zq G (outsideClosedNbhd G (tailRest s qs) x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s x qs h hlen
    match qs, h, hlen with
    | [], h, hlen =>
      subst hlen
      simp only [tailRest_nil, List.length_nil, tA, tB, tC, tE]
      have h1 := Zq_erase G (h : x ∈ s)
      have h2 := Sq_erase G (h : x ∈ s)
      constructor
      · rw [h1]; ring
      · rw [h2]; ring
    | [q], h, hlen =>
      subst hlen
      obtain ⟨hq, hqn, hx⟩ := h
      simp only [List.headD_nil] at hqn
      simp only [tailRest_cons, tailRest_nil, List.length_cons, List.length_nil, tA, tB, tC, tE]
      have h1 := Zq_pendant G hq hqn
      have h2 := Sq_pendant G hq hqn
      have h3 := Zq_erase G (hx : x ∈ s.erase q)
      have h4 := Sq_erase G (hx : x ∈ s.erase q)
      constructor
      · rw [h1, h3]; ring
      · rw [h2, h4]; ring
    | q₁ :: q₂ :: rest, h, hlen =>
      obtain ⟨hq₁, hq₁n, h2⟩ := h
      simp only [List.headD_cons] at hq₁n
      have h3 : IsTail G ((s.erase q₁).erase q₂) x rest := h2.2.2
      have hl : n = rest.length + 2 := by rw [← hlen]; simp
      obtain ⟨ha1, ha2⟩ := ih (rest.length + 1) (by omega) h2 (by simp)
      obtain ⟨hb1, hb2⟩ := ih rest.length (by omega) h3 rfl
      simp only [tailRest_cons] at ha1 ha2 ⊢
      have e1 := Zq_pendant G hq₁ hq₁n
      have e2 := Sq_pendant G hq₁ hq₁n
      rw [hl]
      simp only [tA, tB, tC, tE]
      constructor
      · rw [e1, ha1, hb1]; ring
      · rw [e2, ha2, hb2, hb1]; ring

/-- Extending a pendant path through its attachment vertex `x` and the next vertex `w`. -/
theorem IsTail.append {x w y : V} : ∀ {s : Finset V} {qs : List V}, IsTail G s x qs →
    nbrsIn G (tailRest s qs) x = {w} → nbrsIn G ((tailRest s qs).erase x) w = {y} →
    y ∈ ((tailRest s qs).erase x).erase w →
    IsTail G s y (qs ++ [x, w]) ∧ tailRest s (qs ++ [x, w]) = ((tailRest s qs).erase x).erase w
  | s, [], h, hx, hw, hy => by
    simp only [tailRest_nil] at hx hw hy ⊢
    have hws : w ∈ s.erase x := nbrsIn_subset_erase G s x (by rw [hx]; exact mem_singleton_self w)
    refine ⟨⟨h, ?_, hws, hw, hy⟩, rfl⟩
    simpa using hx
  | s, q :: qs, h, hx, hw, hy => by
    simp only [tailRest_cons] at hx hw hy ⊢
    obtain ⟨h1, h2⟩ := IsTail.append h.2.2 hx hw hy
    refine ⟨⟨h.1, ?_, h1⟩, h2⟩
    rw [h.2.1]
    cases qs with
    | nil => rfl
    | cons q' qs => rfl

omit [DecidableRel G.Adj] in
/-- A forest has no triangles. -/
theorem not_triangle (hG : G.IsAcyclic) {x w y : V} (hxw : G.Adj x w) (hxy : G.Adj x y)
    (hwy : G.Adj w y) : False := by
  have hw : w ∈ ({x, w, y} : Finset V).erase x :=
    Finset.mem_erase.mpr ⟨(G.ne_of_adj hxw).symm, by simp⟩
  have hy : y ∈ ({x, w, y} : Finset V).erase x :=
    Finset.mem_erase.mpr ⟨(G.ne_of_adj hxy).symm, by simp⟩
  have hyc : y ∈ compIn G (({x, w, y} : Finset V).erase x) w :=
    mem_compIn_of_adjIn (self_mem_compIn hw) ⟨hw, hy, hwy⟩
  have := eq_of_mem_branch_of_adj hG hxw hyc hxy
  subst this
  exact G.irrefl hwy

/-- **Deleting the neighbours of `x` one at a time.**  With `J' = J - x` and `d_w` the degree of a
neighbour `w` of `x` in `J'`: for every set `N'` of neighbours of `x`,
`cc(J' - N') + |N'| = cc(J') + ∑_{N'} d_w` and `∏_{N'} f(d_w) · Z(J' - N') ≤ Z(J')`. -/
theorem removal_chain (hG : G.IsAcyclic) {J : Finset V} {x : V} :
    ∀ N' ⊆ nbrsIn G J x,
      ccIn G ((J.erase x) \ N') + N'.card =
          ccIn G (J.erase x) + ∑ w ∈ N', (nbrsIn G (J.erase x) w).card ∧
        (∏ w ∈ N', fac (nbrsIn G (J.erase x) w).card) * Zq G ((J.erase x) \ N') ≤
          Zq G (J.erase x) := by
  intro N' hN'
  induction N' using Finset.induction_on with
  | empty => simp
  | insert w N'' hw ih =>
    have hN'' : N'' ⊆ nbrsIn G J x := (Finset.subset_insert w N'').trans hN'
    obtain ⟨ih1, ih2⟩ := ih hN''
    have hwN : w ∈ nbrsIn G J x := hN' (Finset.mem_insert_self w N'')
    set A := (J.erase x) \ N'' with hA
    have hwJ' : w ∈ J.erase x := nbrsIn_subset_erase G J x hwN
    have hwA : w ∈ A := Finset.mem_sdiff.mpr ⟨hwJ', hw⟩
    have hsd : (J.erase x) \ insert w N'' = A.erase w := by
      ext y
      simp only [hA, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      tauto
    -- the neighbours of `w` inside `A` are its neighbours inside `J - x`
    have hnb : nbrsIn G A w = nbrsIn G (J.erase x) w := by
      ext y
      rw [mem_nbrsIn, mem_nbrsIn]
      constructor
      · rintro ⟨hyA, hwy⟩
        exact ⟨(Finset.mem_sdiff.mp hyA).1, hwy⟩
      · rintro ⟨hyJ, hwy⟩
        refine ⟨Finset.mem_sdiff.mpr ⟨hyJ, fun hyN => ?_⟩, hwy⟩
        exact not_triangle hG (mem_nbrsIn.mp hwN).2 (mem_nbrsIn.mp (hN'' hyN)).2 hwy
    constructor
    · have h1 := ccIn_erase hG hwA
      rw [hnb, ← hsd] at h1
      rw [Finset.card_insert_of_notMem hw, Finset.sum_insert hw]
      omega
    · rw [Finset.prod_insert hw, hsd]
      -- `Z(A) ≥ f(d_w) Z(A - w)`
      have hZA := Zq_erase G hwA
      rw [outsideClosedNbhd_eq, hnb] at hZA
      have hsub : nbrsIn G (J.erase x) w ⊆ A.erase w := by
        rw [← hnb]; exact nbrsIn_subset_erase G A w
      have hle := Zq_le_sdiff G hsub
      set dw := (nbrsIn G (J.erase x) w).card
      have hkey : fac dw * Zq G (A.erase w) ≤ Zq G A := by
        rw [hZA]
        unfold fac
        have hpow : (3 / 10 : ℚ) ^ dw * (10 / 3) ^ dw = 1 := by
          rw [← mul_pow]; norm_num
        have h0 : (0 : ℚ) ≤ (3 / 10) ^ dw := by positivity
        have h3 : (3 / 10 : ℚ) ^ dw * Zq G (A.erase w) ≤
            Zq G (A.erase w \ nbrsIn G (J.erase x) w) := by
          calc (3 / 10 : ℚ) ^ dw * Zq G (A.erase w)
              ≤ (3 / 10) ^ dw * ((10 / 3) ^ dw * Zq G (A.erase w \ nbrsIn G (J.erase x) w)) :=
                mul_le_mul_of_nonneg_left hle h0
            _ = _ := by rw [← mul_assoc, hpow, one_mul]
        nlinarith
      have hprod : 0 ≤ ∏ w ∈ N'', fac (nbrsIn G (J.erase x) w).card :=
        Finset.prod_nonneg fun i _ => (fac_pos _).le
      calc (fac dw * ∏ w ∈ N'', fac (nbrsIn G (J.erase x) w).card) * Zq G (A.erase w)
          = (∏ w ∈ N'', fac (nbrsIn G (J.erase x) w).card) * (fac dw * Zq G (A.erase w)) := by ring
        _ ≤ (∏ w ∈ N'', fac (nbrsIn G (J.erase x) w).card) * Zq G A :=
          mul_le_mul_of_nonneg_left hkey hprod
        _ ≤ Zq G (J.erase x) := ih2

/-- The combinatorial facts at a matching-essential vertex `x` of `J` (with `J' = J - x`,
`N = N_J(x)`, `M = J - N[x]`). -/
theorem essential_facts (hG : G.IsAcyclic) {J : Finset V} {x : V} (hxJ : x ∈ J)
    (hess : nuIn G J = nuIn G (J.erase x) + 1) :
    1 ≤ (nbrsIn G J x).card ∧ (J.erase x).card + 1 = J.card ∧
      ccIn G (J.erase x) + 1 = ccIn G J + (nbrsIn G J x).card ∧
      (outsideClosedNbhd G J x).card + (nbrsIn G J x).card = (J.erase x).card ∧
      ccIn G (outsideClosedNbhd G J x) + (nbrsIn G J x).card =
        ccIn G (J.erase x) + ∑ w ∈ nbrsIn G J x, (nbrsIn G (J.erase x) w).card ∧
      nuIn G (outsideClosedNbhd G J x) ≤ nuIn G (J.erase x) ∧
      (∏ w ∈ nbrsIn G J x, fac (nbrsIn G (J.erase x) w).card) * Zq G (outsideClosedNbhd G J x) ≤
        Zq G (J.erase x) ∧
      Zq G (J.erase x) ≤ (10 / 3) ^ (nbrsIn G J x).card * Zq G (outsideClosedNbhd G J x) ∧
      outsideClosedNbhd G J x ⊆ J.erase x ∧
      outsideClosedNbhd G J x = (J.erase x) \ nbrsIn G J x := by
  have hMeq : outsideClosedNbhd G J x = (J.erase x) \ nbrsIn G J x := outsideClosedNbhd_eq G J x
  have hNsub : nbrsIn G J x ⊆ J.erase x := nbrsIn_subset_erase G J x
  obtain ⟨hMcc, hlow⟩ := removal_chain hG (J := J) (x := x) (nbrsIn G J x) (Finset.Subset.refl _)
  rw [← hMeq] at hMcc hlow
  refine ⟨?_, Finset.card_erase_add_one hxJ, ccIn_erase hG hxJ, ?_, hMcc, ?_, hlow, ?_, ?_, hMeq⟩
  · by_contra h0
    push_neg at h0
    have hN0 : nbrsIn G J x = ∅ := Finset.card_eq_zero.mp (by omega)
    have := nuIn_isolated hxJ hN0
    omega
  · rw [hMeq]; exact Finset.card_sdiff_add_card_eq_card hNsub
  · exact nuIn_mono (by rw [hMeq]; exact Finset.sdiff_subset)
  · rw [hMeq]; exact Zq_le_sdiff G hNsub
  · rw [hMeq]; exact Finset.sdiff_subset

theorem ssubset_of_erase {J s : Finset V} {x : V} (hJs : J ⊆ s) (hx : x ∈ J) {A : Finset V}
    (hA : A ⊆ J.erase x) : A ⊂ s := by
  rw [Finset.ssubset_iff_of_subset (hA.trans ((Finset.erase_subset x J).trans hJs))]
  exact ⟨x, hJs hx, fun h => (Finset.mem_erase.mp (hA h)).1 rfl⟩

/-- **The length-five tail** (ceiling proof, App. R3, the `N₅` case). -/
theorem surplus_tail5 (hG : G.IsAcyclic) {s : Finset V} {x : V} {qs : List V}
    (ht : IsTail G s x qs) (hlen : qs.length = 5)
    (hess : nuIn G (tailRest s qs) = nuIn G ((tailRest s qs).erase x) + 1)
    (ih : ∀ t ⊂ s, 0 ≤ surplus G t) : 0 ≤ surplus G s := by
  obtain ⟨hZ, hS⟩ := ht.decomp 5 hlen
  have hcard := ht.card_eq
  have hnu := IsTail.nuIn_eq 2 ht (by rw [hlen]) hess
  have hcc := ht.ccIn_eq hG
  have hxJ := ht.mem
  have hJs := tailRest_subset s qs
  rw [hlen] at hcard
  generalize tailRest s qs = J at hZ hS hcard hnu hcc hxJ hJs hess
  obtain ⟨hk1, hJ'card, hJ'cc, hMcard, hMcc, hMnu, hlow, hup, hMsub, hMeq⟩ :=
    essential_facts hG hxJ hess
  have ihJ' := ih (J.erase x) (ssubset_of_erase hJs hxJ (Finset.Subset.refl _))
  have ihM := ih _ (ssubset_of_erase hJs hxJ hMsub)
  generalize outsideClosedNbhd G J x = M at *
  generalize hNdef : nbrsIn G J x = N at *
  generalize hJ' : J.erase x = J' at *
  set k := N.card with hk
  set D := ∑ w ∈ N, (nbrsIn G J' w).card with hD
  have hYpos : 0 < Zq G M := Zq_pos G M
  have tA5 : tA 5 = 1567 / 27 := by norm_num [tA]
  have tB5 : tB 5 = 80 / 3 := by norm_num [tB]
  have tC5 : tC 5 = 1036 / 9 := by norm_num [tC, tA]
  have tE5 : tE 5 = 1442 / 9 := by norm_num [tE, tB]
  rw [tA5, tB5] at hZ
  rw [tA5, tB5, tC5, tE5] at hS
  have hν : (0 : ℚ) ≤ ((nuIn G J : ℚ) - 1 - nuIn G M) * Zq G M := by
    apply mul_nonneg _ hYpos.le
    have : (nuIn G M : ℚ) ≤ nuIn G J' := by exact_mod_cast hMnu
    have h2 : (nuIn G J : ℚ) = nuIn G J' + 1 := by exact_mod_cast hess
    linarith
  have key : 189 * surplus G s = 189 * (1567 / 27) * surplus G J' +
      189 * (7 / 3 * (80 / 3)) * surplus G M + (1567 * (k : ℚ) - 1749) * Zq G J' +
      (5082 - 5880 * (k : ℚ) + 1680 * (D : ℚ)) * Zq G M +
      189 * (7 / 3 * (80 / 3)) / 3 * (((nuIn G J : ℚ) - 1 - nuIn G M) * Zq G M) := by
    have e1 : (s.card : ℚ) = J.card + 5 := by exact_mod_cast hcard
    have e2 : (nuIn G s : ℚ) = nuIn G J + 2 := by exact_mod_cast hnu
    have e3 : (ccIn G s : ℚ) = ccIn G J := by exact_mod_cast hcc
    have e4 : (J'.card : ℚ) = J.card - 1 := by
      have : (J'.card : ℚ) + 1 = J.card := by exact_mod_cast hJ'card
      linarith
    have e5 : (nuIn G J' : ℚ) = nuIn G J - 1 := by
      have : (nuIn G J : ℚ) = nuIn G J' + 1 := by exact_mod_cast hess
      linarith
    have e6 : (ccIn G J' : ℚ) = ccIn G J + k - 1 := by
      have : (ccIn G J' : ℚ) + 1 = ccIn G J + k := by exact_mod_cast hJ'cc
      linarith
    have e7 : (M.card : ℚ) = J.card - 1 - k := by
      have : (M.card : ℚ) + k = J'.card := by exact_mod_cast hMcard
      linarith
    have e8 : (ccIn G M : ℚ) = ccIn G J + D - 1 := by
      have : (ccIn G M : ℚ) + k = ccIn G J' + D := by exact_mod_cast hMcc
      linarith
    unfold surplus target
    rw [hZ, hS, e1, e2, e3, e4, e5, e6, e7, e8]
    ring
  suffices h : 0 ≤ 189 * surplus G s by linarith
  rw [key]
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- `k = 1`
    have hk1' : k = 1 := by omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hk1'
    have hDw : D = (nbrsIn G J' w).card := by rw [hD, hw, Finset.sum_singleton]
    have hkq : (k : ℚ) = 1 := by exact_mod_cast hk1'
    rcases Nat.eq_zero_or_pos D with hD0 | hD1
    · -- `D = 0`: the whole component is `P₇`; `w` is isolated in `J'`
      have hwJ' : w ∈ J' := by
        rw [← hJ']
        exact nbrsIn_subset_erase G J x (by rw [hNdef, hw]; exact Finset.mem_singleton_self w)
      have hwn : nbrsIn G J' w = ∅ := Finset.card_eq_zero.mp (by omega)
      have hMw : M = J'.erase w := by rw [hMeq, hw, Finset.sdiff_singleton_eq_erase]
      have hΦ := surplus_isolated hG hwJ' hwn
      have hZw := Zq_isolated G hwJ' hwn
      have hνw := nuIn_isolated hwJ' hwn
      rw [← hMw] at hΦ hZw hνw
      have hνq : (nuIn G J : ℚ) - 1 - nuIn G M = 0 := by
        have : (nuIn G J : ℚ) = nuIn G J' + 1 := by exact_mod_cast hess
        have h2 : (nuIn G J' : ℚ) = nuIn G M := by exact_mod_cast hνw
        linarith
      have hD0q : (D : ℚ) = 0 := by exact_mod_cast hD0
      rw [hνq, hD0q, hkq, hΦ, hZw]
      linarith
    · -- `D ≥ 1`: the upper ratio bound `Q ≤ 10/3` pays
      have hDq : (1 : ℚ) ≤ D := by exact_mod_cast hD1
      rw [hk1'] at hup
      rw [hkq]
      nlinarith
  · -- `k ≥ 2`: the lower ratio bound `Q ≥ P` and `N₅ ≥ 0`
    have hN5 := N5_nonneg N (fun w => (nbrsIn G J' w).card) hk2
    have hDq : ∑ w ∈ N, ((nbrsIn G J' w).card : ℚ) = (D : ℚ) := by rw [hD]; push_cast; rfl
    rw [hDq] at hN5
    have hc : (0 : ℚ) ≤ 1567 * (k : ℚ) - 1749 := by
      have : (2 : ℚ) ≤ k := by exact_mod_cast hk2
      linarith
    have h1 := mul_le_mul_of_nonneg_left hlow hc
    nlinarith [mul_nonneg hYpos.le hN5]

/-- **The length-three tail** (ceiling proof, App. R3, the `N₃` case).  For `k = 1`, `D = 1` the same
forest has a length-five tail at the next vertex, handled by `surplus_tail5`. -/
theorem surplus_tail3 (hG : G.IsAcyclic) {s : Finset V} {x : V} {qs : List V}
    (ht : IsTail G s x qs) (hlen : qs.length = 3)
    (hess : nuIn G (tailRest s qs) = nuIn G ((tailRest s qs).erase x) + 1)
    (ih : ∀ t ⊂ s, 0 ≤ surplus G t) : 0 ≤ surplus G s := by
  obtain ⟨hZ, hS⟩ := ht.decomp 3 hlen
  have hcard := ht.card_eq
  have hnu := IsTail.nuIn_eq 1 ht (by rw [hlen]) hess
  have hcc := ht.ccIn_eq hG
  have hxJ := ht.mem
  have hJs := tailRest_subset s qs
  rw [hlen] at hcard
  generalize hJdef : tailRest s qs = J at hZ hS hcard hnu hcc hxJ hJs hess
  obtain ⟨hk1, hJ'card, hJ'cc, hMcard, hMcc, hMnu, hlow, hup, hMsub, hMeq⟩ :=
    essential_facts hG hxJ hess
  have ihJ' := ih (J.erase x) (ssubset_of_erase hJs hxJ (Finset.Subset.refl _))
  have ihM := ih _ (ssubset_of_erase hJs hxJ hMsub)
  generalize outsideClosedNbhd G J x = M at *
  generalize hNdef : nbrsIn G J x = N at *
  generalize hJ' : J.erase x = J' at *
  set k := N.card with hk
  set D := ∑ w ∈ N, (nbrsIn G J' w).card with hD
  have hYpos : 0 < Zq G M := Zq_pos G M
  have tA3 : tA 3 = 121 / 9 := by norm_num [tA]
  have tB3 : tB 3 = 17 / 3 := by norm_num [tB]
  have tC3 : tC 3 = 161 / 9 := by norm_num [tC, tA]
  have tE3 : tE 3 = 217 / 9 := by norm_num [tE, tB]
  rw [tA3, tB3] at hZ
  rw [tA3, tB3, tC3, tE3] at hS
  have hν : (0 : ℚ) ≤ ((nuIn G J : ℚ) - 1 - nuIn G M) * Zq G M := by
    apply mul_nonneg _ hYpos.le
    have : (nuIn G M : ℚ) ≤ nuIn G J' := by exact_mod_cast hMnu
    have h2 : (nuIn G J : ℚ) = nuIn G J' + 1 := by exact_mod_cast hess
    linarith
  have key : 378 * surplus G s = 378 * (121 / 9) * surplus G J' +
      378 * (7 / 3 * (17 / 3)) * surplus G M + (726 * (k : ℚ) - 740) * Zq G J' +
      (1736 - 2499 * (k : ℚ) + 714 * (D : ℚ)) * Zq G M +
      378 * (7 / 3 * (17 / 3)) / 3 * (((nuIn G J : ℚ) - 1 - nuIn G M) * Zq G M) := by
    have e1 : (s.card : ℚ) = J.card + 3 := by exact_mod_cast hcard
    have e2 : (nuIn G s : ℚ) = nuIn G J + 1 := by exact_mod_cast hnu
    have e3 : (ccIn G s : ℚ) = ccIn G J := by exact_mod_cast hcc
    have e4 : (J'.card : ℚ) = J.card - 1 := by
      have : (J'.card : ℚ) + 1 = J.card := by exact_mod_cast hJ'card
      linarith
    have e5 : (nuIn G J' : ℚ) = nuIn G J - 1 := by
      have : (nuIn G J : ℚ) = nuIn G J' + 1 := by exact_mod_cast hess
      linarith
    have e6 : (ccIn G J' : ℚ) = ccIn G J + k - 1 := by
      have : (ccIn G J' : ℚ) + 1 = ccIn G J + k := by exact_mod_cast hJ'cc
      linarith
    have e7 : (M.card : ℚ) = J.card - 1 - k := by
      have : (M.card : ℚ) + k = J'.card := by exact_mod_cast hMcard
      linarith
    have e8 : (ccIn G M : ℚ) = ccIn G J + D - 1 := by
      have : (ccIn G M : ℚ) + k = ccIn G J' + D := by exact_mod_cast hMcc
      linarith
    unfold surplus target
    rw [hZ, hS, e1, e2, e3, e4, e5, e6, e7, e8]
    ring
  suffices h : 0 ≤ 378 * surplus G s by linarith
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- `k = 1`
    have hk1' : k = 1 := by omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hk1'
    have hDw : D = (nbrsIn G J' w).card := by rw [hD, hw, Finset.sum_singleton]
    have hkq : (k : ℚ) = 1 := by exact_mod_cast hk1'
    have hwJ' : w ∈ J' := by
      rw [← hJ']
      exact nbrsIn_subset_erase G J x (by rw [hNdef, hw]; exact Finset.mem_singleton_self w)
    rcases Nat.lt_or_ge D 2 with hD2 | hD2
    · rcases Nat.eq_zero_or_pos D with hD0 | hD1
      · -- `D = 0`: the whole component is `P₅`; `w` is isolated in `J'`
        have hwn : nbrsIn G J' w = ∅ := Finset.card_eq_zero.mp (by omega)
        have hMw : M = J'.erase w := by rw [hMeq, hw, Finset.sdiff_singleton_eq_erase]
        have hΦ := surplus_isolated hG hwJ' hwn
        have hZw := Zq_isolated G hwJ' hwn
        have hνw := nuIn_isolated hwJ' hwn
        rw [← hMw] at hΦ hZw hνw
        have hνq : (nuIn G J : ℚ) - 1 - nuIn G M = 0 := by
          have : (nuIn G J : ℚ) = nuIn G J' + 1 := by exact_mod_cast hess
          have h2 : (nuIn G J' : ℚ) = nuIn G M := by exact_mod_cast hνw
          linarith
        have hD0q : (D : ℚ) = 0 := by exact_mod_cast hD0
        rw [key, hνq, hD0q, hkq, hΦ, hZw]
        linarith
      · -- `D = 1`: the same forest has a length-five tail at the neighbour `y` of `w`
        have hD1' : (nbrsIn G J' w).card = 1 := by omega
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hD1'
        have hyJ2 : y ∈ J'.erase w :=
          nbrsIn_subset_erase G J' w (by rw [hy]; exact Finset.mem_singleton_self y)
        have hxw : nbrsIn G (tailRest s qs) x = {w} := by rw [hJdef, hNdef, hw]
        have hwy : nbrsIn G ((tailRest s qs).erase x) w = {y} := by rw [hJdef, hJ', hy]
        have hyr : y ∈ ((tailRest s qs).erase x).erase w := by rw [hJdef, hJ']; exact hyJ2
        obtain ⟨ht5, hrest⟩ := ht.append hxw hwy hyr
        rw [hJdef, hJ'] at hrest
        have hlen5 : (qs ++ [x, w]).length = 5 := by simp [hlen]
        have hess5 : nuIn G (tailRest s (qs ++ [x, w])) =
            nuIn G ((tailRest s (qs ++ [x, w])).erase y) + 1 := by
          rw [hrest]
          have hwJ : nbrsIn G J x = {w} := by rw [hNdef, hw]
          have h1 := nuIn_pendant hxJ hwJ
          have h2 := nuIn_pendant hwJ' hy
          rw [hJ'] at h1
          omega
        have h5 := surplus_tail5 hG ht5 hlen5 hess5 ih
        linarith
    · -- `D ≥ 2`: the upper ratio bound `Q ≤ 10/3` pays
      have hDq : (2 : ℚ) ≤ D := by exact_mod_cast hD2
      rw [hk1'] at hup
      rw [key, hkq]
      nlinarith
  · -- `k ≥ 2`: the lower ratio bound `Q ≥ P` and `N₃ ≥ 0`
    have hN3 := N3_nonneg N (fun w => (nbrsIn G J' w).card) hk2
    have hDq : ∑ w ∈ N, ((nbrsIn G J' w).card : ℚ) = (D : ℚ) := by rw [hD]; push_cast; rfl
    rw [hDq] at hN3
    have hc : (0 : ℚ) ≤ 726 * (k : ℚ) - 740 := by
      have : (2 : ℚ) ≤ k := by exact_mod_cast hk2
      linarith
    have h1 := mul_le_mul_of_nonneg_left hlow hc
    rw [key]
    nlinarith [mul_nonneg hYpos.le hN3]

end Occupation
end Erdos993Lean
