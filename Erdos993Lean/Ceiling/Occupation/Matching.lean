module

public import Mathlib
public import Erdos993Lean.Floor.TreeDecomp

/-!
# B5, part 2: the matching number of an induced subgraph

`nuIn G s` is the matching number `ν(G[s])`: the largest number of pairwise vertex-disjoint edges of
`G` with both ends in `s` (the disjointness condition of `matchingNumber`,
`Ceiling/Statement.lean`).
Proved here: monotonicity (`nuIn_mono`); `ν(s) ≤ ν(s - v) + 1` (`nuIn_le_erase_add_one`); the
leaf-stem recurrence `ν(s) = ν(s - ℓ - a) + 1` for a pendant vertex `ℓ` with neighbour `a`
(`nuIn_pendant`; some maximum matching uses the pendant edge); additivity over edge-free disjoint
unions (`nuIn_union`); `ν = 0` on edgeless sets; isolated vertices do not matter
(`nuIn_isolated`).  These are the matching facts used by B5 (the ceiling proof,
Appendix R3).  The bridge `nuIn G univ = matchingNumber G` is in
`Occupation/Main.lean`.
-/

@[expose] public section

namespace Erdos993Lean
namespace Occupation

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `M` is a matching of `G` inside the vertex set `s`: edges of `G` with both ends in `s`, pairwise
vertex-disjoint (the same disjointness condition as `matchingNumber`). -/
def IsMatchingIn (s : Finset V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet ∧ ∀ a ∈ e, a ∈ s) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ a ∈ e, a ∉ f

/-- The matching number `ν(G[s])` of the subgraph induced on `s`. -/
noncomputable def nuIn (s : Finset V) : ℕ := by
  classical
  exact ((s.sym2.filter (· ∈ G.edgeSet)).powerset.filter (IsMatchingIn G s)).sup Finset.card

variable {G}

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem IsMatchingIn.subset_sym2 {s : Finset V} {M : Finset (Sym2 V)} (h : IsMatchingIn G s M) :
    ∀ e ∈ M, e ∈ s.sym2 ∧ e ∈ G.edgeSet := fun e he =>
  ⟨Finset.mem_sym2_iff.mpr (h.1 e he).2, (h.1 e he).1⟩

omit [DecidableEq V] in
theorem le_nuIn {s : Finset V} {M : Finset (Sym2 V)} (h : IsMatchingIn G s M) :
    M.card ≤ nuIn G s := by
  classical
  unfold nuIn
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun e he => ?_, h⟩
  rw [Finset.mem_filter]
  exact h.subset_sym2 e he

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem isMatchingIn_empty (s : Finset V) : IsMatchingIn G s ∅ :=
  ⟨fun e he => absurd he (Finset.notMem_empty e), fun e he => absurd he (Finset.notMem_empty e)⟩

omit [DecidableEq V] in
variable (G) in
theorem exists_isMatchingIn_card_eq (s : Finset V) :
    ∃ M, IsMatchingIn G s M ∧ M.card = nuIn G s := by
  classical
  unfold nuIn
  obtain ⟨M, hM, hMeq⟩ := Finset.exists_mem_eq_sup
    ((s.sym2.filter (· ∈ G.edgeSet)).powerset.filter (IsMatchingIn G s))
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, isMatchingIn_empty s⟩⟩ Finset.card
  exact ⟨M, (Finset.mem_filter.mp hM).2, hMeq.symm⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem IsMatchingIn.mono {s s' : Finset V} {M : Finset (Sym2 V)} (h : IsMatchingIn G s M)
    (hss : s ⊆ s') : IsMatchingIn G s' M :=
  ⟨fun e he => ⟨(h.1 e he).1, fun a ha => hss ((h.1 e he).2 a ha)⟩, h.2⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem IsMatchingIn.filter {s : Finset V} {M : Finset (Sym2 V)} (h : IsMatchingIn G s M)
    (p : Sym2 V → Prop) [DecidablePred p] : IsMatchingIn G s (M.filter p) :=
  ⟨fun e he => h.1 e (Finset.mem_of_mem_filter e he),
    fun e he f hf => h.2 e (Finset.mem_of_mem_filter e he) f (Finset.mem_of_mem_filter f hf)⟩

omit [DecidableEq V] in
theorem nuIn_mono {s s' : Finset V} (hss : s ⊆ s') : nuIn G s ≤ nuIn G s' := by
  obtain ⟨M, hM, hMc⟩ := exists_isMatchingIn_card_eq G s
  rw [← hMc]
  exact le_nuIn (hM.mono hss)

omit [DecidableRel G.Adj] in
/-- At most one edge of a matching contains a given vertex. -/
theorem IsMatchingIn.card_filter_mem_le_one {s : Finset V} {M : Finset (Sym2 V)}
    (h : IsMatchingIn G s M) (a : V) : (M.filter (fun e => a ∈ e)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he f hf
  rw [Finset.mem_filter] at he hf
  by_contra hne
  exact h.2 e he.1 f hf.1 hne a he.2 hf.2

omit [DecidableEq V] in
/-- An edge of `G` inside `s` through a pendant vertex `ℓ` of `s` with stem `a` contains `a`. -/
theorem mem_of_pendant {s : Finset V} {ℓ a : V} (hn : nbrsIn G s ℓ = {a}) {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hes : ∀ b ∈ e, b ∈ s) (hℓ : ℓ ∈ e) : a ∈ e := by
  obtain ⟨q, rfl⟩ := Sym2.mem_iff_exists.mp hℓ
  have hq : q ∈ nbrsIn G s ℓ := mem_nbrsIn.mpr ⟨hes q (Sym2.mem_mk_right ℓ q), he⟩
  rw [hn, Finset.mem_singleton] at hq
  rw [hq]
  exact Sym2.mem_mk_right ℓ a

/-- Deleting a vertex lowers the matching number by at most one. -/
theorem nuIn_le_erase_add_one (s : Finset V) (v : V) : nuIn G s ≤ nuIn G (s.erase v) + 1 := by
  classical
  obtain ⟨M, hM, hMc⟩ := exists_isMatchingIn_card_eq G s
  have h1 : IsMatchingIn G (s.erase v) (M.filter (fun e => v ∉ e)) := by
    refine ⟨fun e he => ?_, (hM.filter _).2⟩
    rw [Finset.mem_filter] at he
    refine ⟨(hM.1 e he.1).1, fun b hb => Finset.mem_erase.mpr ⟨?_, (hM.1 e he.1).2 b hb⟩⟩
    rintro rfl
    exact he.2 hb
  have h2 := le_nuIn h1
  have h3 := hM.card_filter_mem_le_one v
  have h4 := Finset.card_filter_add_card_filter_not (s := M) (fun e => v ∈ e)
  omega

/-- The leaf-stem recurrence: if `ℓ` is a pendant vertex of `s` with stem `a`, then
`ν(s) = ν(s - ℓ - a) + 1`. -/
theorem nuIn_pendant {s : Finset V} {ℓ a : V} (hℓ : ℓ ∈ s) (hn : nbrsIn G s ℓ = {a}) :
    nuIn G s = nuIn G ((s.erase ℓ).erase a) + 1 := by
  classical
  have ha : a ∈ nbrsIn G s ℓ := by rw [hn]; exact Finset.mem_singleton_self a
  obtain ⟨has, hadj⟩ := mem_nbrsIn.mp ha
  apply le_antisymm
  · obtain ⟨M, hM, hMc⟩ := exists_isMatchingIn_card_eq G s
    have h1 : IsMatchingIn G ((s.erase ℓ).erase a) (M.filter (fun e => ℓ ∉ e ∧ a ∉ e)) := by
      refine ⟨fun e he => ?_, (hM.filter _).2⟩
      rw [Finset.mem_filter] at he
      refine ⟨(hM.1 e he.1).1, fun b hb => ?_⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, (hM.1 e he.1).2 b hb⟩⟩
      · rintro rfl; exact he.2.2 hb
      · rintro rfl; exact he.2.1 hb
    have h2 := le_nuIn h1
    have h3 := hM.card_filter_mem_le_one a
    have h4 := Finset.card_filter_add_card_filter_not (s := M) (fun e => ℓ ∉ e ∧ a ∉ e)
    have h5 : (M.filter (fun e => ¬ (ℓ ∉ e ∧ a ∉ e))).card ≤ (M.filter (fun e => a ∈ e)).card := by
      apply Finset.card_le_card
      intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨he.1, ?_⟩
      by_cases hℓe : ℓ ∈ e
      · exact mem_of_pendant hn (hM.1 e he.1).1 (hM.1 e he.1).2 hℓe
      · by_contra hae
        exact he.2 ⟨hℓe, hae⟩
    omega
  · obtain ⟨M, hM, hMc⟩ := exists_isMatchingIn_card_eq G ((s.erase ℓ).erase a)
    have hnot : ∀ e ∈ M, ℓ ∉ e ∧ a ∉ e := by
      intro e he
      constructor
      · intro h
        have := (hM.1 e he).2 ℓ h
        simp at this
      · intro h
        have := (hM.1 e he).2 a h
        simp at this
    have hnew : s(ℓ, a) ∉ M := fun h => (hnot _ h).1 (Sym2.mem_mk_left ℓ a)
    have h1 : IsMatchingIn G s (insert s(ℓ, a) M) := by
      refine ⟨fun e he => ?_, fun e he f hf hef => ?_⟩
      · rw [Finset.mem_insert] at he
        rcases he with rfl | he
        · refine ⟨hadj, fun b hb => ?_⟩
          rcases Sym2.mem_iff.mp hb with rfl | rfl
          · exact hℓ
          · exact has
        · exact ⟨(hM.1 e he).1, fun b hb =>
            Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ((hM.1 e he).2 b hb))⟩
      · rw [Finset.mem_insert] at he hf
        rcases he with rfl | he <;> rcases hf with rfl | hf
        · exact absurd rfl hef
        · intro b hb hbf
          rcases Sym2.mem_iff.mp hb with rfl | rfl
          · exact (hnot f hf).1 hbf
          · exact (hnot f hf).2 hbf
        · intro b hbe hb
          rcases Sym2.mem_iff.mp hb with rfl | rfl
          · exact (hnot e he).1 hbe
          · exact (hnot e he).2 hbe
        · exact hM.2 e he f hf hef
    have h2 := le_nuIn h1
    rw [Finset.card_insert_of_notMem hnew] at h2
    omega

/-- Matching numbers add over a disjoint union with no edges between the parts. -/
theorem nuIn_union {s t : Finset V} (hst : Disjoint s t) (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    nuIn G (s ∪ t) = nuIn G s + nuIn G t := by
  classical
  apply le_antisymm
  · obtain ⟨M, hM, hMc⟩ := exists_isMatchingIn_card_eq G (s ∪ t)
    -- every edge of `M` lies inside `s` or inside `t`
    have hsplit : ∀ e ∈ M, (∀ b ∈ e, b ∈ s) ∨ (∀ b ∈ e, b ∈ t) := by
      intro e he
      obtain ⟨hadj, hin⟩ := hM.1 e he
      induction e using Sym2.ind with
      | h x y =>
        have hx := hin x (Sym2.mem_mk_left x y)
        have hy := hin y (Sym2.mem_mk_right x y)
        rw [SimpleGraph.mem_edgeSet] at hadj
        rw [Finset.mem_union] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · left; intro b hb; rcases Sym2.mem_iff.mp hb with rfl | rfl <;> assumption
        · exact absurd hadj (hno x hx y hy)
        · exact absurd hadj.symm (hno y hy x hx)
        · right; intro b hb; rcases Sym2.mem_iff.mp hb with rfl | rfl <;> assumption
    have h1 : IsMatchingIn G s (M.filter (fun e => ∀ b ∈ e, b ∈ s)) := by
      refine ⟨fun e he => ?_, (hM.filter _).2⟩
      rw [Finset.mem_filter] at he
      exact ⟨(hM.1 e he.1).1, he.2⟩
    have h2 : IsMatchingIn G t (M.filter (fun e => ¬ ∀ b ∈ e, b ∈ s)) := by
      refine ⟨fun e he => ?_, (hM.filter _).2⟩
      rw [Finset.mem_filter] at he
      refine ⟨(hM.1 e he.1).1, ?_⟩
      rcases hsplit e he.1 with h | h
      · exact absurd h he.2
      · exact h
    have h3 := le_nuIn h1
    have h4 := le_nuIn h2
    have h5 := Finset.card_filter_add_card_filter_not (s := M) (fun e => ∀ b ∈ e, b ∈ s)
    omega
  · obtain ⟨M, hM, hMc⟩ := exists_isMatchingIn_card_eq G s
    obtain ⟨N, hN, hNc⟩ := exists_isMatchingIn_card_eq G t
    have hne : ∀ e ∈ M, ∀ f ∈ N, ∀ b ∈ e, b ∉ f := by
      intro e he f hf b hbe hbf
      exact Finset.disjoint_left.mp hst ((hM.1 e he).2 b hbe) ((hN.1 f hf).2 b hbf)
    have hdisj : Disjoint M N := by
      rw [Finset.disjoint_left]
      intro e he hf
      induction e using Sym2.ind with
      | h x y => exact hne _ he _ hf x (Sym2.mem_mk_left x y) (Sym2.mem_mk_left x y)
    have h1 : IsMatchingIn G (s ∪ t) (M ∪ N) := by
      refine ⟨fun e he => ?_, fun e he f hf hef => ?_⟩
      · rw [Finset.mem_union] at he
        rcases he with he | he
        · exact ⟨(hM.1 e he).1, fun b hb => Finset.mem_union_left t ((hM.1 e he).2 b hb)⟩
        · exact ⟨(hN.1 e he).1, fun b hb => Finset.mem_union_right s ((hN.1 e he).2 b hb)⟩
      · rw [Finset.mem_union] at he hf
        rcases he with he | he <;> rcases hf with hf | hf
        · exact hM.2 e he f hf hef
        · exact hne e he f hf
        · intro b hbe hbf
          exact hne f hf e he b hbf hbe
        · exact hN.2 e he f hf hef
    have h2 := le_nuIn h1
    rw [Finset.card_union_of_disjoint hdisj] at h2
    omega

omit [DecidableEq V] in
/-- An edgeless vertex set has matching number `0`. -/
theorem nuIn_eq_zero_of_edgeless {r : Finset V} (hr : ∀ a ∈ r, ∀ b ∈ r, ¬ G.Adj a b) :
    nuIn G r = 0 := by
  obtain ⟨M, hM, hMc⟩ := exists_isMatchingIn_card_eq G r
  rw [← hMc, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro e he
  obtain ⟨hadj, hin⟩ := hM.1 e he
  induction e using Sym2.ind with
  | h x y =>
    exact hr x (hin x (Sym2.mem_mk_left x y)) y (hin y (Sym2.mem_mk_right x y)) hadj

/-- Deleting an isolated vertex does not change the matching number. -/
theorem nuIn_isolated {s : Finset V} {x : V} (hx : x ∈ s) (hxn : nbrsIn G s x = ∅) :
    nuIn G s = nuIn G (s.erase x) := by
  have hno : ∀ a ∈ ({x} : Finset V), ∀ b ∈ s.erase x, ¬ G.Adj a b := by
    intro a ha b hb hab
    rw [Finset.mem_singleton] at ha
    subst ha
    have : b ∈ nbrsIn G s a := mem_nbrsIn.mpr ⟨Finset.mem_of_mem_erase hb, hab⟩
    rw [hxn] at this
    exact Finset.notMem_empty b this
  have hdisj : Disjoint ({x} : Finset V) (s.erase x) := by simp
  have hs : s = {x} ∪ s.erase x := by
    rw [← Finset.insert_eq, Finset.insert_erase hx]
  conv_lhs => rw [hs]
  rw [nuIn_union hdisj hno, nuIn_eq_zero_of_edgeless (by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    subst ha; subst hb
    exact G.irrefl), zero_add]

end Occupation
end Erdos993Lean
