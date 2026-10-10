module

public import Mathlib
public import Erdos993Lean.Floor.TreeDecomp

/-!
# B5, part 3: the number of connected components of an induced subgraph

`ccIn G s` counts the connected components of `G[s]`, isolated vertices included (the convention of
B5: "cc is the number of connected components including isolates"), as the number
of distinct components `compIn G s x` (`Floor/TreeDecomp.lean`).  Proved here: additivity over
edge-free disjoint unions and finite families (`ccIn_union`, `ccIn_biUnion`); one component for a
nonempty connected set; `|r|` components for an edgeless set; and, in a forest, deleting a vertex of
degree `d` adds `d - 1` components, `cc(s - x) + 1 = cc(s) + deg_s(x)` (`ccIn_erase`, via the
branches at `x`).  The bridge `ccIn G univ = Nat.card G.ConnectedComponent` is in
`Occupation/Main.lean`.
-/

@[expose] public section

namespace Erdos993Lean
namespace Occupation

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The number of connected components of `G[s]` (isolated vertices included). -/
noncomputable def ccIn (s : Finset V) : ℕ := (s.image (compIn G s)).card

variable {G}

theorem ccIn_empty : ccIn G (∅ : Finset V) = 0 := by
  simp [ccIn]

/-- Inside a disjoint union with no edges between the parts, chains from `A` stay in `A`. -/
theorem reachIn_union_left {A B : Finset V} (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) {x y : V}
    (hx : x ∈ A) (h : ReachIn G (A ∪ B) x y) : y ∈ A ∧ ReachIn G A x y := by
  induction h with
  | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨hcA, hxc⟩ := ih
    have hdA : d ∈ A := by
      rcases Finset.mem_union.mp hcd.2.1 with h | h
      · exact h
      · exact absurd hcd.2.2 (hno c hcA d h)
    exact ⟨hdA, hxc.tail ⟨hcA, hdA, hcd.2.2⟩⟩

omit [DecidableEq V] in
theorem reachIn_mono {A B : Finset V} (hAB : A ⊆ B) {x y : V} (h : ReachIn G A x y) :
    ReachIn G B x y :=
  Relation.ReflTransGen.mono (fun _ _ hab => ⟨hAB hab.1, hAB hab.2.1, hab.2.2⟩) _ _ h

theorem compIn_union_left {A B : Finset V} (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) {x : V}
    (hx : x ∈ A) : compIn G (A ∪ B) x = compIn G A x := by
  ext y
  rw [mem_compIn, mem_compIn]
  constructor
  · rintro ⟨_, h⟩
    exact reachIn_union_left hno hx h
  · rintro ⟨hy, h⟩
    exact ⟨Finset.mem_union_left B hy, reachIn_mono Finset.subset_union_left h⟩

/-- Component counts add over a disjoint union with no edges between the parts. -/
theorem ccIn_union {A B : Finset V} (hAB : Disjoint A B) (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    ccIn G (A ∪ B) = ccIn G A + ccIn G B := by
  have hno' : ∀ b ∈ B, ∀ a ∈ A, ¬ G.Adj b a := fun b hb a ha h => hno a ha b hb h.symm
  have h1 : A.image (compIn G (A ∪ B)) = A.image (compIn G A) :=
    Finset.image_congr (fun x hx => compIn_union_left hno hx)
  have h2 : B.image (compIn G (A ∪ B)) = B.image (compIn G B) := by
    apply Finset.image_congr
    intro x hx
    rw [Finset.union_comm]
    exact compIn_union_left hno' hx
  unfold ccIn
  rw [Finset.image_union, h1, h2]
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro C hCA hCB
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hCA
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hCB
  have hxC : x ∈ compIn G B y := by rw [hxy]; exact self_mem_compIn hx
  exact Finset.disjoint_left.mp hAB hx (compIn_subset _ _ hxC)

/-- A nonempty connected vertex set has one component. -/
theorem ccIn_eq_one {s : Finset V} (hs : ConnectedIn G s) (hne : s.Nonempty) : ccIn G s = 1 := by
  unfold ccIn
  rw [Finset.card_eq_one]
  refine ⟨s, ?_⟩
  obtain ⟨x0, hx0⟩ := hne
  ext C
  rw [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    ext y
    rw [mem_compIn]
    exact ⟨fun h => h.1, fun hy => ⟨hy, hs x hx y hy⟩⟩
  · rintro rfl
    refine ⟨x0, hx0, ?_⟩
    ext y
    rw [mem_compIn]
    exact ⟨fun h => h.1, fun hy => ⟨hy, hs x0 hx0 y hy⟩⟩

/-- Component counts add over a finite family of pairwise disjoint parts with no edges between
distinct parts. -/
theorem ccIn_biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (f i) (f j))
    (hno : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, ¬ G.Adj a b) :
    ccIn G (I.biUnion f) = ∑ i ∈ I, ccIn G (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [ccIn_empty]
  | insert i I hiI ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hiI]
    rw [ccIn_union ?_ ?_, ih ?_ ?_]
    · intro j hj k hk hjk
      exact hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    · intro j hj k hk hjk
      exact hno j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    · rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun h => hiI (h ▸ hj))
    · intro a ha b hb
      rw [Finset.mem_biUnion] at hb
      obtain ⟨j, hj, hbj⟩ := hb
      exact hno i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun h => hiI (h ▸ hj)) a ha b hbj

/-- An edgeless vertex set has as many components as vertices. -/
theorem ccIn_edgeless {r : Finset V} (hr : ∀ a ∈ r, ∀ b ∈ r, ¬ G.Adj a b) : ccIn G r = r.card := by
  have hsing : ∀ x ∈ r, compIn G r x = {x} := by
    intro x hx
    ext y
    rw [mem_compIn, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hxc, _⟩
      · exact h.symm
      · exact absurd hxc.2.2 (hr x hx c hxc.2.1)
    · rintro rfl
      exact ⟨hx, Relation.ReflTransGen.refl⟩
  unfold ccIn
  rw [Finset.image_congr hsing]
  exact Finset.card_image_of_injective r (fun a b h => Finset.singleton_injective h)

variable [DecidableRel G.Adj]

/-- **Deleting a vertex of degree `d` from a forest adds `d - 1` components**:
`cc(s - x) + 1 = cc(s) + deg_s(x)`. -/
theorem ccIn_erase (hG : G.IsAcyclic) {s : Finset V} {x : V} (hx : x ∈ s) :
    ccIn G (s.erase x) + 1 = ccIn G s + (nbrsIn G s x).card := by
  classical
  set C := compIn G s x with hC
  set R := s \ C with hR
  have hCs : C ⊆ s := compIn_subset _ _
  have hxC : x ∈ C := self_mem_compIn hx
  have hdisj : Disjoint C R := Finset.disjoint_sdiff
  have hno : ∀ a ∈ C, ∀ b ∈ R, ¬ G.Adj a b := by
    intro a ha b hb hab
    have hbs : b ∈ s := (Finset.mem_sdiff.mp hb).1
    exact (Finset.mem_sdiff.mp hb).2 (mem_compIn_of_adjIn ha ⟨hCs ha, hbs, hab⟩)
  have hsCR : s = C ∪ R := (Finset.union_sdiff_of_subset hCs).symm
  have hconn : ConnectedIn G C := connectedIn_compIn s x
  -- the count for `s`
  have h1 : ccIn G s = 1 + ccIn G R := by
    conv_lhs => rw [hsCR]
    rw [ccIn_union hdisj hno, ccIn_eq_one hconn ⟨x, hxC⟩]
  -- the count for `s - x`
  have hsx : s.erase x = C.erase x ∪ R := by
    rw [hsCR, Finset.erase_union_distrib]
    congr 1
    apply Finset.erase_eq_of_notMem
    intro h
    exact (Finset.mem_sdiff.mp h).2 hxC
  have h2 : ccIn G (s.erase x) = ccIn G (C.erase x) + ccIn G R := by
    rw [hsx]
    exact ccIn_union (hdisj.mono_left (Finset.erase_subset x C))
      (fun a ha b hb => hno a (Finset.mem_of_mem_erase ha) b hb)
  -- the branches at `x`
  have h3 : ccIn G (C.erase x) = (nbrsIn G C x).card := by
    rw [erase_eq_biUnion hconn hxC, ccIn_biUnion]
    · rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨hbr, hwbr, _⟩ := compIn_branch hG hconn hxC hw
      exact ccIn_eq_one hbr ⟨w, hwbr⟩
    · exact fun i hi j hj hij => disjoint_branches hG hi hj hij
    · exact fun i hi j hj hij a ha b hb => not_adj_branches hG hi hj hij ha hb
  have h4 : nbrsIn G C x = nbrsIn G s x := by
    ext w
    rw [mem_nbrsIn, mem_nbrsIn]
    constructor
    · exact fun h => ⟨hCs h.1, h.2⟩
    · exact fun h => ⟨mem_compIn_of_adjIn hxC ⟨hx, h.1, h.2⟩, h.2⟩
  rw [h2, h1, h3, h4]
  ring

end Occupation
end Erdos993Lean
