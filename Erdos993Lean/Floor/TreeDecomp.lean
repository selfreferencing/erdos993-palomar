module

public import Mathlib
public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Floor.RootedPair
public import Erdos993Lean.Caterpillar.Structure

/-!
# Rooted decomposition of trees inside a forest, and centroids

Inside a fixed acyclic graph `G`, a vertex set `s` that induces a connected subgraph is a tree.
Deleting a vertex `r ∈ s` splits `s` into branches, one for each neighbour `w` of `r` in `s`; the
branch of `w` is the component `compIn G (s.erase r) w`, and `w` is the only neighbour of `r` in
it.  Hence

  `I(s) = ∏_w I(C_w) + x ∏_w I(C_w - w)`,

which shows (by induction) that every rooted tree inside `G` yields a `RootedPair`.

We also prove Jordan's centroid theorem in this setting: every such `s` has a vertex `c` all of
whose branches have at most `|s| / 2` vertices.
-/

@[expose] public section

namespace Erdos993Lean

open Finset Polynomial

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Adjacency inside the vertex set `s`. -/
def AdjIn (G : SimpleGraph V) (s : Finset V) (a b : V) : Prop :=
  a ∈ s ∧ b ∈ s ∧ G.Adj a b

/-- Reachability inside the vertex set `s`. -/
def ReachIn (G : SimpleGraph V) (s : Finset V) : V → V → Prop :=
  Relation.ReflTransGen (AdjIn G s)

/-- `s` induces a connected subgraph of `G`. -/
def ConnectedIn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ReachIn G s x y

/-- The connected component of `x` in the subgraph induced on `s`. -/
noncomputable def compIn (G : SimpleGraph V) (s : Finset V) (x : V) : Finset V := by
  classical
  exact s.filter (ReachIn G s x)

/-- The neighbours of `r` inside `s`. -/
def nbrsIn (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (r : V) : Finset V :=
  s.filter (G.Adj r)

/-! ### Basic facts about `ReachIn` and `compIn` -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem mem_compIn {s : Finset V} {x y : V} : y ∈ compIn G s x ↔ y ∈ s ∧ ReachIn G s x y := by
  simp only [compIn, Finset.mem_filter]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem compIn_subset (s : Finset V) (x : V) : compIn G s x ⊆ s :=
  fun _ hy => (mem_compIn.mp hy).1

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem self_mem_compIn {s : Finset V} {x : V} (hx : x ∈ s) : x ∈ compIn G s x :=
  mem_compIn.mpr ⟨hx, Relation.ReflTransGen.refl⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem ReachIn.symm {s : Finset V} {x y : V} (h : ReachIn G s x y) : ReachIn G s y x :=
  (@Relation.ReflTransGen.stdSymm _ (AdjIn G s) ⟨fun _ _ hab => ⟨hab.2.1, hab.1, hab.2.2.symm⟩⟩).symm _ _ h

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem ReachIn.trans {s : Finset V} {x y z : V} (h1 : ReachIn G s x y) (h2 : ReachIn G s y z) :
    ReachIn G s x z :=
  Relation.ReflTransGen.trans h1 h2

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A chain inside `s` ending in `s` gives a walk of `G` all of whose vertices lie in `s`. -/
theorem ReachIn.exists_walk {s : Finset V} {x y : V} (h : ReachIn G s x y) (hy : y ∈ s) :
    ∃ p : G.Walk x y, ∀ v ∈ p.support, v ∈ s := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simp [hy]⟩
  | head hac _ ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨SimpleGraph.Walk.cons hac.2.2 p, ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hac.1
    · exact hp v hv

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A walk all of whose vertices lie in `s` gives a chain inside `s`. -/
theorem reachIn_of_walk {s : Finset V} {x y : V} (p : G.Walk x y)
    (hp : ∀ v ∈ p.support, v ∈ s) : ReachIn G s x y := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons h q ih =>
    exact Relation.ReflTransGen.head ⟨hp _ (by simp), hp _ (by simp), h⟩
      (ih fun v hv => hp v (by simp [hv]))

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Within `s`, the component of `x` is closed under steps. -/
theorem mem_compIn_of_adjIn {s : Finset V} {x a b : V} (ha : a ∈ compIn G s x)
    (hab : AdjIn G s a b) : b ∈ compIn G s x :=
  mem_compIn.mpr ⟨hab.2.1, (mem_compIn.mp ha).2.tail hab⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Within `s`, the component of `x` is closed under chains. -/
theorem mem_compIn_of_reachIn {s : Finset V} {x a b : V} (ha : a ∈ compIn G s x)
    (hab : ReachIn G s a b) : b ∈ compIn G s x := by
  induction hab with
  | refl => exact ha
  | tail _ hcd ih => exact mem_compIn_of_adjIn ih hcd

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The component of `x` in `s` is connected. -/
theorem connectedIn_compIn (s : Finset V) (x : V) : ConnectedIn G (compIn G s x) := by
  -- every chain inside `s` starting in the component stays in the component
  have key : ∀ a ∈ compIn G s x, ∀ b, ReachIn G s a b → ReachIn G (compIn G s x) a b := by
    intro a ha b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail hac hcd ih =>
      have hc : _ ∈ compIn G s x := mem_compIn_of_reachIn ha hac
      exact ih.tail ⟨hc, mem_compIn_of_adjIn hc hcd, hcd.2.2⟩
  intro a ha b hb
  exact key a ha b (((mem_compIn.mp ha).2.symm).trans (mem_compIn.mp hb).2)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- If the components of `x` and `y` in `s` meet, then `y` lies in the component of `x`. -/
theorem mem_compIn_of_inter {s : Finset V} {x y z : V} (hx : z ∈ compIn G s x)
    (hy : z ∈ compIn G s y) (hys : y ∈ s) : y ∈ compIn G s x :=
  mem_compIn.mpr ⟨hys, (mem_compIn.mp hx).2.trans (mem_compIn.mp hy).2.symm⟩

/-! ### Branches at a vertex -/

omit [DecidableEq V] in
theorem mem_nbrsIn {s : Finset V} {r w : V} : w ∈ nbrsIn G s r ↔ w ∈ s ∧ G.Adj r w := by
  simp only [nbrsIn, Finset.mem_filter]

/-- The base vertex of a branch lies in it. -/
theorem self_mem_branch {s : Finset V} {r w : V} (hw : w ∈ nbrsIn G s r) :
    w ∈ compIn G (s.erase r) w := by
  rw [mem_nbrsIn] at hw
  exact self_mem_compIn (Finset.mem_erase.mpr ⟨(G.ne_of_adj hw.2).symm, hw.1⟩)

omit [DecidableRel G.Adj] in
/-- In an acyclic graph, the only neighbour of `r` in the branch of `w` is `w`. -/
theorem eq_of_mem_branch_of_adj (hG : G.IsAcyclic) {s : Finset V} {r w y : V}
    (hrw : G.Adj r w) (hy : y ∈ compIn G (s.erase r) w) (hry : G.Adj r y) : y = w := by
  obtain ⟨hys, hwy⟩ := mem_compIn.mp hy
  obtain ⟨q, hq⟩ := hwy.exists_walk hys
  exact IsAcyclic.eq_of_adj_of_walk hG hry hrw q (fun h => by simpa using hq r h)

/-- Distinct neighbours have disjoint branches. -/
theorem disjoint_branches (hG : G.IsAcyclic) {s : Finset V} {r w w' : V}
    (hw : w ∈ nbrsIn G s r) (hw' : w' ∈ nbrsIn G s r) (hne : w ≠ w') :
    Disjoint (compIn G (s.erase r) w) (compIn G (s.erase r) w') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  have h1 : w' ∈ compIn G (s.erase r) w :=
    mem_compIn_of_inter hz hz' (compIn_subset _ _ (self_mem_branch hw'))
  exact hne (eq_of_mem_branch_of_adj hG (mem_nbrsIn.mp hw).2 h1 (mem_nbrsIn.mp hw').2).symm

/-- There are no edges between distinct branches. -/
theorem not_adj_branches (hG : G.IsAcyclic) {s : Finset V} {r w w' : V}
    (hw : w ∈ nbrsIn G s r) (hw' : w' ∈ nbrsIn G s r) (hne : w ≠ w')
    {a b : V} (ha : a ∈ compIn G (s.erase r) w) (hb : b ∈ compIn G (s.erase r) w') :
    ¬ G.Adj a b := by
  intro hab
  have hb' : b ∈ compIn G (s.erase r) w :=
    mem_compIn_of_adjIn ha ⟨compIn_subset _ _ ha, compIn_subset _ _ hb, hab⟩
  exact Finset.disjoint_left.mp (disjoint_branches hG hw hw' hne) hb' hb

/-- The branches cover `s - r`. -/
theorem exists_branch {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) {y : V}
    (hy : y ∈ s.erase r) : ∃ w ∈ nbrsIn G s r, y ∈ compIn G (s.erase r) w := by
  have key : ∀ z, ReachIn G s r z → z = r ∨ ∃ w ∈ nbrsIn G s r, z ∈ compIn G (s.erase r) w := by
    intro z hz
    induction hz with
    | refl => exact Or.inl rfl
    | @tail c d _ hcd ih =>
      by_cases hdr : d = r
      · exact Or.inl hdr
      right
      have hd : d ∈ s.erase r := Finset.mem_erase.mpr ⟨hdr, hcd.2.1⟩
      rcases ih with hc | ⟨w, hw, hc⟩
      · rw [hc] at hcd
        exact ⟨d, mem_nbrsIn.mpr ⟨hcd.2.1, hcd.2.2⟩, self_mem_compIn hd⟩
      · exact ⟨w, hw, mem_compIn_of_adjIn hc ⟨compIn_subset _ _ hc, hd, hcd.2.2⟩⟩
  rcases key y (hs r hr y (Finset.mem_of_mem_erase hy)) with h | h
  · exact absurd h (Finset.ne_of_mem_erase hy)
  · exact h

/-- `s - r` is the union of the branches. -/
theorem erase_eq_biUnion {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    s.erase r = (nbrsIn G s r).biUnion (fun w => compIn G (s.erase r) w) := by
  ext y
  rw [Finset.mem_biUnion]
  constructor
  · exact exists_branch hs hr
  · rintro ⟨w, _, hy⟩
    exact compIn_subset _ _ hy

/-- `s - N[r]` is the union of the branches with their base vertices removed. -/
theorem outsideClosedNbhd_eq_biUnion (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    outsideClosedNbhd G s r =
      (nbrsIn G s r).biUnion (fun w => (compIn G (s.erase r) w).erase w) := by
  ext y
  simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨hys, hyr, hry⟩
    obtain ⟨w, hw, hyw⟩ := exists_branch hs hr (Finset.mem_erase.mpr ⟨hyr, hys⟩)
    refine ⟨w, hw, ?_, hyw⟩
    rintro rfl
    exact hry (mem_nbrsIn.mp hw).2
  · rintro ⟨w, hw, hyw, hy⟩
    have hy' := compIn_subset _ _ hy
    rw [Finset.mem_erase] at hy'
    exact ⟨hy'.2, hy'.1, fun hry => hyw (eq_of_mem_branch_of_adj hG (mem_nbrsIn.mp hw).2 hy hry)⟩

/-- Multiplicativity over a finite family of pairwise disjoint parts with no edges between
distinct parts. -/
theorem indepPoly_biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (f i) (f j))
    (hno : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, ¬ G.Adj a b) :
    indepPoly G (I.biUnion f) = ∏ i ∈ I, indepPoly G (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [indepPoly_empty]
  | insert i I hiI ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert hiI]
    rw [indepPoly_union G ?_ ?_, ih ?_ ?_]
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

/-- The polynomial of `s - r` is the product over the branches (helper form). -/
theorem indepPoly_erase_root_aux (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    indepPoly G (s.erase r) = ∏ w ∈ nbrsIn G s r, indepPoly G (compIn G (s.erase r) w) := by
  conv_lhs => rw [erase_eq_biUnion hs hr]
  exact indepPoly_biUnion _ _ (fun i hi j hj hij => disjoint_branches hG hi hj hij)
    (fun i hi j hj hij a ha b hb => not_adj_branches hG hi hj hij ha hb)

/-- **Rooted decomposition.**  For a connected vertex set `s` of an acyclic graph and `r ∈ s`,
`I(s) = ∏_w I(C_w) + x ∏_w I(C_w - w)`, the products over the neighbours `w` of `r` in `s`,
with `C_w` the component of `w` in `s - r`. -/
theorem indepPoly_rooted_decomposition (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    indepPoly G s =
      (∏ w ∈ nbrsIn G s r, indepPoly G (compIn G (s.erase r) w)) +
        X * ∏ w ∈ nbrsIn G s r, indepPoly G ((compIn G (s.erase r) w).erase w) := by
  rw [indepPoly_erase_add G hr, indepPoly_erase_root_aux hG hs hr,
    outsideClosedNbhd_eq_biUnion hG hs hr, indepPoly_biUnion]
  · intro i hi j hj hij
    exact (disjoint_branches hG hi hj hij).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  · intro i hi j hj hij a ha b hb
    exact not_adj_branches hG hi hj hij (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb)

/-- The polynomial of `s - r` is the product over the branches. -/
theorem indepPoly_erase_root (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    indepPoly G (s.erase r) = ∏ w ∈ nbrsIn G s r, indepPoly G (compIn G (s.erase r) w) :=
  indepPoly_erase_root_aux hG hs hr

-- The statement keeps `hG` and `hs` (unused by the proof); silence the linter rather than change
-- the statement.
set_option linter.unusedVariables false in
/-- Each branch is connected, contains `w`, and is strictly smaller than `s`. -/
theorem compIn_branch (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s) {r w : V}
    (hr : r ∈ s) (hw : w ∈ nbrsIn G s r) :
    ConnectedIn G (compIn G (s.erase r) w) ∧ w ∈ compIn G (s.erase r) w ∧
      (compIn G (s.erase r) w).card < s.card := by
  refine ⟨connectedIn_compIn _ _, self_mem_branch hw, ?_⟩
  calc (compIn G (s.erase r) w).card ≤ (s.erase r).card :=
        Finset.card_le_card (compIn_subset _ _)
    _ < s.card := Finset.card_erase_lt_of_mem hr

/-- The branch sizes add up to `|s| - 1`. -/
theorem sum_card_branches (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s) {r : V}
    (hr : r ∈ s) :
    ∑ w ∈ nbrsIn G s r, (compIn G (s.erase r) w).card + 1 = s.card := by
  have hdisj : (↑(nbrsIn G s r) : Set V).PairwiseDisjoint (fun w => compIn G (s.erase r) w) :=
    fun i hi j hj hij => disjoint_branches hG hi hj hij
  rw [← Finset.card_biUnion hdisj, ← erase_eq_biUnion hs hr, Finset.card_erase_add_one hr]

/-- **Every rooted tree inside a forest gives a rooted pair.** -/
theorem rootedPair_of_connectedIn (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    RootedPair s.card (indepPoly G s) (indepPoly G (s.erase r)) := by
  induction s using Finset.strongInduction generalizing r with
  | H s ih =>
    let f : V → ℕ × ℤ[X] × ℤ[X] := fun w =>
      ((compIn G (s.erase r) w).card, indepPoly G (compIn G (s.erase r) w),
        indepPoly G ((compIn G (s.erase r) w).erase w))
    have hb : ∀ b ∈ (nbrsIn G s r).toList.map f, RootedPair b.1 b.2.1 b.2.2 := by
      intro b hb
      rw [List.mem_map] at hb
      obtain ⟨w, hw, rfl⟩ := hb
      rw [Finset.mem_toList] at hw
      obtain ⟨hC, hwC, _⟩ := compIn_branch hG hs hr hw
      have hsub : compIn G (s.erase r) w ⊂ s :=
        (compIn_subset _ _).trans_ssubset (Finset.erase_ssubset hr)
      exact ih _ hsub hC hwC
    have key := RootedPair.node ((nbrsIn G s r).toList.map f) hb
    have h1 : (((nbrsIn G s r).toList.map f).map (·.1)).sum =
        ∑ w ∈ nbrsIn G s r, (compIn G (s.erase r) w).card := by
      rw [List.map_map]
      exact Finset.sum_map_toList _ _
    have h2 : (((nbrsIn G s r).toList.map f).map (·.2.1)).prod =
        ∏ w ∈ nbrsIn G s r, indepPoly G (compIn G (s.erase r) w) := by
      rw [List.map_map]
      exact Finset.prod_map_toList _ _
    have h3 : (((nbrsIn G s r).toList.map f).map (·.2.2)).prod =
        ∏ w ∈ nbrsIn G s r, indepPoly G ((compIn G (s.erase r) w).erase w) := by
      rw [List.map_map]
      exact Finset.prod_map_toList _ _
    rw [h1, h2, h3, sum_card_branches hG hs hr, ← indepPoly_rooted_decomposition hG hs hr,
      ← indepPoly_erase_root hG hs hr] at key
    exact key

/-! ### Centroids -/

/-- Inside `s - w`, a step never leaves or enters the branch of `w` at `c`. -/
theorem mem_branch_of_adj_of_mem (hG : G.IsAcyclic) {s : Finset V} {c w a b : V}
    (hw : w ∈ nbrsIn G s c) (ha : a ∈ compIn G (s.erase c) w) (hb : b ∈ s.erase w)
    (hab : G.Adj a b) (haw : a ≠ w) : b ∈ compIn G (s.erase c) w := by
  by_cases hbc : b = c
  · rw [hbc] at hab
    exact absurd (eq_of_mem_branch_of_adj hG (mem_nbrsIn.mp hw).2 ha hab.symm) haw
  · exact mem_compIn_of_adjIn ha
      ⟨compIn_subset _ _ ha, Finset.mem_erase.mpr ⟨hbc, Finset.mem_of_mem_erase hb⟩, hab⟩

/-- A chain inside `s - w` stays inside, or stays outside, the branch of `w` at `c`. -/
theorem mem_branch_iff_of_reachIn (hG : G.IsAcyclic) {s : Finset V} {c w a b : V}
    (hw : w ∈ nbrsIn G s c) (hab : ReachIn G (s.erase w) a b) :
    a ∈ compIn G (s.erase c) w ↔ b ∈ compIn G (s.erase c) w := by
  induction hab with
  | refl => exact Iff.rfl
  | @tail x y _ hxy ih =>
    rw [ih]
    constructor
    · intro hx
      exact mem_branch_of_adj_of_mem hG hw hx hxy.2.1 hxy.2.2 (Finset.ne_of_mem_erase hxy.1)
    · intro hy
      exact mem_branch_of_adj_of_mem hG hw hy hxy.1 hxy.2.2.symm (Finset.ne_of_mem_erase hxy.2.1)

/-- If the branch `C` of `w` at `c` is large, then every branch at `w` is smaller than `C`. -/
theorem card_branch_lt (hG : G.IsAcyclic) {s : Finset V} {c w u : V}
    (hw : w ∈ nbrsIn G s c) (hbig : s.card < 2 * (compIn G (s.erase c) w).card)
    (hu : u ∈ nbrsIn G s w) :
    (compIn G (s.erase w) u).card < (compIn G (s.erase c) w).card := by
  set C := compIn G (s.erase c) w
  have hwC : w ∈ C := self_mem_branch hw
  by_cases huc : u = c
  · -- the branch of `w` containing `c` misses `C`
    rw [huc]
    have hcC : c ∉ C := fun h => by simpa using compIn_subset _ _ h
    have hsub : compIn G (s.erase w) c ⊆ s \ C := by
      intro z hz
      obtain ⟨hzs, hcz⟩ := mem_compIn.mp hz
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_of_mem_erase hzs,
        fun hzC => hcC ((mem_branch_iff_of_reachIn hG hw hcz).mpr hzC)⟩
    have h1 : (compIn G (s.erase w) c).card ≤ (s \ C).card := Finset.card_le_card hsub
    have h2 : (s \ C).card + C.card = s.card := Finset.card_sdiff_add_card_eq_card
      ((compIn_subset (G := G) (s.erase c) w).trans (Finset.erase_subset c s))
    omega
  · -- every other branch at `w` lies inside `C - w`
    have hus : u ∈ s := (mem_nbrsIn.mp hu).1
    have huC : u ∈ C := mem_compIn_of_adjIn hwC
      ⟨compIn_subset _ _ hwC, Finset.mem_erase.mpr ⟨huc, hus⟩, (mem_nbrsIn.mp hu).2⟩
    have hsub : compIn G (s.erase w) u ⊆ C.erase w := by
      intro z hz
      obtain ⟨hzs, huz⟩ := mem_compIn.mp hz
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hzs,
        (mem_branch_iff_of_reachIn hG hw huz).mp huC⟩
    exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hwC)

-- Connectedness is not needed by the proof: a vertex minimizing the largest branch is a centroid.
set_option linter.unusedVariables false in
/-- **Jordan's centroid theorem**: a nonempty connected vertex set of an acyclic graph has a
vertex all of whose branches have at most half the vertices. -/
theorem exists_centroid (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s)
    (hne : s.Nonempty) :
    ∃ c ∈ s, ∀ w ∈ nbrsIn G s c, 2 * (compIn G (s.erase c) w).card ≤ s.card := by
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image s
    (fun c => (nbrsIn G s c).sup (fun w => (compIn G (s.erase c) w).card)) hne
  refine ⟨c, hc, fun w hw => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hws : w ∈ s := (mem_nbrsIn.mp hw).1
  have hpos : (⊥ : ℕ) < (compIn G (s.erase c) w).card :=
    Finset.card_pos.mpr ⟨w, self_mem_branch hw⟩
  have h1 : (nbrsIn G s w).sup (fun u => (compIn G (s.erase w) u).card) <
      (compIn G (s.erase c) w).card :=
    (Finset.sup_lt_iff hpos).mpr fun u hu => card_branch_lt hG hw hlt hu
  have h2 : (compIn G (s.erase c) w).card ≤
      (nbrsIn G s c).sup (fun w => (compIn G (s.erase c) w).card) :=
    Finset.le_sup (f := fun w => (compIn G (s.erase c) w).card) hw
  have h3 := hmin w hws
  try simp only at h3
  omega

/-- The vertex set of a connected component of `G` is connected in the above sense. -/
theorem connectedIn_reachable_set [Fintype V] (x : V) :
    ConnectedIn G (Finset.univ.filter (G.Reachable x)) := by
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  obtain ⟨p⟩ := (ha.2.symm.trans hb.2 : G.Reachable a b)
  apply reachIn_of_walk p
  intro v hv
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ v, ha.2.trans ⟨p.takeUntil v hv⟩⟩

end Erdos993Lean
