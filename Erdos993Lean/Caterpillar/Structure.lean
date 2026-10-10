module

public import Mathlib
public import Erdos993Lean.Caterpillar.Build

/-!
# From a dominating path to a construction by the letters S and L

Let `G` be acyclic and `p` a path in `G`.  The vertices on `p` together with the vertices adjacent
to `p` form the set `walkNbhd p`.  We show `Build G (walkNbhd p) u`, where `u` is the start of
`p`: walking along `p` from its far end, each new path vertex is an `S` step and each pendant
vertex is an `L` step.

The graph input is acyclicity only, used through three consequences for a path `P`:
* a vertex off `P` is adjacent to at most one vertex of `P`;
* two adjacent vertices off `P` are not both adjacent to `P`;
* a path vertex is adjacent to no later path vertex except its successor.
-/

@[expose] public section

namespace Erdos993Lean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The vertices on the walk `p` or adjacent to a vertex of `p`. -/
def walkNbhd {u v : V} (p : G.Walk u v) : Finset V :=
  Finset.univ.filter (fun x => x ∈ p.support ∨ ∃ y ∈ p.support, G.Adj x y)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In an acyclic graph, an edge lies on every walk between its endpoints. -/
theorem IsAcyclic.edge_mem_edges (hG : G.IsAcyclic) {x y : V} (hxy : G.Adj x y)
    (q : G.Walk x y) : s(x, y) ∈ q.edges :=
  (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG hxy)) q

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In an acyclic graph, if `x` is adjacent to `y` and to `z`, and some walk from `z` to `y`
avoids `x`, then `y = z`. -/
theorem IsAcyclic.eq_of_adj_of_walk (hG : G.IsAcyclic) {x y z : V} (hxy : G.Adj x y)
    (hxz : G.Adj x z) (q : G.Walk z y) (hx : x ∉ q.support) : y = z := by
  have h := IsAcyclic.edge_mem_edges hG hxy (SimpleGraph.Walk.cons hxz q)
  rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at h
  rcases h with h | h
  · rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hxz.ne
  · exact absurd (SimpleGraph.Walk.fst_mem_support_of_mem_edges q h) hx

omit [Fintype V] [DecidableRel G.Adj] in
/-- A walk between two vertices of a walk `p`, all of whose vertices lie on `p`. -/
theorem exists_walk_support_subset {u v : V} (p : G.Walk u v) {y z : V} (hy : y ∈ p.support)
    (hz : z ∈ p.support) : ∃ q : G.Walk z y, ∀ w ∈ q.support, w ∈ p.support := by
  refine ⟨(p.takeUntil z hz).reverse.append (p.takeUntil y hy), fun w hw => ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse] at hw
  rcases hw with hw | hw
  · exact p.support_takeUntil_subset hz hw
  · exact p.support_takeUntil_subset hy hw

omit [Fintype V] [DecidableRel G.Adj] in
/-- In an acyclic graph, a vertex off a walk is adjacent to at most one vertex of the walk. -/
theorem IsAcyclic.offPath_adj_unique (hG : G.IsAcyclic) {u v : V} (p : G.Walk u v)
    {x y z : V} (hx : x ∉ p.support) (hy : y ∈ p.support) (hz : z ∈ p.support)
    (hxy : G.Adj x y) (hxz : G.Adj x z) : y = z := by
  obtain ⟨q, hq⟩ := exists_walk_support_subset p hy hz
  exact IsAcyclic.eq_of_adj_of_walk hG hxy hxz q (fun h => hx (hq x h))

omit [Fintype V] [DecidableRel G.Adj] in
/-- In an acyclic graph, two adjacent vertices off a walk are not both adjacent to the walk. -/
theorem IsAcyclic.offPath_adj_false (hG : G.IsAcyclic) {u v : V} (p : G.Walk u v)
    {x y z z' : V} (hx : x ∉ p.support) (hy : y ∉ p.support)
    (hxy : G.Adj x y) (hz : z ∈ p.support) (hz' : z' ∈ p.support)
    (hxz : G.Adj x z) (hyz' : G.Adj y z') : False := by
  obtain ⟨q, hq⟩ := exists_walk_support_subset p hz' hz
  have key := IsAcyclic.eq_of_adj_of_walk hG hxy hxz (q.concat hyz'.symm) (by
    intro h
    rw [SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at h
    rcases h with h | h
    · exact hx (hq x h)
    · exact hxy.ne h)
  exact hy (key ▸ hz)

/-- The vertices off `B` adjacent to `a`. -/
def leavesAt (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) (a : V) : Finset V :=
  Finset.univ.filter (fun x => x ∉ B ∧ G.Adj x a)

/-- The vertices of the walk `q`, together with the vertices off `B` adjacent to `q`. -/
def nbhdOut (B : Finset V) {a b : V} (q : G.Walk a b) : Finset V :=
  Finset.univ.filter (fun x => x ∈ q.support ∨ (x ∉ B ∧ ∃ y ∈ q.support, G.Adj x y))

omit [Fintype V] [DecidableRel G.Adj] in
/-- Adding a set of pairwise non-adjacent leaves at the root, one `L` step at a time. -/
theorem Build.union_leaves {s : Finset V} {r : V} (hs : Build G s r) (T : Finset V)
    (hrT : r ∉ T) (hsT : ∀ x ∈ T, x ∉ s) (hadj : ∀ x ∈ T, ∀ w ∈ s, G.Adj x w ↔ w = r)
    (hTT : ∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y) : Build G (s ∪ T) r := by
  induction T using Finset.induction_on with
  | empty => simpa using hs
  | insert x T hxT ih =>
    rw [Finset.union_insert]
    refine Build.L (ih ?_ ?_ ?_ ?_) ?_ ?_
    · exact fun h => hrT (Finset.mem_insert_of_mem h)
    · exact fun y hy => hsT y (Finset.mem_insert_of_mem hy)
    · exact fun y hy => hadj y (Finset.mem_insert_of_mem hy)
    · exact fun y hy z hz => hTT y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    · rw [Finset.mem_union, not_or]
      exact ⟨hsT x (Finset.mem_insert_self x T), hxT⟩
    · intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hadj x (Finset.mem_insert_self x T) w hw
      · constructor
        · intro h
          exact absurd h (hTT x (Finset.mem_insert_self x T) w (Finset.mem_insert_of_mem hw))
        · rintro rfl
          exact absurd (Finset.mem_insert_of_mem hw) hrT

/-- The generalized construction: for a path `q` inside `B`, `nbhdOut B q` is built with root
the start of `q`, provided vertices off `B` see `B` in at most one vertex, and no edge off `B`
has both ends adjacent to `B`. -/
theorem build_nbhdOut (hG : G.IsAcyclic) (B : Finset V)
    (H1 : ∀ x ∉ B, ∀ y ∈ B, ∀ z ∈ B, G.Adj x y → G.Adj x z → y = z)
    (H2 : ∀ x ∉ B, ∀ y ∉ B, G.Adj x y → ∀ z ∈ B, ∀ z' ∈ B, G.Adj x z → G.Adj y z' → False)
    {a b : V} (q : G.Walk a b) (hq : q.IsPath) (hqB : ∀ w ∈ q.support, w ∈ B) :
    Build G (nbhdOut B q) a := by
  induction q with
  | @nil a =>
    have haB : a ∈ B := hqB a (by simp)
    have hset : nbhdOut B (SimpleGraph.Walk.nil : G.Walk a a) = {a} ∪ leavesAt G B a := by
      ext x
      simp [nbhdOut, leavesAt]
    rw [hset]
    refine Build.union_leaves (Build.single a) _ ?_ ?_ ?_ ?_
    · simp [leavesAt, haB]
    · intro x hx
      simp only [leavesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_singleton]
      rintro rfl
      exact hx.1 haB
    · intro x hx w hw
      simp only [leavesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_singleton] at hw
      subst hw
      simp [hx.2]
    · intro x hx y hy hxy
      simp only [leavesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact H2 x hx.1 y hy.1 hxy a haB a haB hx.2 hy.2
  | @cons a w b h q ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hq
    have haB : a ∈ B := hqB a (by simp)
    have hqB' : ∀ v ∈ q.support, v ∈ B := fun v hv => hqB v (by simp [hv])
    have hb := ih hq.1 hqB'
    have hS : Build G (insert a (nbhdOut B q)) a := by
      refine Build.S hb ?_ ?_
      · simp [nbhdOut, haB, hq.2]
      · intro u hu
        simp only [nbhdOut, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        constructor
        · intro hau
          rcases hu with hu | ⟨huB, y, hy, huy⟩
          · exact IsAcyclic.eq_of_adj_of_walk hG hau h (q.takeUntil u hu)
              (fun ha => hq.2 (q.support_takeUntil_subset hu ha))
          · exfalso
            have hya : a = y := H1 u huB a haB y (hqB' y hy) hau.symm huy
            exact hq.2 (hya ▸ hy)
        · rintro rfl
          exact h
    have hset :
        nbhdOut B (SimpleGraph.Walk.cons h q) = insert a (nbhdOut B q) ∪ leavesAt G B a := by
      ext x
      simp only [nbhdOut, leavesAt, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.mem_insert, SimpleGraph.Walk.support_cons, List.mem_cons,
        or_and_right, exists_or, exists_eq_left]
      constructor
      · rintro ((h1 | h1) | ⟨h1, h2 | h2⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr (Or.inl h1))
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inl (Or.inr (Or.inr ⟨h1, h2⟩))
      · rintro ((h1 | h1 | ⟨h1, h2⟩) | ⟨h1, h2⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1)
        · exact Or.inr ⟨h1, Or.inr h2⟩
        · exact Or.inr ⟨h1, Or.inl h2⟩
    rw [hset]
    refine Build.union_leaves hS _ ?_ ?_ ?_ ?_
    · simp [leavesAt, haB]
    · intro x hx
      simp only [leavesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [nbhdOut, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_and, not_exists]
      refine ⟨?_, fun hxq => hx.1 (hqB' x hxq), fun _ y hy hxy => ?_⟩
      · rintro rfl
        exact hx.1 haB
      · have hya : y = a := H1 x hx.1 y (hqB' y hy) a haB hxy hx.2
        exact hq.2 (hya ▸ hy)
    · intro x hx u hu
      simp only [leavesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases Finset.mem_insert.mp hu with rfl | hu
      · simp [hx.2]
      · simp only [nbhdOut, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        constructor
        · intro hxu
          rcases hu with hu | ⟨huB, y, hy, huy⟩
          · exact H1 x hx.1 u (hqB' u hu) a haB hxu hx.2
          · exact (H2 x hx.1 u huB hxu a haB y (hqB' y hy) hx.2 huy).elim
        · rintro rfl
          exact hx.2
    · intro x hx y hy hxy
      simp only [leavesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact H2 x hx.1 y hy.1 hxy a haB a haB hx.2 hy.2

/-- The construction theorem: `walkNbhd p` is built from a single vertex by `S` and `L`, with
root the start of the path. -/
theorem build_walkNbhd (hG : G.IsAcyclic) {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    Build G (walkNbhd p) u := by
  have H1 : ∀ x ∉ p.support.toFinset, ∀ y ∈ p.support.toFinset, ∀ z ∈ p.support.toFinset,
      G.Adj x y → G.Adj x z → y = z := by
    intro x hx y hy z hz hxy hxz
    rw [List.mem_toFinset] at hx hy hz
    exact IsAcyclic.offPath_adj_unique hG p hx hy hz hxy hxz
  have H2 : ∀ x ∉ p.support.toFinset, ∀ y ∉ p.support.toFinset, G.Adj x y →
      ∀ z ∈ p.support.toFinset, ∀ z' ∈ p.support.toFinset, G.Adj x z → G.Adj y z' → False := by
    intro x hx y hy hxy z hz z' hz' hxz hyz'
    rw [List.mem_toFinset] at hx hy hz hz'
    exact IsAcyclic.offPath_adj_false hG p hx hy hxy hz hz' hxz hyz'
  have h := build_nbhdOut hG p.support.toFinset H1 H2 p hp
    (fun w hw => List.mem_toFinset.mpr hw)
  have hset : nbhdOut p.support.toFinset p = walkNbhd p := by
    ext x
    simp only [nbhdOut, walkNbhd, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset]
    tauto
  rwa [hset] at h

end Erdos993Lean
