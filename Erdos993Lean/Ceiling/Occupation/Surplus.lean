module

public import Mathlib
public import Erdos993Lean.Ceiling.Occupation.Partition
public import Erdos993Lean.Ceiling.Occupation.Matching
public import Erdos993Lean.Ceiling.Occupation.Components

/-!
# B5, part 5: the target, the surplus, and a vertex with pendant leaves

`target G s = |s|/2 - ν(s)/3 + cc(s)/7` (that is `W + cc/7`, with `W = n/2 - ν/3`) and
`surplus G s = S(s) - T(s) Z(s)`.  B5 on the vertex sets of a fixed forest is `surplus ≥ 0`
(`Occupation/Main.lean`); this file supplies the pieces of the induction step of the ceiling proof,
Appendix R3:

* `surplus_isolated`: deleting an isolated vertex, `Φ(s) = (10/3) Φ(s - x) + (4/21) Z(s - x)`
  (the isolate surplus `2/35` of the paper, `7/10 - 1/2 - 1/7`);
* a vertex `v` with leaf neighbours `Λ = leavesAt G s v` (`t = |Λ|`) and other neighbours
  `U = stemsAt G s v`, `H = s - v - Λ = residualAt G s v`, `J = H - U = s - N[v]`:
  `Z(s) = b^t Z(H) + λ Z(J)` (`Zq_leafStem`) and the formula for `S` (`Sq_leafStem`) (the exact
  root partition (R2) of the paper), `|s| = |H| + t + 1`, `ν(s) = ν(H) + 1` ("matching `v` to a
  leaf", `nuIn_leafStem`), `cc(s) + |U| = cc(H) + 1` (`ccIn_leafStem`).
-/

@[expose] public section

namespace Erdos993Lean
namespace Occupation

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The target `T(s) = |s|/2 - ν(s)/3 + cc(s)/7`. -/
noncomputable def target (s : Finset V) : ℚ :=
  (s.card : ℚ) / 2 - (nuIn G s : ℚ) / 3 + (ccIn G s : ℚ) / 7

/-- The surplus `Φ(s) = S(s) - T(s) Z(s)`; B5 is `Φ ≥ 0`. -/
noncomputable def surplus (s : Finset V) : ℚ := Sq G s - target G s * Zq G s

/-- The empty set has surplus `0`. -/
theorem surplus_empty : surplus G (∅ : Finset V) = 0 := by
  simp [surplus, target, Sq_empty, Zq_empty, nuIn_eq_zero_of_edgeless (G := G)
    (r := (∅ : Finset V)) (by simp), ccIn_empty]

variable {G}

/-- Deleting an isolated vertex: `Φ(s) = (10/3) Φ(s - x) + (4/21) Z(s - x)`. -/
theorem surplus_isolated (hG : G.IsAcyclic) {s : Finset V} {x : V} (hx : x ∈ s)
    (hxn : nbrsIn G s x = ∅) :
    surplus G s = 10 / 3 * surplus G (s.erase x) + 4 / 21 * Zq G (s.erase x) := by
  have hZ := Zq_isolated G hx hxn
  have hS := Sq_isolated G hx hxn
  have hnu := nuIn_isolated (G := G) hx hxn
  have hcc := ccIn_erase hG hx
  rw [hxn, Finset.card_empty, add_zero] at hcc
  have hcard := Finset.card_erase_add_one hx
  unfold surplus target
  rw [hZ, hS, hnu]
  have hcc' : (ccIn G s : ℚ) = ccIn G (s.erase x) + 1 := by exact_mod_cast hcc.symm
  have hcard' : (s.card : ℚ) = (s.erase x).card + 1 := by exact_mod_cast hcard.symm
  rw [hcc', hcard']
  ring

/-! ### A vertex with pendant leaves -/

variable (G) in
/-- The leaves of `G[s]` adjacent to `v` (vertices whose only neighbour in `s` is `v`). -/
def leavesAt (s : Finset V) (v : V) : Finset V :=
  (nbrsIn G s v).filter (fun ℓ => nbrsIn G s ℓ = {v})

variable (G) in
/-- The other neighbours of `v` in `s`. -/
def stemsAt (s : Finset V) (v : V) : Finset V :=
  (nbrsIn G s v).filter (fun ℓ => nbrsIn G s ℓ ≠ {v})

variable (G) in
/-- `s` minus `v` and its leaves. -/
def residualAt (s : Finset V) (v : V) : Finset V := (s.erase v) \ leavesAt G s v

omit [DecidableEq V] in
variable (G) in
theorem self_notMem_nbrsIn (s : Finset V) (v : V) : v ∉ nbrsIn G s v := fun h =>
  G.irrefl (mem_nbrsIn.mp h).2

variable (G) in
theorem nbrsIn_subset_erase (s : Finset V) (v : V) : nbrsIn G s v ⊆ s.erase v := fun _ hw =>
  Finset.mem_erase.mpr ⟨fun h => self_notMem_nbrsIn G s v (h ▸ hw), (mem_nbrsIn.mp hw).1⟩

variable (G) in
theorem leavesAt_subset (s : Finset V) (v : V) : leavesAt G s v ⊆ s.erase v :=
  (Finset.filter_subset _ _).trans (nbrsIn_subset_erase G s v)

theorem mem_leavesAt {s : Finset V} {v ℓ : V} :
    ℓ ∈ leavesAt G s v ↔ ℓ ∈ nbrsIn G s v ∧ nbrsIn G s ℓ = {v} := by
  simp only [leavesAt, Finset.mem_filter]

theorem mem_stemsAt {s : Finset V} {v u : V} :
    u ∈ stemsAt G s v ↔ u ∈ nbrsIn G s v ∧ nbrsIn G s u ≠ {v} := by
  simp only [stemsAt, Finset.mem_filter]

/-- A neighbour of a leaf at `v` is `v`. -/
theorem eq_of_adj_leaf {s : Finset V} {v ℓ w : V} (hℓ : ℓ ∈ leavesAt G s v) (hw : w ∈ s)
    (hadj : G.Adj ℓ w) : w = v := by
  have h : w ∈ nbrsIn G s ℓ := mem_nbrsIn.mpr ⟨hw, hadj⟩
  rw [(mem_leavesAt.mp hℓ).2, Finset.mem_singleton] at h
  exact h

theorem leavesAt_edgeless {s : Finset V} {v : V} :
    ∀ a ∈ leavesAt G s v, ∀ b ∈ leavesAt G s v, ¬ G.Adj a b := by
  intro a ha b hb hab
  have hbs : b ∈ s := Finset.mem_of_mem_erase (leavesAt_subset G s v hb)
  have := eq_of_adj_leaf ha hbs hab
  exact (Finset.mem_erase.mp (leavesAt_subset G s v hb)).1 this

theorem residualAt_noAdj {s : Finset V} {v : V} :
    ∀ a ∈ residualAt G s v, ∀ b ∈ leavesAt G s v, ¬ G.Adj a b := by
  intro a ha b hb hab
  have has : a ∈ s.erase v := (Finset.mem_sdiff.mp ha).1
  have := eq_of_adj_leaf hb (Finset.mem_of_mem_erase has) hab.symm
  exact (Finset.mem_erase.mp has).1 this

variable (G) in
theorem erase_eq_residualAt_union (s : Finset V) (v : V) :
    s.erase v = residualAt G s v ∪ leavesAt G s v :=
  (Finset.sdiff_union_of_subset (leavesAt_subset G s v)).symm

variable (G) in
theorem disjoint_residualAt_leavesAt (s : Finset V) (v : V) :
    Disjoint (residualAt G s v) (leavesAt G s v) := Finset.sdiff_disjoint

variable (G) in
theorem nbrsIn_eq_union (s : Finset V) (v : V) :
    nbrsIn G s v = leavesAt G s v ∪ stemsAt G s v :=
  (Finset.filter_union_filter_not_eq _ _).symm

variable (G) in
theorem outsideClosedNbhd_eq_residualAt_sdiff (s : Finset V) (v : V) :
    outsideClosedNbhd G s v = residualAt G s v \ stemsAt G s v := by
  rw [outsideClosedNbhd_eq, nbrsIn_eq_union G, residualAt]
  ext w
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

variable (G) in
theorem card_eq_residualAt {s : Finset V} {v : V} (hv : v ∈ s) :
    s.card = (residualAt G s v).card + (leavesAt G s v).card + 1 := by
  rw [← Finset.card_erase_add_one hv, erase_eq_residualAt_union G s v,
    Finset.card_union_of_disjoint (disjoint_residualAt_leavesAt G s v)]

/-- The root partition at `v`: `Z(s) = (10/3)^t Z(H) + (7/3) Z(J)`. -/
theorem Zq_leafStem {s : Finset V} {v : V} (hv : v ∈ s) :
    Zq G s = (10 / 3) ^ (leavesAt G s v).card * Zq G (residualAt G s v) +
      7 / 3 * Zq G (residualAt G s v \ stemsAt G s v) := by
  rw [Zq_erase G hv, outsideClosedNbhd_eq_residualAt_sdiff G, erase_eq_residualAt_union G,
    Zq_union G (disjoint_residualAt_leavesAt G s v) residualAt_noAdj,
    (Zq_Sq_edgeless G leavesAt_edgeless).1]
  ring

theorem Sq_leafStem {s : Finset V} {v : V} (hv : v ∈ s) :
    Sq G s = (10 / 3) ^ (leavesAt G s v).card * Sq G (residualAt G s v) +
      7 / 10 * (leavesAt G s v).card * (10 / 3) ^ (leavesAt G s v).card *
        Zq G (residualAt G s v) +
      7 / 3 * (Zq G (residualAt G s v \ stemsAt G s v) +
        Sq G (residualAt G s v \ stemsAt G s v)) := by
  rw [Sq_erase G hv, outsideClosedNbhd_eq_residualAt_sdiff G, erase_eq_residualAt_union G,
    Sq_union G (disjoint_residualAt_leavesAt G s v) residualAt_noAdj,
    (Zq_Sq_edgeless G leavesAt_edgeless).1, (Zq_Sq_edgeless G leavesAt_edgeless).2]
  ring

/-- Matching a leaf to `v`: `ν(s) = ν(H) + 1`. -/
theorem nuIn_leafStem {s : Finset V} {v ℓ : V} (hℓ : ℓ ∈ leavesAt G s v) :
    nuIn G s = nuIn G (residualAt G s v) + 1 := by
  obtain ⟨hℓv, hℓn⟩ := mem_leavesAt.mp hℓ
  have hℓs : ℓ ∈ s := (mem_nbrsIn.mp hℓv).1
  rw [nuIn_pendant hℓs hℓn]
  have hvs : v ∈ nbrsIn G s ℓ := by rw [hℓn]; exact Finset.mem_singleton_self v
  have hv : v ∈ s.erase ℓ := Finset.mem_erase.mpr ⟨fun h => by
    subst h; exact self_notMem_nbrsIn G s _ hℓv, (mem_nbrsIn.mp hvs).1⟩
  have heq : (s.erase ℓ).erase v = residualAt G s v ∪ (leavesAt G s v).erase ℓ := by
    rw [Finset.erase_right_comm, erase_eq_residualAt_union G s v, Finset.erase_union_distrib,
      Finset.erase_eq_of_notMem]
    exact Finset.disjoint_right.mp (disjoint_residualAt_leavesAt G s v) hℓ
  rw [heq, nuIn_union (G := G)
    ((disjoint_residualAt_leavesAt G s v).mono_right (Finset.erase_subset _ _))
    (fun a ha b hb => residualAt_noAdj a ha b (Finset.mem_of_mem_erase hb)),
    nuIn_eq_zero_of_edgeless (G := G) (fun a ha b hb =>
      leavesAt_edgeless a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)), add_zero]

/-- Components: `cc(s) + |U| = cc(H) + 1`. -/
theorem ccIn_leafStem (hG : G.IsAcyclic) {s : Finset V} {v : V} (hv : v ∈ s) :
    ccIn G s + (stemsAt G s v).card = ccIn G (residualAt G s v) + 1 := by
  have h1 := ccIn_erase hG hv
  rw [erase_eq_residualAt_union G s v,
    ccIn_union (disjoint_residualAt_leavesAt G s v) residualAt_noAdj,
    ccIn_edgeless (G := G) (r := leavesAt G s v) leavesAt_edgeless, nbrsIn_eq_union G s v,
    Finset.card_union_of_disjoint (by
      unfold leavesAt stemsAt
      exact Finset.disjoint_filter_filter_not _ _ _)] at h1
  omega

end Occupation
end Erdos993Lean
