module

public import Mathlib
public import Erdos993Lean.Analytic.Reserve.Moments
public import Erdos993Lean.Analytic.Reserve.Step

/-!
# O1 by the two-generation reserve: the rooted tree

Sources:
the two-generation reserve proof (rooting, "every unselected vertex has a child", the messages
`p = λ e^{−Y}/(1 + λ e^{−Y})`, `y = −log(1 − p)`, recursion (1)).


A rooted subtree is a connected vertex set `s` of an acyclic graph with a root `r ∈ s` (see
`ConnectedIn`, `nbrsIn`, `compIn`); the children of `r` are `nbrsIn G s r` and the subtree of the
child `w` is the branch `C_w = compIn G (s − r) w`.

* `yLog G t s r = −log(1 − p)`, `p = rootProb G t s r` (the downward message), and
  `Tmass G t s r = ∑_w yLog (C_w, w)` (the children's total log-mass);
* `rootProb_eq_msg`, `yLog_eq_lmass`: `p = msg t T` and `y = lmass t T` with `T = Tmass` (from
  `rootProb_odds`);
* `Good G B s r`: every unselected vertex has a child (the root: a neighbour in `s`; any other
  vertex: at least two neighbours in `s`, its parent and a child); `Good.branch` (it passes to the
  branches), `Good.root_mem` (a childless root is selected);
* `resF G B t A s = A U(s) − V(s)` (the function `F`, and `G = resF (s − r)`), `port G B t s r =
  U(s) − U(s − r)` (the port `u`);
* **`resF_rec`** (the recursion (1)):
  `F(s) = A p a + (1 − p) ∑_w F(C_w) + p ∑_w F(C_w − w) − p (1 − p)(a − ∑_w u_w)²`, and
  **`port_rec`**: `u(s, r) = p (a − ∑_w u_w)`; `resF_erase_root`: `G(s, r) = ∑_w F(C_w)`.

Scalarity check.  `U(s), V(s)` (parent unoccupied) and `U(s − r), V(s − r)` (parent occupied) are the
mean and variance of `K_B` under the two actual boundary laws of the subtree; `p` is the subtree
root's downward message, `y` its log-mass, `T` the sum of the actual children's log-masses; `u` is the
response of the mean of `K_B` to the parent's occupancy.  Producer: the hard-core law of the actual
subtree (`Reserve/Moments.lean`); consumer: the reserve induction (`Reserve/Induction.lean`).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve

open Finset Erdos993Lean.Analytic.Tail

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Log-masses and messages -/

variable (G) in
/-- The log-mass `y = −log(1 − p)` of the downward message `p = rootProb G t s r` of the root. -/
noncomputable def yLog (t : ℝ) (s : Finset V) (r : V) : ℝ := -Real.log (1 - rootProb G t s r)

variable (G) in
/-- The children's total log-mass `T(s, r) = ∑_{w ∈ nbrsIn s r} y(C_w, w)`. -/
noncomputable def Tmass (t : ℝ) (s : Finset V) (r : V) : ℝ :=
  ∑ w ∈ nbrsIn G s r, yLog G t (compIn G (s.erase r) w) w

theorem one_sub_rootProb_eq_exp {t : ℝ} (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    1 - rootProb G t s r = Real.exp (-yLog G t s r) := by
  unfold yLog
  rw [neg_neg, Real.exp_log]
  have := rootProb_lt_one (G := G) ht hr
  linarith

/-- **The downward message is `msg t T`**, `T` the children's total log-mass (from
`rootProb_odds`: `p/(1 − p) = t ∏_w (1 − p_w) = t e^{−T}`). -/
theorem rootProb_eq_msg (hG : G.IsAcyclic) {t : ℝ} (ht : 0 < t) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    rootProb G t s r = msg t (Tmass G t s r) := by
  have hodds := rootProb_odds hG ht hs hr
  have hprod : ∏ w ∈ nbrsIn G s r, (1 - rootProb G t (compIn G (s.erase r) w) w) =
      Real.exp (-Tmass G t s r) := by
    rw [Tmass, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun w hw => ?_
    exact one_sub_rootProb_eq_exp ht.le (compIn_branch hG hs hr hw).2.1
  rw [hprod] at hodds
  have hp1 : 0 < 1 - rootProb G t s r := by
    have := rootProb_lt_one (G := G) ht.le hr
    linarith
  rw [div_eq_iff hp1.ne'] at hodds
  unfold msg
  rw [eq_div_iff (by positivity)]
  linear_combination hodds

/-- **The log-mass is `lmass t T`**, `T` the children's total log-mass. -/
theorem yLog_eq_lmass (hG : G.IsAcyclic) {t : ℝ} (ht : 0 < t) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    yLog G t s r = lmass t (Tmass G t s r) := by
  rw [yLog, rootProb_eq_msg hG ht hs hr, lmass_eq_neg_log ht]

theorem yLog_pos (hG : G.IsAcyclic) {t : ℝ} (ht : 0 < t) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) : 0 < yLog G t s r := by
  rw [yLog_eq_lmass hG ht hs hr]
  exact lmass_pos ht _

theorem Tmass_nonneg (hG : G.IsAcyclic) {t : ℝ} (ht : 0 < t) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) : 0 ≤ Tmass G t s r :=
  Finset.sum_nonneg fun _ hw =>
    (yLog_pos hG ht (compIn_branch hG hs hr hw).1 (compIn_branch hG hs hr hw).2.1).le

/-- A root with a child has positive children's log-mass. -/
theorem Tmass_pos (hG : G.IsAcyclic) {t : ℝ} (ht : 0 < t) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (hne : (nbrsIn G s r).Nonempty) :
    0 < Tmass G t s r :=
  Finset.sum_pos (fun _ hw =>
    yLog_pos hG ht (compIn_branch hG hs hr hw).1 (compIn_branch hG hs hr hw).2.1) hne

/-- The children's log-mass is the sum of the children's `lmass t T_w`. -/
theorem Tmass_eq_sum_lmass (hG : G.IsAcyclic) {t : ℝ} (ht : 0 < t) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    Tmass G t s r = ∑ w ∈ nbrsIn G s r,
      lmass t (Tmass G t (compIn G (s.erase r) w) (w : V)) := by
  unfold Tmass
  refine Finset.sum_congr rfl fun w hw => ?_
  exact yLog_eq_lmass hG ht (compIn_branch hG hs hr hw).1 (compIn_branch hG hs hr hw).2.1

/-! ### Connected vertex sets -/

omit [DecidableEq V] in
/-- In a connected vertex set, a vertex with another vertex of the set has a neighbour in it. -/
theorem nbrsIn_nonempty_of_ne {s : Finset V} (hs : ConnectedIn G s) {r b : V} (hr : r ∈ s)
    (hb : b ∈ s) (hne : r ≠ b) : (nbrsIn G s r).Nonempty := by
  rcases Relation.ReflTransGen.cases_head (hs r hr b hb) with h | ⟨c, hc, _⟩
  · exact absurd h hne
  · exact ⟨c, mem_nbrsIn.mpr ⟨hc.2.1, hc.2.2⟩⟩

omit [DecidableEq V] in
/-- A connected vertex set whose root has no neighbour in it is the root alone. -/
theorem eq_singleton_of_nbrsIn_empty {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s)
    (h : nbrsIn G s r = ∅) : s = {r} := by
  ext y
  rw [Finset.mem_singleton]
  constructor
  · intro hy
    by_contra hne
    obtain ⟨c, hc⟩ := nbrsIn_nonempty_of_ne hs hr hy (Ne.symm hne)
    rw [h] at hc
    exact Finset.notMem_empty c hc
  · rintro rfl
    exact hr

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A connected vertex set meeting a set closed under adjacency lies inside it. -/
theorem subset_of_closed {K : Finset V} (hK : ConnectedIn G K) {v : V} (hv : v ∈ K) {P : Finset V}
    (hvP : v ∈ P) (hP : ∀ y ∈ P, ∀ z, G.Adj y z → z ∈ P) : K ⊆ P := by
  intro y hy
  have h := hK v hv y hy
  clear hy
  induction h with
  | refl => exact hvP
  | tail _ hbc ih => exact hP _ ih _ hbc.2.2

/-! ### The leaf property along the rooted tree -/

variable (G) in
/-- **Every unselected vertex has a child** in the rooted tree `(s, r)`: the root, if unselected,
has a neighbour in `s`; any other unselected vertex has at least two neighbours in `s` (its parent and
a child). -/
def Good (B : Finset V) (s : Finset V) (r : V) : Prop :=
  ∀ v ∈ s, v ∉ B → (v = r → (nbrsIn G s v).Nonempty) ∧ (v ≠ r → 1 < (nbrsIn G s v).card)

/-- A childless root of a good rooted tree is selected. -/
theorem Good.root_mem {B s : Finset V} {r : V} (hgood : Good G B s r) (hr : r ∈ s)
    (h : nbrsIn G s r = ∅) : r ∈ B := by
  by_contra hrB
  obtain ⟨c, hc⟩ := (hgood r hr hrB).1 rfl
  rw [h] at hc
  exact Finset.notMem_empty c hc

/-- **The leaf property passes to the branches**: if `(s, r)` is good, so is `(C_w, w)` for every
child `w`. -/
theorem Good.branch (hG : G.IsAcyclic) {B s : Finset V} {r : V} (hgood : Good G B s r)
    (hr : r ∈ s) {w : V} (hw : w ∈ nbrsIn G s r) : Good G B (compIn G (s.erase r) w) w := by
  have hrw : G.Adj r w := (mem_nbrsIn.mp hw).2
  have hws : w ∈ s := (mem_nbrsIn.mp hw).1
  have hwr : w ≠ r := (G.ne_of_adj hrw).symm
  have hwC : w ∈ compIn G (s.erase r) w := self_mem_branch hw
  intro v hv hvB
  have hvs' : v ∈ s.erase r := compIn_subset _ _ hv
  have hvs : v ∈ s := Finset.mem_of_mem_erase hvs'
  have hvr : v ≠ r := Finset.ne_of_mem_erase hvs'
  refine ⟨fun hvw => ?_, fun hvw => ?_⟩
  · -- the new root `w`: it has a neighbour other than its parent `r`
    rw [hvw] at hvB ⊢
    obtain ⟨x, hx, hxr⟩ := Finset.exists_mem_ne ((hgood w hws hvB).2 hwr) r
    obtain ⟨hxs, hwx⟩ := mem_nbrsIn.mp hx
    refine ⟨x, mem_nbrsIn.mpr ⟨?_, hwx⟩⟩
    exact mem_compIn_of_adjIn hwC
      ⟨Finset.mem_erase.mpr ⟨hwr, hws⟩, Finset.mem_erase.mpr ⟨hxr, hxs⟩, hwx⟩
  · -- any other vertex keeps all its neighbours
    have hsub : nbrsIn G s v ⊆ nbrsIn G (compIn G (s.erase r) w) v := by
      intro x hx
      obtain ⟨hxs, hvx⟩ := mem_nbrsIn.mp hx
      have hxr : x ≠ r := by
        rintro rfl
        exact hvw (eq_of_mem_branch_of_adj hG hrw hv hvx.symm)
      exact mem_nbrsIn.mpr ⟨mem_compIn_of_adjIn hv ⟨hvs', Finset.mem_erase.mpr ⟨hxr, hxs⟩, hvx⟩,
        hvx⟩
    exact lt_of_lt_of_le ((hgood v hvs hvB).2 hvr) (Finset.card_le_card hsub)

/-! ### The reserve functional and the port -/

variable (G) in
/-- The function `F = A U − V` of a vertex set (`G = resF (s − r)` for the rooted subtree `(s, r)`). -/
noncomputable def resF (B : Finset V) (t A : ℝ) (s : Finset V) : ℝ :=
  A * meanB G B t s - varB G B t s

variable (G) in
/-- The port `u(s, r) = U(s) − U(s − r)`: the response of the mean selected count of the subtree to
the occupancy of the parent. -/
noncomputable def port (B : Finset V) (t : ℝ) (s : Finset V) (r : V) : ℝ :=
  meanB G B t s - meanB G B t (s.erase r)

section Rec

variable {B : Finset V} {t A : ℝ}

theorem meanB_erase_root (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    meanB G B t (s.erase r) = ∑ w ∈ nbrsIn G s r, meanB G B t (compIn G (s.erase r) w) := by
  conv_lhs => rw [erase_eq_biUnion hs hr]
  exact meanB_biUnion ht _ _ (fun i hi j hj hij => disjoint_branches hG hi hj hij)
    (fun i hi j hj hij a ha b hb => not_adj_branches hG hi hj hij ha hb)

theorem varB_erase_root (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    varB G B t (s.erase r) = ∑ w ∈ nbrsIn G s r, varB G B t (compIn G (s.erase r) w) := by
  conv_lhs => rw [erase_eq_biUnion hs hr]
  exact varB_biUnion ht _ _ (fun i hi j hj hij => disjoint_branches hG hi hj hij)
    (fun i hi j hj hij a ha b hb => not_adj_branches hG hi hj hij ha hb)

theorem meanB_outside_root (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    meanB G B t (outsideClosedNbhd G s r) =
      ∑ w ∈ nbrsIn G s r, meanB G B t ((compIn G (s.erase r) w).erase w) := by
  rw [outsideClosedNbhd_eq_biUnion hG hs hr]
  refine meanB_biUnion ht _ _ (fun i hi j hj hij => ?_) (fun i hi j hj hij a ha b hb => ?_)
  · exact (disjoint_branches hG hi hj hij).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  · exact not_adj_branches hG hi hj hij (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb)

theorem varB_outside_root (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    varB G B t (outsideClosedNbhd G s r) =
      ∑ w ∈ nbrsIn G s r, varB G B t ((compIn G (s.erase r) w).erase w) := by
  rw [outsideClosedNbhd_eq_biUnion hG hs hr]
  refine varB_biUnion ht _ _ (fun i hi j hj hij => ?_) (fun i hi j hj hij a ha b hb => ?_)
  · exact (disjoint_branches hG hi hj hij).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  · exact not_adj_branches hG hi hj hij (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb)

/-- **`G = ∑ F_child`**: with the root occupied from above, the children's subtrees are free. -/
theorem resF_erase_root (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    resF G B t A (s.erase r) = ∑ w ∈ nbrsIn G s r, resF G B t A (compIn G (s.erase r) w) := by
  unfold resF
  rw [meanB_erase_root hG ht hs hr, varB_erase_root hG ht hs hr, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

theorem resF_outside_root (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    resF G B t A (outsideClosedNbhd G s r) =
      ∑ w ∈ nbrsIn G s r, resF G B t A ((compIn G (s.erase r) w).erase w) := by
  unfold resF
  rw [meanB_outside_root hG ht hs hr, varB_outside_root hG ht hs hr, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

theorem mixture_gap (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    aB B r + meanB G B t (outsideClosedNbhd G s r) - meanB G B t (s.erase r) =
      aB B r - ∑ w ∈ nbrsIn G s r, port G B t (compIn G (s.erase r) w) w := by
  rw [meanB_erase_root hG ht hs hr, meanB_outside_root hG ht hs hr]
  unfold port
  rw [Finset.sum_sub_distrib]
  ring

/-- **The port recursion** `u = p (a − ∑_w u_w)`. -/
theorem port_rec (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    port G B t s r = rootProb G t s r *
      (aB B r - ∑ w ∈ nbrsIn G s r, port G B t (compIn G (s.erase r) w) w) := by
  rw [← mixture_gap hG ht hs hr]
  unfold port
  rw [meanB_root ht hr]
  ring

/-- **The recursion (1)**:
`F(s) = A p a + (1 − p) ∑_w F(C_w) + p ∑_w F(C_w − w) − p (1 − p)(a − ∑_w u_w)²`. -/
theorem resF_rec (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    resF G B t A s = A * rootProb G t s r * aB B r +
      (1 - rootProb G t s r) * ∑ w ∈ nbrsIn G s r, resF G B t A (compIn G (s.erase r) w) +
      rootProb G t s r * ∑ w ∈ nbrsIn G s r, resF G B t A ((compIn G (s.erase r) w).erase w) -
      rootProb G t s r * (1 - rootProb G t s r) *
        (aB B r - ∑ w ∈ nbrsIn G s r, port G B t (compIn G (s.erase r) w) w) ^ 2 := by
  rw [← resF_erase_root hG ht hs hr, ← resF_outside_root hG ht hs hr,
    ← mixture_gap hG ht hs hr]
  unfold resF
  rw [meanB_root ht hr, varB_root ht hr]
  ring

end Rec

end Erdos993Lean.Analytic.Reserve
