module

public import Mathlib
public import Erdos993Lean.Analytic.Defs
public import Erdos993Lean.Analytic.Tail.Weighted

/-!
# The tail input T3, part 2: rooted vertex sets and downward probabilities

Source: T23 §3:
"root every component having a C-vertex at a
C-vertex; downward ratios `R_v = λ ∏_{u ∈ ch(v)} 1/(1 + R_u)`, `p_v = R_v/(1 + R_v)`".

A *rooted vertex set* is a pair `(s, r)` with `s` connected in the acyclic graph `G` and `r ∈ s`.
Its children are `nbrsIn G s r` and the subtree of the child `w` is the branch
`compIn G (s.erase r) w` (`Floor/TreeDecomp.lean`).  Quantities attached to every vertex of the
rooted tree are defined by well-founded recursion on `s.card`:

* `treeSum G f s r = f s r + ∑_{w} treeSum G f (C_w) w` and `treeProd` (the same with products):
  the sum (product) over all vertices `v` of `f (subtree of v) v`;
* `rootProb G t s r = t Z(s - N[r]) / Z(s)`: the downward probability `p_r` of T23, i.e. the
  probability that `r` is occupied in the hard-core model of the subtree alone.

Main results:
* `treeSum_eq`, `treeProd_eq` (unfolding), `rooted_induction`, `treeProd_exp`, and the monotonicity
  lemmas `treeSum_le_treeSum`, `treeProd_le_treeProd`, `treeProd_nonneg`;
* `one_sub_rootProb` (`1 - p = Z(s - r)/Z(s)`), `rootProb_le_actQ` (`p ≤ q = t/(1+t)`),
  `rootProb_lt_actQ` (strict when `r` has a child), `rootProb_eq_actQ` (a leaf has `p = q`);
* `rootProb_odds`: `p / (1 - p) = t ∏_w (1 - p_w)` (the downward recursion `R_r = t ∏ 1/(1 + R_w)`).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Folds over a rooted vertex set -/

-- `hr` is used by the termination proof only.
set_option linter.unusedVariables false in
variable (G) in
/-- The sum over the vertices `v` of the rooted vertex set `(s, r)` of `f (subtree of v) v`:
`treeSum f s r = f s r + ∑_{w ∈ nbrsIn s r} treeSum f (compIn (s - r) w) w` (and `0` if `r ∉ s`). -/
noncomputable def treeSum (f : Finset V → V → ℝ) (s : Finset V) (r : V) : ℝ :=
  if hr : r ∈ s then
    f s r + ∑ w ∈ (nbrsIn G s r).attach, treeSum f (compIn G (s.erase r) w.1) w.1
  else 0
termination_by s.card
decreasing_by
  exact lt_of_le_of_lt (Finset.card_le_card (compIn_subset _ _)) (Finset.card_erase_lt_of_mem hr)

set_option linter.unusedVariables false in
variable (G) in
/-- The product over the vertices `v` of the rooted vertex set `(s, r)` of `f (subtree of v) v`. -/
noncomputable def treeProd (f : Finset V → V → ℝ) (s : Finset V) (r : V) : ℝ :=
  if hr : r ∈ s then
    f s r * ∏ w ∈ (nbrsIn G s r).attach, treeProd f (compIn G (s.erase r) w.1) w.1
  else 1
termination_by s.card
decreasing_by
  exact lt_of_le_of_lt (Finset.card_le_card (compIn_subset _ _)) (Finset.card_erase_lt_of_mem hr)

theorem treeSum_eq (f : Finset V → V → ℝ) {s : Finset V} {r : V} (hr : r ∈ s) :
    treeSum G f s r = f s r + ∑ w ∈ nbrsIn G s r, treeSum G f (compIn G (s.erase r) w) w := by
  rw [treeSum, dif_pos hr]
  congr 1
  exact Finset.sum_attach (nbrsIn G s r) (fun w => treeSum G f (compIn G (s.erase r) w) w)

theorem treeProd_eq (f : Finset V → V → ℝ) {s : Finset V} {r : V} (hr : r ∈ s) :
    treeProd G f s r = f s r * ∏ w ∈ nbrsIn G s r, treeProd G f (compIn G (s.erase r) w) w := by
  rw [treeProd, dif_pos hr]
  congr 1
  exact Finset.prod_attach (nbrsIn G s r) (fun w => treeProd G f (compIn G (s.erase r) w) w)

/-- Induction over all pairs `(s, r)` along the branch structure. -/
theorem tree_induction {P : Finset V → V → Prop}
    (step : ∀ s r, r ∈ s → (∀ w ∈ nbrsIn G s r, P (compIn G (s.erase r) w) w) → P s r)
    (base : ∀ s r, r ∉ s → P s r) (s : Finset V) (r : V) : P s r := by
  induction s using Finset.strongInduction generalizing r with
  | H s ih =>
    by_cases hr : r ∈ s
    · refine step s r hr fun w _ => ih _ ?_ w
      exact (compIn_subset _ _).trans_ssubset (Finset.erase_ssubset hr)
    · exact base s r hr

/-- Induction over rooted connected vertex sets: to prove `P s r` for every connected `s ∋ r`, it
suffices to prove it assuming it for every branch. -/
theorem rooted_induction (hG : G.IsAcyclic) {P : Finset V → V → Prop}
    (step : ∀ s r, ConnectedIn G s → r ∈ s →
      (∀ w ∈ nbrsIn G s r, P (compIn G (s.erase r) w) w) → P s r)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) : P s r := by
  induction s using Finset.strongInduction generalizing r with
  | H s ih =>
    apply step s r hs hr
    intro w hw
    obtain ⟨hC, hwC, _⟩ := compIn_branch hG hs hr hw
    exact ih _ ((compIn_subset _ _).trans_ssubset (Finset.erase_ssubset hr)) hC hwC

/-- The product of exponentials is the exponential of the sum. -/
theorem treeProd_exp (f : Finset V → V → ℝ) (s : Finset V) (r : V) :
    treeProd G (fun s r => Real.exp (f s r)) s r = Real.exp (treeSum G f s r) := by
  refine tree_induction (G := G)
    (P := fun s r => treeProd G (fun s r => Real.exp (f s r)) s r = Real.exp (treeSum G f s r))
    ?_ ?_ s r
  · intro s r hr ih
    rw [treeProd_eq _ hr, treeSum_eq _ hr, Real.exp_add, Real.exp_sum]
    congr 1
    exact Finset.prod_congr rfl ih
  · intro s r hr
    rw [treeProd, dif_neg hr, treeSum, dif_neg hr, Real.exp_zero]

theorem treeSum_le_treeSum (hG : G.IsAcyclic) {f g : Finset V → V → ℝ}
    (hfg : ∀ s r, ConnectedIn G s → r ∈ s → f s r ≤ g s r) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) : treeSum G f s r ≤ treeSum G g s r := by
  refine rooted_induction hG (P := fun s r => treeSum G f s r ≤ treeSum G g s r) ?_ hs hr
  intro s r hs hr ih
  rw [treeSum_eq _ hr, treeSum_eq _ hr]
  exact add_le_add (hfg s r hs hr) (Finset.sum_le_sum ih)

theorem treeSum_nonneg (hG : G.IsAcyclic) {f : Finset V → V → ℝ}
    (h0 : ∀ s r, ConnectedIn G s → r ∈ s → 0 ≤ f s r) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) : 0 ≤ treeSum G f s r := by
  refine rooted_induction hG (P := fun s r => 0 ≤ treeSum G f s r) ?_ hs hr
  intro s r hs hr ih
  rw [treeSum_eq _ hr]
  exact add_nonneg (h0 s r hs hr) (Finset.sum_nonneg ih)

theorem treeProd_nonneg (hG : G.IsAcyclic) {f : Finset V → V → ℝ}
    (h0 : ∀ s r, ConnectedIn G s → r ∈ s → 0 ≤ f s r) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) : 0 ≤ treeProd G f s r := by
  refine rooted_induction hG (P := fun s r => 0 ≤ treeProd G f s r) ?_ hs hr
  intro s r hs hr ih
  rw [treeProd_eq _ hr]
  exact mul_nonneg (h0 s r hs hr) (Finset.prod_nonneg ih)

theorem treeProd_le_treeProd (hG : G.IsAcyclic) {f g : Finset V → V → ℝ}
    (h0 : ∀ s r, ConnectedIn G s → r ∈ s → 0 ≤ f s r)
    (hfg : ∀ s r, ConnectedIn G s → r ∈ s → f s r ≤ g s r) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) : treeProd G f s r ≤ treeProd G g s r := by
  refine rooted_induction hG (P := fun s r => treeProd G f s r ≤ treeProd G g s r) ?_ hs hr
  intro s r hs hr ih
  rw [treeProd_eq _ hr, treeProd_eq _ hr]
  have hb : ∀ w ∈ nbrsIn G s r, 0 ≤ treeProd G f (compIn G (s.erase r) w) w := by
    intro w hw
    obtain ⟨hC, hwC, _⟩ := compIn_branch hG hs hr hw
    exact treeProd_nonneg hG h0 hC hwC
  exact mul_le_mul (hfg s r hs hr) (Finset.prod_le_prod₀ hb ih) (Finset.prod_nonneg hb)
    ((h0 s r hs hr).trans (hfg s r hs hr))

/-! ### The downward probability -/

variable (G) in
/-- The downward probability `p(s, r) = t Z(s - N[r]) / Z(s)`: the probability that the root `r`
is occupied in the hard-core model of `G[s]` at activity `t` (T23's `p_r` for the subtree `s`). -/
noncomputable def rootProb (t : ℝ) (s : Finset V) (r : V) : ℝ :=
  t * Zw G (fun _ => t) (outsideClosedNbhd G s r) / Zw G (fun _ => t) s

section rootProb

variable {t : ℝ}

theorem rootProb_nonneg (ht : 0 ≤ t) (s : Finset V) (r : V) : 0 ≤ rootProb G t s r :=
  div_nonneg (mul_nonneg ht (Zw_nonneg (fun _ => ht) _)) (Zw_nonneg (fun _ => ht) _)

/-- `1 - p = Z(s - r) / Z(s)`. -/
theorem one_sub_rootProb (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    1 - rootProb G t s r = Zw G (fun _ => t) (s.erase r) / Zw G (fun _ => t) s := by
  have hZ := Zw_pos (G := G) (fun _ => ht) s
  rw [rootProb, eq_div_iff hZ.ne', sub_mul, one_mul, div_mul_cancel₀ _ hZ.ne',
    Zw_erase_add _ hr]
  ring

theorem rootProb_lt_one (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    rootProb G t s r < 1 := by
  have h := one_sub_rootProb (G := G) ht hr
  have : 0 < Zw G (fun _ => t) (s.erase r) / Zw G (fun _ => t) s :=
    div_pos (Zw_pos (fun _ => ht) _) (Zw_pos (fun _ => ht) _)
  linarith

theorem rootProb_le_one (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    rootProb G t s r ≤ 1 :=
  (rootProb_lt_one ht hr).le

theorem rootProb_pos (ht : 0 < t) (s : Finset V) (r : V) : 0 < rootProb G t s r :=
  div_pos (mul_pos ht (Zw_pos (fun _ => ht.le) _)) (Zw_pos (fun _ => ht.le) _)

/-- `s - N[r] ⊆ s - r`. -/
theorem outsideClosedNbhd_subset_erase (s : Finset V) (r : V) :
    outsideClosedNbhd G s r ⊆ s.erase r := by
  intro x hx
  simp only [outsideClosedNbhd, Finset.mem_filter] at hx
  exact Finset.mem_erase.mpr ⟨hx.2.1, hx.1⟩

/-- **`p ≤ q`**: the downward probability is at most `q = t/(1+t)`. -/
theorem rootProb_le_actQ (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    rootProb G t s r ≤ actQ t := by
  have hZ : Zw G (fun _ => t) s =
      Zw G (fun _ => t) (s.erase r) + t * Zw G (fun _ => t) (outsideClosedNbhd G s r) :=
    Zw_erase_add _ hr
  have hab : Zw G (fun _ => t) (outsideClosedNbhd G s r) ≤ Zw G (fun _ => t) (s.erase r) :=
    Zw_mono (fun _ => ht) (outsideClosedNbhd_subset_erase s r)
  have hb := Zw_pos (G := G) (fun _ => ht) (s.erase r)
  have ha := Zw_pos (G := G) (fun _ => ht) (outsideClosedNbhd G s r)
  have hZpos := Zw_pos (G := G) (fun _ => ht) s
  rw [rootProb, actQ, div_le_div_iff₀ hZpos (by linarith), hZ]
  nlinarith [mul_le_mul_of_nonneg_left hab ht, mul_nonneg ht ht]

/-- A vertex with a child has `p < q`. -/
theorem rootProb_lt_actQ (ht : 0 < t) {s : Finset V} {r : V} (hr : r ∈ s)
    (hne : (nbrsIn G s r).Nonempty) : rootProb G t s r < actQ t := by
  obtain ⟨u, hu⟩ := hne
  rw [mem_nbrsIn] at hu
  have hZ : Zw G (fun _ => t) s =
      Zw G (fun _ => t) (s.erase r) + t * Zw G (fun _ => t) (outsideClosedNbhd G s r) :=
    Zw_erase_add _ hr
  have hsub : outsideClosedNbhd G s r ⊆ (s.erase r).erase u := by
    intro x hx
    simp only [outsideClosedNbhd, Finset.mem_filter] at hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hx.2.1, hx.1⟩⟩
    rintro rfl
    exact hx.2.2 hu.2
  have hus : u ∈ s.erase r := Finset.mem_erase.mpr ⟨(G.ne_of_adj hu.2).symm, hu.1⟩
  have hab : Zw G (fun _ => t) (outsideClosedNbhd G s r) + t ≤ Zw G (fun _ => t) (s.erase r) :=
    Zw_add_le_of_mem (fun _ => ht.le) hus hsub
  have hZpos := Zw_pos (G := G) (fun _ => ht.le) s
  have ha := Zw_pos (G := G) (fun _ => ht.le) (outsideClosedNbhd G s r)
  rw [rootProb, actQ, div_lt_div_iff₀ hZpos (by linarith), hZ]
  nlinarith [mul_pos ht ht, mul_le_mul_of_nonneg_left hab ht.le]

/-- A vertex without children (a leaf of the rooted tree, or an isolated vertex) has `p = q`. -/
theorem rootProb_eq_actQ (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s)
    (hnil : nbrsIn G s r = ∅) : rootProb G t s r = actQ t := by
  have hout : outsideClosedNbhd G s r = s.erase r := by
    ext x
    simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hxr, _⟩
      exact ⟨hxr, hx⟩
    · rintro ⟨hxr, hx⟩
      refine ⟨hx, hxr, fun hadj => ?_⟩
      have : x ∈ nbrsIn G s r := mem_nbrsIn.mpr ⟨hx, hadj⟩
      rw [hnil] at this
      exact Finset.notMem_empty x this
  have hZ : Zw G (fun _ => t) s =
      Zw G (fun _ => t) (s.erase r) + t * Zw G (fun _ => t) (outsideClosedNbhd G s r) :=
    Zw_erase_add _ hr
  have hb := Zw_pos (G := G) (fun _ => ht) (s.erase r)
  rw [rootProb, actQ, hZ, hout]
  field_simp

/-- `1 - p_w = Z(C_w - w) / Z(C_w)` for a branch. -/
theorem one_sub_rootProb_branch (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V}
    (hs : ConnectedIn G s) {r w : V} (hr : r ∈ s) (hw : w ∈ nbrsIn G s r) :
    1 - rootProb G t (compIn G (s.erase r) w) w =
      Zw G (fun _ => t) ((compIn G (s.erase r) w).erase w) /
        Zw G (fun _ => t) (compIn G (s.erase r) w) :=
  one_sub_rootProb ht (compIn_branch hG hs hr hw).2.1

/-- **The downward recursion** `R_r = t ∏_w (1 - p_w)` in odds form: `p / (1 - p) = t ∏_w (1 - p_w)`. -/
theorem rootProb_odds (hG : G.IsAcyclic) (ht : 0 < t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    rootProb G t s r / (1 - rootProb G t s r) =
      t * ∏ w ∈ nbrsIn G s r, (1 - rootProb G t (compIn G (s.erase r) w) w) := by
  have hprod : ∏ w ∈ nbrsIn G s r, (1 - rootProb G t (compIn G (s.erase r) w) w) =
      Zw G (fun _ => t) (outsideClosedNbhd G s r) / Zw G (fun _ => t) (s.erase r) := by
    rw [Finset.prod_congr rfl (fun w hw => one_sub_rootProb_branch hG ht.le hs hr hw),
      Finset.prod_div_distrib, Zw_outside_root hG _ hs hr, Zw_erase_root hG _ hs hr]
  rw [hprod, one_sub_rootProb ht.le hr, rootProb]
  have h1 := Zw_pos (G := G) (fun _ => ht.le) s
  have h2 := Zw_pos (G := G) (fun _ => ht.le) (s.erase r)
  field_simp

end rootProb

end Erdos993Lean.Analytic.Tail
