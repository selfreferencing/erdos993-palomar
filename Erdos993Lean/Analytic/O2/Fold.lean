module

public import Erdos993Lean.Analytic.O2.Defs
public import Erdos993Lean.Analytic.Reserve.Tree

/-!
# O2: the diary fold over a rooted tree

Source: the O2 proof, §1 and §4
(every original record carries its actual parent), its implementation map §2, obligation 1
(records indexed by actual vertices, the transfer "actual child-subtree construction plus original
parent boundary transport, terminating by subtree cardinality").

A rooted vertex set `(s, r)` of an acyclic graph (the `compIn` decomposition) carries at every
vertex `v` the two inherited fields of the O2 record: `ρ_v = r_v`, the probability that the parent of
`v` is vacant, and `t_v`, the parent's cavity probability.  The root receives `(ρ, t)`; a child `w` of
`v` receives `(1 − ρ_v p_v, p_v)` with `p_v = rootProb G λ (subtree of v) v` (the parent's marginal
is `ρ_v p_v`, Tail's `mu_branch`).

* `dfold G λ f s r ρ t`: the sum over the vertices `v` of `(s, r)` of `f (subtree of v) v ρ_v t_v`;
* `dfold_eq` (unfolding), `dfold_add`, `dfold_sub`, `dfold_mul_left` (linearity);
* **`dfold_telescope`**: an incoming charge `Y` of every vertex is regrouped at its parent,
  `dfold (X − Y) = dfold (X − ∑_{children} Y) − Y(root)`;
* `dfold_const`: for a field of the vertex alone, the fold is the plain sum over `s`;
* `dfold_le_of_inv`, `dfold_congr_of_inv`: comparison under an invariant carried down the tree.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.O2

open Finset Erdos993Lean.Analytic.Tail

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

-- `hr` is used by the termination proof only.
set_option linter.unusedVariables false in
variable (G) in
/-- **The diary fold**: the sum over the vertices `v` of the rooted vertex set `(s, r)` of
`f (subtree of v) v ρ_v t_v`, where the root receives `(ρ, t)` and a child `w` of `v` receives
`(1 − ρ_v p_v, p_v)`, `p_v = rootProb G λ (subtree of v) v` (and `0` if `r ∉ s`). -/
noncomputable def dfold (lam : ℝ) (f : Finset V → V → ℝ → ℝ → ℝ) (s : Finset V) (r : V)
    (ρ t : ℝ) : ℝ :=
  if hr : r ∈ s then
    f s r ρ t + ∑ w ∈ (nbrsIn G s r).attach,
      dfold lam f (compIn G (s.erase r) w.1) w.1 (1 - ρ * rootProb G lam s r) (rootProb G lam s r)
  else 0
termination_by s.card
decreasing_by
  exact lt_of_le_of_lt (Finset.card_le_card (compIn_subset _ _)) (Finset.card_erase_lt_of_mem hr)

theorem dfold_eq (lam : ℝ) (f : Finset V → V → ℝ → ℝ → ℝ) {s : Finset V} {r : V} (hr : r ∈ s)
    (ρ t : ℝ) :
    dfold G lam f s r ρ t = f s r ρ t + ∑ w ∈ nbrsIn G s r,
      dfold G lam f (compIn G (s.erase r) w) w (1 - ρ * rootProb G lam s r)
        (rootProb G lam s r) := by
  rw [dfold, dif_pos hr]
  congr 1
  exact Finset.sum_attach (nbrsIn G s r) (fun w => dfold G lam f (compIn G (s.erase r) w) w
    (1 - ρ * rootProb G lam s r) (rootProb G lam s r))

theorem dfold_of_not_mem (lam : ℝ) (f : Finset V → V → ℝ → ℝ → ℝ) {s : Finset V} {r : V}
    (hr : r ∉ s) (ρ t : ℝ) : dfold G lam f s r ρ t = 0 := by
  rw [dfold, dif_neg hr]

/-! ### Linearity -/

theorem dfold_add (lam : ℝ) (f g : Finset V → V → ℝ → ℝ → ℝ) (s : Finset V) (r : V) (ρ t : ℝ) :
    dfold G lam (fun s v ρ t => f s v ρ t + g s v ρ t) s r ρ t =
      dfold G lam f s r ρ t + dfold G lam g s r ρ t := by
  refine tree_induction (G := G) (P := fun s r => ∀ ρ t : ℝ,
    dfold G lam (fun s v ρ t => f s v ρ t + g s v ρ t) s r ρ t =
      dfold G lam f s r ρ t + dfold G lam g s r ρ t) ?_ ?_ s r ρ t
  · intro s r hr ih ρ t
    rw [dfold_eq _ _ hr, dfold_eq _ _ hr, dfold_eq _ _ hr,
      Finset.sum_congr rfl (fun w hw => ih w hw _ _), Finset.sum_add_distrib]
    ring
  · intro s r hr ρ t
    rw [dfold_of_not_mem _ _ hr, dfold_of_not_mem _ _ hr, dfold_of_not_mem _ _ hr, add_zero]

theorem dfold_sub (lam : ℝ) (f g : Finset V → V → ℝ → ℝ → ℝ) (s : Finset V) (r : V) (ρ t : ℝ) :
    dfold G lam (fun s v ρ t => f s v ρ t - g s v ρ t) s r ρ t =
      dfold G lam f s r ρ t - dfold G lam g s r ρ t := by
  refine tree_induction (G := G) (P := fun s r => ∀ ρ t : ℝ,
    dfold G lam (fun s v ρ t => f s v ρ t - g s v ρ t) s r ρ t =
      dfold G lam f s r ρ t - dfold G lam g s r ρ t) ?_ ?_ s r ρ t
  · intro s r hr ih ρ t
    rw [dfold_eq _ _ hr, dfold_eq _ _ hr, dfold_eq _ _ hr,
      Finset.sum_congr rfl (fun w hw => ih w hw _ _), Finset.sum_sub_distrib]
    ring
  · intro s r hr ρ t
    rw [dfold_of_not_mem _ _ hr, dfold_of_not_mem _ _ hr, dfold_of_not_mem _ _ hr, sub_zero]

theorem dfold_mul_left (lam c : ℝ) (f : Finset V → V → ℝ → ℝ → ℝ) (s : Finset V) (r : V)
    (ρ t : ℝ) :
    dfold G lam (fun s v ρ t => c * f s v ρ t) s r ρ t = c * dfold G lam f s r ρ t := by
  refine tree_induction (G := G) (P := fun s r => ∀ ρ t : ℝ,
    dfold G lam (fun s v ρ t => c * f s v ρ t) s r ρ t = c * dfold G lam f s r ρ t) ?_ ?_ s r ρ t
  · intro s r hr ih ρ t
    rw [dfold_eq _ _ hr, dfold_eq _ _ hr, Finset.sum_congr rfl (fun w hw => ih w hw _ _),
      ← Finset.mul_sum]
    ring
  · intro s r hr ρ t
    rw [dfold_of_not_mem _ _ hr, dfold_of_not_mem _ _ hr, mul_zero]

/-! ### Telescoping an incoming charge to the parent -/

/-- **Telescoping.**  If every vertex pays an incoming charge `Y` (a function of its own record and
of the fields `(ρ, t)` it inherits from its parent), the charges of the children of `v` can be
regrouped at `v`: `dfold (X − Y) = dfold (X − ∑_{w child} Y_w) − Y_root`. -/
theorem dfold_telescope (lam : ℝ) (X Y : Finset V → V → ℝ → ℝ → ℝ) {s : Finset V} {r : V}
    (hr : r ∈ s) (ρ t : ℝ) :
    dfold G lam (fun s v ρ t => X s v ρ t - Y s v ρ t) s r ρ t =
      dfold G lam (fun s v ρ t => X s v ρ t - ∑ w ∈ nbrsIn G s v,
        Y (compIn G (s.erase v) w) w (1 - ρ * rootProb G lam s v) (rootProb G lam s v))
        s r ρ t - Y s r ρ t := by
  refine tree_induction (G := G) (P := fun s r => r ∈ s → ∀ ρ t : ℝ,
    dfold G lam (fun s v ρ t => X s v ρ t - Y s v ρ t) s r ρ t =
      dfold G lam (fun s v ρ t => X s v ρ t - ∑ w ∈ nbrsIn G s v,
        Y (compIn G (s.erase v) w) w (1 - ρ * rootProb G lam s v) (rootProb G lam s v))
        s r ρ t - Y s r ρ t) ?_ ?_ s r hr ρ t
  · intro s r hr ih _ ρ t
    rw [dfold_eq _ _ hr, dfold_eq _ _ hr,
      Finset.sum_congr rfl (fun w hw => ih w hw (self_mem_branch hw) _ _), Finset.sum_sub_distrib]
    ring
  · intro s r hr hr'
    exact absurd hr' hr

/-! ### Fields of the vertex alone -/

/-- For a field `F v` of the vertex alone, the fold is the plain sum over the rooted set. -/
theorem dfold_const (hG : G.IsAcyclic) (lam : ℝ) (F : V → ℝ) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (ρ t : ℝ) :
    dfold G lam (fun _ v _ _ => F v) s r ρ t = ∑ v ∈ s, F v := by
  refine rooted_induction hG (P := fun s r => ∀ ρ t : ℝ,
    dfold G lam (fun _ v _ _ => F v) s r ρ t = ∑ v ∈ s, F v) ?_ hs hr ρ t
  intro s r hs hr ih ρ t
  have hsplit : ∑ v ∈ s.erase r, F v =
      ∑ w ∈ nbrsIn G s r, ∑ v ∈ compIn G (s.erase r) w, F v := by
    conv_lhs => rw [erase_eq_biUnion hs hr]
    exact Finset.sum_biUnion fun i hi j hj hij => disjoint_branches hG hi hj hij
  rw [dfold_eq _ _ hr, Finset.sum_congr rfl (fun w hw => ih w hw _ _), ← hsplit,
    Finset.add_sum_erase s F hr]

/-! ### Comparison under an inherited invariant -/

/-- **Comparison under an invariant** carried down the tree (from a vertex to each child with the
inherited fields `(1 − ρ p, p)`). -/
theorem dfold_le_of_inv (hG : G.IsAcyclic) (lam : ℝ) {f g : Finset V → V → ℝ → ℝ → ℝ}
    (Inv : Finset V → V → ℝ → ℝ → Prop)
    (hInv : ∀ s r ρ t, ConnectedIn G s → r ∈ s → Inv s r ρ t → ∀ w ∈ nbrsIn G s r,
      Inv (compIn G (s.erase r) w) w (1 - ρ * rootProb G lam s r) (rootProb G lam s r))
    (hfg : ∀ s r ρ t, ConnectedIn G s → r ∈ s → Inv s r ρ t → f s r ρ t ≤ g s r ρ t)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) {ρ t : ℝ} (h : Inv s r ρ t) :
    dfold G lam f s r ρ t ≤ dfold G lam g s r ρ t := by
  refine rooted_induction hG (P := fun s r => ∀ ρ t : ℝ, Inv s r ρ t →
    dfold G lam f s r ρ t ≤ dfold G lam g s r ρ t) ?_ hs hr ρ t h
  intro s r hs hr ih ρ t h
  rw [dfold_eq _ _ hr, dfold_eq _ _ hr]
  exact add_le_add (hfg s r ρ t hs hr h)
    (Finset.sum_le_sum fun w hw => ih w hw _ _ (hInv s r ρ t hs hr h w hw))

/-- **Equality under an invariant** carried down the tree. -/
theorem dfold_congr_of_inv (hG : G.IsAcyclic) (lam : ℝ) {f g : Finset V → V → ℝ → ℝ → ℝ}
    (Inv : Finset V → V → ℝ → ℝ → Prop)
    (hInv : ∀ s r ρ t, ConnectedIn G s → r ∈ s → Inv s r ρ t → ∀ w ∈ nbrsIn G s r,
      Inv (compIn G (s.erase r) w) w (1 - ρ * rootProb G lam s r) (rootProb G lam s r))
    (hfg : ∀ s r ρ t, ConnectedIn G s → r ∈ s → Inv s r ρ t → f s r ρ t = g s r ρ t)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) {ρ t : ℝ} (h : Inv s r ρ t) :
    dfold G lam f s r ρ t = dfold G lam g s r ρ t :=
  le_antisymm (dfold_le_of_inv hG lam Inv hInv (fun s r ρ t hs hr h => (hfg s r ρ t hs hr h).le)
      hs hr h)
    (dfold_le_of_inv hG lam Inv hInv (fun s r ρ t hs hr h => (hfg s r ρ t hs hr h).ge) hs hr h)

/-- **Nonnegativity under an invariant.** -/
theorem dfold_nonneg_of_inv (hG : G.IsAcyclic) (lam : ℝ) {f : Finset V → V → ℝ → ℝ → ℝ}
    (Inv : Finset V → V → ℝ → ℝ → Prop)
    (hInv : ∀ s r ρ t, ConnectedIn G s → r ∈ s → Inv s r ρ t → ∀ w ∈ nbrsIn G s r,
      Inv (compIn G (s.erase r) w) w (1 - ρ * rootProb G lam s r) (rootProb G lam s r))
    (hf : ∀ s r ρ t, ConnectedIn G s → r ∈ s → Inv s r ρ t → 0 ≤ f s r ρ t)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) {ρ t : ℝ} (h : Inv s r ρ t) :
    0 ≤ dfold G lam f s r ρ t := by
  have h0 : dfold G lam (fun _ _ _ _ => (0 : ℝ)) s r ρ t = 0 := by
    rw [dfold_const hG lam (fun _ => (0 : ℝ)) hs hr, Finset.sum_const_zero]
  rw [← h0]
  exact dfold_le_of_inv hG lam Inv hInv hf hs hr h

end Erdos993Lean.Analytic.O2
