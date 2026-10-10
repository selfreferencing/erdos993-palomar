module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.LemmaA

/-!
# The tail input T3, part 4: marginals on a rooted tree

Source: T23 §3, Lemma B:
`π_c = r_c p_c` with
`r_c = 1 − π_{parent(c)}`, `r_root = 1`.

`marg G t s x = t Z(s − N[x]) / Z(s)` is the hard-core marginal `π_x = P(x ∈ S)` of `G[s]` at
activity `t` (and `0` for `x ∉ s`).  The top-down factor `r_c` of T23 is carried by

  `mu G t s r ρ x = ρ π_x(s) + (1 − ρ) π_x(s − r)`,

the marginal of `x` in the model where the root `r` is free with probability `ρ` (the parent of `r`
is unoccupied with probability `ρ`); at the top `ρ = 1` it is the true marginal.

Main results:
* `marg_condition` (conditioning on a vertex `v`):
  `π_x(s) = (1 − p_v) π_x(s − v) + p_v π_x(s − N[v])`;
* `marg_of_closed`: the marginal only depends on the part of `s` that `x` is joined to
  (in particular `π_x(s) = π_x(K)` for the component `K` of `x`);
* `mu_root`: `μ_r = ρ p_r`; `mu_branch`: for `x` in the branch of the child `w`,
  `μ(s, r, ρ, x) = μ(C_w, w, 1 − ρ p_r, x)` (the child's factor is `1 − π_parent`);
* `massB_rec`: the B-mass below the root, `massB s r ρ = ∑_{x ∈ B ∩ (s − r)} μ(s, r, ρ, x)`,
  satisfies `massB s r ρ = ∑_w ([w ∈ B] (1 − ρ p_r) p_w + massB(C_w, w, 1 − ρ p_r))`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Set identities for closed neighbourhoods -/

theorem mem_outsideClosedNbhd {s : Finset V} {x y : V} :
    y ∈ outsideClosedNbhd G s x ↔ y ∈ s ∧ y ≠ x ∧ ¬ G.Adj x y := by
  simp only [outsideClosedNbhd, Finset.mem_filter]

theorem outside_erase_comm (s : Finset V) (x v : V) :
    outsideClosedNbhd G (s.erase v) x = (outsideClosedNbhd G s x).erase v := by
  ext y
  simp only [mem_outsideClosedNbhd, Finset.mem_erase]
  tauto

theorem outside_outside_comm (s : Finset V) (x v : V) :
    outsideClosedNbhd G (outsideClosedNbhd G s v) x =
      outsideClosedNbhd G (outsideClosedNbhd G s x) v := by
  ext y
  simp only [mem_outsideClosedNbhd]
  tauto

/-! ### Marginals -/

variable (G) in
/-- The hard-core marginal `π_x(s) = t Z(s − N[x]) / Z(s)` of `G[s]` at activity `t` (`0` if
`x ∉ s`). -/
noncomputable def marg (t : ℝ) (s : Finset V) (x : V) : ℝ :=
  if x ∈ s then t * Zw G (fun _ => t) (outsideClosedNbhd G s x) / Zw G (fun _ => t) s else 0

section marg

variable {t : ℝ}

theorem marg_of_mem {s : Finset V} {x : V} (hx : x ∈ s) : marg G t s x = rootProb G t s x := by
  rw [marg, if_pos hx, rootProb]

theorem marg_of_not_mem {s : Finset V} {x : V} (hx : x ∉ s) : marg G t s x = 0 := by
  rw [marg, if_neg hx]

theorem marg_nonneg (ht : 0 ≤ t) (s : Finset V) (x : V) : 0 ≤ marg G t s x := by
  unfold marg
  split_ifs
  · exact div_nonneg (mul_nonneg ht (Zw_nonneg (fun _ => ht) _)) (Zw_nonneg (fun _ => ht) _)
  · exact le_rfl

theorem marg_le_one (ht : 0 ≤ t) (s : Finset V) (x : V) : marg G t s x ≤ 1 := by
  by_cases hx : x ∈ s
  · rw [marg_of_mem hx]
    exact rootProb_le_one ht hx
  · rw [marg_of_not_mem hx]
    exact zero_le_one

/-- **Conditioning on a vertex `v`**: `π_x(s) = (1 − p_v) π_x(s − v) + p_v π_x(s − N[v])`. -/
theorem marg_condition (ht : 0 ≤ t) {s : Finset V} {v x : V} (hv : v ∈ s) (hx : x ∈ s)
    (hxv : x ≠ v) :
    marg G t s x = (1 - rootProb G t s v) * marg G t (s.erase v) x +
      rootProb G t s v * marg G t (outsideClosedNbhd G s v) x := by
  have hxe : x ∈ s.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
  have hZ := (Zw_pos (G := G) (fun _ => ht) s).ne'
  have hZe := (Zw_pos (G := G) (fun _ => ht) (s.erase v)).ne'
  have hZo := (Zw_pos (G := G) (fun _ => ht) (outsideClosedNbhd G s v)).ne'
  rw [one_sub_rootProb ht hv]
  by_cases hadj : G.Adj v x
  · have hxo : x ∉ outsideClosedNbhd G s v := by
      rw [mem_outsideClosedNbhd]
      exact fun h => h.2.2 hadj
    have hvo : v ∉ outsideClosedNbhd G s x := by
      rw [mem_outsideClosedNbhd]
      exact fun h => h.2.2 hadj.symm
    have hset : outsideClosedNbhd G (s.erase v) x = outsideClosedNbhd G s x := by
      rw [outside_erase_comm, Finset.erase_eq_of_notMem hvo]
    simp only [marg, if_pos hx, if_pos hxe, if_neg hxo, hset, mul_zero, add_zero]
    field_simp
  · have hxo : x ∈ outsideClosedNbhd G s v := mem_outsideClosedNbhd.mpr ⟨hx, hxv, hadj⟩
    have hvo : v ∈ outsideClosedNbhd G s x :=
      mem_outsideClosedNbhd.mpr ⟨hv, fun h => hxv h.symm, fun h => hadj h.symm⟩
    have hsplit : Zw G (fun _ => t) (outsideClosedNbhd G s x) =
        Zw G (fun _ => t) (outsideClosedNbhd G (s.erase v) x) +
          t * Zw G (fun _ => t) (outsideClosedNbhd G (outsideClosedNbhd G s v) x) := by
      rw [Zw_erase_add (fun _ => t) hvo, outside_erase_comm, outside_outside_comm s v x]
    have hZoo := (Zw_pos (G := G) (fun _ => ht) (outsideClosedNbhd G s x)).ne'
    simp only [marg, if_pos hx, if_pos hxe, if_pos hxo]
    rw [hsplit, rootProb]
    field_simp

/-- **Locality of marginals**: if `x ∈ K ⊆ s` and there are no edges between `K` and `s − K`, then
`π_x(s) = π_x(K)`. -/
theorem marg_of_closed (ht : 0 ≤ t) {s K : Finset V} (hK : K ⊆ s)
    (hno : ∀ a ∈ K, ∀ b ∈ s \ K, ¬ G.Adj a b) {x : V} (hx : x ∈ K) :
    marg G t s x = marg G t K x := by
  have hxs : x ∈ s := hK hx
  have hO : outsideClosedNbhd G s x = outsideClosedNbhd G K x ∪ (s \ K) := by
    ext y
    simp only [mem_outsideClosedNbhd, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hy, hyx, hadj⟩
      by_cases hyK : y ∈ K
      · exact Or.inl ⟨hyK, hyx, hadj⟩
      · exact Or.inr ⟨hy, hyK⟩
    · rintro (⟨hyK, hyx, hadj⟩ | ⟨hy, hyK⟩)
      · exact ⟨hK hyK, hyx, hadj⟩
      · refine ⟨hy, ?_, hno x hx y (Finset.mem_sdiff.mpr ⟨hy, hyK⟩)⟩
        rintro rfl
        exact hyK hx
  have hOsub : outsideClosedNbhd G K x ⊆ K := Finset.filter_subset _ _
  have hdisj : Disjoint (outsideClosedNbhd G K x) (s \ K) :=
    Finset.disjoint_of_subset_left hOsub Finset.disjoint_sdiff
  have hno' : ∀ a ∈ outsideClosedNbhd G K x, ∀ b ∈ s \ K, ¬ G.Adj a b :=
    fun a ha b hb => hno a (hOsub ha) b hb
  have hZs : Zw G (fun _ => t) s = Zw G (fun _ => t) K * Zw G (fun _ => t) (s \ K) := by
    rw [← Zw_union _ Finset.disjoint_sdiff hno, Finset.union_sdiff_of_subset hK]
  have h1 := (Zw_pos (G := G) (fun _ => ht) K).ne'
  have h2 := (Zw_pos (G := G) (fun _ => ht) (s \ K)).ne'
  unfold marg
  rw [if_pos hxs, if_pos hx, hO, Zw_union _ hdisj hno', hZs, ← mul_assoc,
    mul_div_mul_right _ _ h2]

/-- Inside `s − r`, the marginal of a vertex of the branch `C_w` is its marginal in `C_w`. -/
theorem marg_erase_root_branch (ht : 0 ≤ t) {s : Finset V} {r w x : V}
    (hx : x ∈ compIn G (s.erase r) w) :
    marg G t (s.erase r) x = marg G t (compIn G (s.erase r) w) x :=
  marg_of_closed ht (compIn_subset _ _) (fun _ ha _ hb => not_adj_compIn_sdiff ha hb) hx

/-- Inside `s − N[r]`, the marginal of a vertex `x ≠ w` of the branch `C_w` is its marginal in
`C_w − w`. -/
theorem marg_outside_root_branch (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} {r w x : V}
    (hw : w ∈ nbrsIn G s r) (hx : x ∈ compIn G (s.erase r) w) (hxw : x ≠ w) :
    marg G t (outsideClosedNbhd G s r) x = marg G t ((compIn G (s.erase r) w).erase w) x := by
  have hrw := (mem_nbrsIn.mp hw).2
  have hsub : (compIn G (s.erase r) w).erase w ⊆ outsideClosedNbhd G s r := by
    intro a ha
    obtain ⟨haw, haC⟩ := Finset.mem_erase.mp ha
    have has := compIn_subset _ _ haC
    rw [Finset.mem_erase] at has
    exact mem_outsideClosedNbhd.mpr ⟨has.2, has.1,
      fun hra => haw (eq_of_mem_branch_of_adj hG hrw haC hra)⟩
  refine marg_of_closed ht hsub ?_ (Finset.mem_erase.mpr ⟨hxw, hx⟩)
  intro a ha b hb hab
  obtain ⟨hbO, hbK⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨hbs, hbr, _⟩ := mem_outsideClosedNbhd.mp hbO
  have haC := Finset.mem_of_mem_erase ha
  have hbC : b ∈ compIn G (s.erase r) w :=
    mem_compIn_of_adjIn haC ⟨compIn_subset _ _ haC, Finset.mem_erase.mpr ⟨hbr, hbs⟩, hab⟩
  have hbw : b ≠ w := by
    rintro rfl
    exact (mem_outsideClosedNbhd.mp hbO).2.2 hrw
  exact hbK (Finset.mem_erase.mpr ⟨hbw, hbC⟩)

end marg

/-! ### The top-down factor -/

variable (G) in
/-- `μ(s, r, ρ, x) = ρ π_x(s) + (1 − ρ) π_x(s − r)`: the marginal of `x` when the root `r` is
blocked from above with probability `1 − ρ` (T23's `r_r = ρ`). -/
noncomputable def mu (t : ℝ) (s : Finset V) (r : V) (ρ : ℝ) (x : V) : ℝ :=
  ρ * marg G t s x + (1 - ρ) * marg G t (s.erase r) x

section mu

variable {t : ℝ}

theorem mu_one (s : Finset V) (r x : V) : mu G t s r 1 x = marg G t s x := by
  unfold mu
  ring

/-- `μ` at the root: `ρ p_r`. -/
theorem mu_root {s : Finset V} {r : V} (hr : r ∈ s) (ρ : ℝ) :
    mu G t s r ρ r = ρ * rootProb G t s r := by
  unfold mu
  rw [marg_of_mem hr, marg_of_not_mem (Finset.notMem_erase r s)]
  ring

theorem mu_nonneg (ht : 0 ≤ t) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (s : Finset V) (r x : V) :
    0 ≤ mu G t s r ρ x :=
  add_nonneg (mul_nonneg hρ0 (marg_nonneg ht _ _))
    (mul_nonneg (by linarith) (marg_nonneg ht _ _))

/-- **The top-down recursion** (T23 Lemma B, `π_c = r_c p_c`, `r_c = 1 − π_{parent(c)}`): for `x` in
the branch of the child `w`, `μ(s, r, ρ, x) = μ(C_w, w, 1 − ρ p_r, x)`. -/
theorem mu_branch (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} {r w x : V} (hr : r ∈ s)
    (hw : w ∈ nbrsIn G s r) (hx : x ∈ compIn G (s.erase r) w) (ρ : ℝ) :
    mu G t s r ρ x = mu G t (compIn G (s.erase r) w) w (1 - ρ * rootProb G t s r) x := by
  have hxe := compIn_subset _ _ hx
  obtain ⟨hxr, hxs⟩ := Finset.mem_erase.mp hxe
  unfold mu
  rw [marg_condition ht hr hxs hxr, marg_erase_root_branch ht hx]
  by_cases hxw : x = w
  · rw [hxw]
    have h1 : marg G t (outsideClosedNbhd G s r) w = 0 := by
      apply marg_of_not_mem
      rw [mem_outsideClosedNbhd]
      exact fun h => h.2.2 (mem_nbrsIn.mp hw).2
    rw [h1, marg_of_not_mem (Finset.notMem_erase w _)]
    ring
  · rw [marg_outside_root_branch hG ht hw hx hxw]
    ring

end mu

/-! ### The B-mass below the root -/

variable (G) in
/-- The B-mass below the root: `∑_{x ∈ B ∩ (s − r)} μ(s, r, ρ, x)`; at `ρ = 1` it is
`∑_{b ∈ B ∩ (s − r)} π_b(s)`. -/
noncomputable def massB (B : Finset V) (t : ℝ) (s : Finset V) (r : V) (ρ : ℝ) : ℝ :=
  ∑ x ∈ (s.erase r).filter (· ∈ B), mu G t s r ρ x

/-- Splitting the base vertex off a sum over the B-vertices of a branch. -/
theorem sum_filter_split (B : Finset V) (K : Finset V) (w : V) (hw : w ∈ K) (f : V → ℝ) :
    ∑ x ∈ K.filter (· ∈ B), f x =
      (if w ∈ B then f w else 0) + ∑ x ∈ (K.erase w).filter (· ∈ B), f x := by
  rw [Finset.filter_erase]
  by_cases hwB : w ∈ B
  · rw [if_pos hwB, Finset.add_sum_erase _ _ (Finset.mem_filter.mpr ⟨hw, hwB⟩)]
  · rw [if_neg hwB, zero_add, Finset.erase_eq_of_notMem (fun h => hwB (Finset.mem_filter.mp h).2)]

/-- **The recursion of the B-mass**: `massB s r ρ = ∑_w ([w ∈ B] (1 − ρ p_r) p_w +
massB(C_w, w, 1 − ρ p_r))`. -/
theorem massB_rec (hG : G.IsAcyclic) {B : Finset V} {t : ℝ} (ht : 0 ≤ t) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (ρ : ℝ) :
    massB G B t s r ρ = ∑ w ∈ nbrsIn G s r,
      ((if w ∈ B then (1 - ρ * rootProb G t s r) * rootProb G t (compIn G (s.erase r) w) w
          else 0) +
        massB G B t (compIn G (s.erase r) w) w (1 - ρ * rootProb G t s r)) := by
  unfold massB
  have hset : (s.erase r).filter (· ∈ B) =
      (nbrsIn G s r).biUnion (fun w => (compIn G (s.erase r) w).filter (· ∈ B)) := by
    conv_lhs => rw [erase_eq_biUnion hs hr]
    rw [Finset.filter_biUnion]
  rw [hset, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro w hw
    have hwC := self_mem_branch hw
    rw [Finset.sum_congr rfl (fun x hx => mu_branch hG ht hr hw (Finset.mem_filter.mp hx).1 ρ)]
    rw [sum_filter_split B _ w hwC, mu_root hwC]
  · intro i hi j hj hij
    exact Finset.disjoint_filter_filter (disjoint_branches hG hi hj hij)

end Erdos993Lean.Analytic.Tail
