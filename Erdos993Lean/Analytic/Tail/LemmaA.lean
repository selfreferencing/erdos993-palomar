module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.Rooted

/-!
# The tail input T3, part 3: Lemma A (toy-unit domination), for every `z ∈ [0, 1]`

Source: T23 §3, Lemma A.


Fix an independent set `B` of the acyclic graph `G`, an activity `t ≥ 0` and `z ∈ [0, 1]`.
For a vertex set `s`, `phiF G B t z s = E_{G[s]}[z^{K_B}]` (`K_B = |S ∩ B|`, `S` the hard-core set
of `G[s]` at activity `t`) is the ratio `Z(t on C, t z on B)(s) / Z_t(s)`.  For a rooted connected
vertex set `(s, r)` with children `w` and branches `C_w`:

* `betaB s r = ∏_{w ∈ ch_B(r)} (1 − (1 − z) p_w)` (T23's `β`), `tauC s r = p_r + (1 − p_r) β`
  (T23's toy factor `τ`), and `toy s r = ∏_{c ∈ C ∩ s} τ_c` (over the rooted tree, `treeProd`);
* `zetaF s r = p_r z^{[r ∈ B]} + (1 − p_r) β`: equal to `τ` at a C-root and to `1 − (1 − z) p_r`
  at a B-root (there `β = 1`, since `B` is independent).

Main results:
* `phiF_rooted` (exact): `Φ^f(s) = p z^{[r ∈ B]} Φ^f(s − N[r]) + (1 − p) Φ^f(s − r)`, and the
  products `phiF_erase_root`, `phiF_outside_root` over the branches (`Φ^b_r = ∏_w Φ^f_w`);
* `lemmaA_tree` (**T23 Lemma A, induction claims**): `Φ^f(s − r) ≤ β · Toy_r` and
  `Φ^f(s) ≤ ζ · Toy_r`, with `Toy_r = ∏_w toy(C_w, w)` the product of `τ` over the C-vertices
  strictly below `r`; hence `phiF_le_toy`: `E_{G[s]}[z^{K_B}] ≤ ∏_{c ∈ C ∩ s} τ_c` (any root);
* `lemmaA_forest`: for every vertex set `s`, `E_{G[s]}[z^{K_B}]` is at most the product over the
  components `K` of `G[s]` of `toy(K, c_K)` (`c_K` a C-vertex of `K`) or, for a component inside
  `B` (an isolated B-vertex), `1 − (1 − z) q` (`compProd`, `compToy`).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Components of `G[s]` -/

omit [DecidableRel G.Adj] in
/-- A component `compIn G s x` has no edges to the rest of `s`. -/
theorem not_adj_compIn_sdiff {s : Finset V} {x a b : V} (ha : a ∈ compIn G s x)
    (hb : b ∈ s \ compIn G s x) : ¬ G.Adj a b := by
  intro hab
  rw [Finset.mem_sdiff] at hb
  exact hb.2 (mem_compIn_of_adjIn ha ⟨compIn_subset _ _ ha, hb.1, hab⟩)

omit [DecidableRel G.Adj] in
theorem compIn_union_sdiff (s : Finset V) (x : V) : compIn G s x ∪ (s \ compIn G s x) = s :=
  Finset.union_sdiff_of_subset (compIn_subset _ _)

/-- `Z` factors over a component and the rest. -/
theorem Zw_comp_split (wt : V → ℝ) (s : Finset V) (x : V) :
    Zw G wt s = Zw G wt (compIn G s x) * Zw G wt (s \ compIn G s x) := by
  conv_lhs => rw [← compIn_union_sdiff (G := G) s x]
  exact Zw_union wt Finset.disjoint_sdiff (fun a ha b hb => not_adj_compIn_sdiff ha hb)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A connected vertex set inside an independent set is a single vertex. -/
theorem eq_singleton_of_subset_indep {B : Finset V} (hB : IsIndepFinset G B) {K : Finset V}
    (hK : ConnectedIn G K) (hKB : K ⊆ B) {x : V} (hx : x ∈ K) : K = {x} := by
  ext y
  rw [Finset.mem_singleton]
  constructor
  · intro hy
    have h := hK x hx y hy
    induction h with
    | refl => rfl
    | tail _ hcd _ => exact absurd hcd.2.2 (hB _ (hKB hcd.1) _ (hKB hcd.2.1))
  · rintro rfl
    exact hx

set_option linter.unusedVariables false in
variable (G) in
/-- The product of `g` over the connected components of `G[s]`. -/
noncomputable def compProd (g : Finset V → ℝ) (s : Finset V) : ℝ :=
  if h : s.Nonempty then g (compIn G s h.choose) * compProd g (s \ compIn G s h.choose) else 1
termination_by s.card
decreasing_by
  exact Finset.card_lt_card (Finset.sdiff_ssubset (compIn_subset _ _)
    ⟨h.choose, self_mem_compIn h.choose_spec⟩)

omit [DecidableRel G.Adj] in
theorem compProd_eq (g : Finset V → ℝ) {s : Finset V} (h : s.Nonempty) :
    compProd G g s = g (compIn G s h.choose) * compProd G g (s \ compIn G s h.choose) := by
  rw [compProd, dif_pos h]

omit [DecidableRel G.Adj] in
theorem compProd_empty (g : Finset V → ℝ) : compProd G g ∅ = 1 := by
  rw [compProd, dif_neg Finset.not_nonempty_empty]

/-! ### The Laplace transform of `K_B` on a vertex set -/

section Laplace

variable (B : Finset V) (t z : ℝ)

/-- The Laplace weights: activity `t` on `C = Bᶜ` and `t z` on `B`. -/
def lapW : V → ℝ := fun v => if v ∈ B then t * z else t

variable (G) in
/-- `Φ^f(s) = E_{G[s]}[z^{K_B}] = Z(t on C, t z on B)(s) / Z_t(s)`. -/
noncomputable def phiF (s : Finset V) : ℝ :=
  Zw G (lapW B t z) s / Zw G (fun _ => t) s

variable {B t z}

theorem lapW_nonneg (ht : 0 ≤ t) (hz : 0 ≤ z) (v : V) : 0 ≤ lapW B t z v := by
  unfold lapW
  split_ifs
  · exact mul_nonneg ht hz
  · exact ht

theorem lapW_le (ht : 0 ≤ t) (hz1 : z ≤ 1) (v : V) : lapW B t z v ≤ t := by
  unfold lapW
  split_ifs
  · nlinarith
  · exact le_rfl

theorem lapW_eq (v : V) : lapW B t z v = t * (if v ∈ B then z else 1) := by
  unfold lapW
  split_ifs <;> ring

theorem phiF_nonneg (ht : 0 ≤ t) (hz : 0 ≤ z) (s : Finset V) : 0 ≤ phiF G B t z s :=
  div_nonneg (Zw_nonneg (lapW_nonneg ht hz) s) (Zw_nonneg (fun _ => ht) s)

theorem phiF_le_one (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (s : Finset V) :
    phiF G B t z s ≤ 1 :=
  div_le_one_of_le₀ (Zw_le_Zw (lapW_nonneg ht hz0) (lapW_le ht hz1) s) (Zw_nonneg (fun _ => ht) s)

theorem phiF_empty : phiF G B t z ∅ = 1 := by
  rw [phiF, Zw_empty, Zw_empty, div_one]

/-- `Φ^f` of a single vertex: `(1 + t z^{[v ∈ B]}) / (1 + t)`. -/
theorem phiF_singleton (v : V) : phiF G B t z {v} = (1 + lapW B t z v) / (1 + t) := by
  rw [phiF, Zw_singleton, Zw_singleton]

/-- `Φ^f` factors over a component of `G[s]` and the rest. -/
theorem phiF_comp_split (s : Finset V) (x : V) :
    phiF G B t z s = phiF G B t z (compIn G s x) * phiF G B t z (s \ compIn G s x) := by
  rw [phiF, phiF, phiF, Zw_comp_split _ s x, Zw_comp_split (fun _ => t) s x, mul_div_mul_comm]

/-- **The exact recursion at a vertex** (T23 Lemma A):
`Φ^f(s) = p z^{[r ∈ B]} Φ^f(s − N[r]) + (1 − p) Φ^f(s − r)`. -/
theorem phiF_rooted (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    phiF G B t z s =
      rootProb G t s r * (if r ∈ B then z else 1) * phiF G B t z (outsideClosedNbhd G s r) +
        (1 - rootProb G t s r) * phiF G B t z (s.erase r) := by
  have hZ := Zw_pos (G := G) (fun _ => ht) s
  have hZe := Zw_pos (G := G) (fun _ => ht) (s.erase r)
  have hZo := Zw_pos (G := G) (fun _ => ht) (outsideClosedNbhd G s r)
  have hZ' := hZ.ne'
  have hZe' := hZe.ne'
  have hZo' := hZo.ne'
  rw [one_sub_rootProb ht hr]
  unfold phiF rootProb
  rw [Zw_erase_add (lapW B t z) hr, lapW_eq]
  field_simp
  ring

/-- `Φ^b_r = Φ^f(s − r) = ∏_w Φ^f(C_w)`. -/
theorem phiF_erase_root (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s) {r : V}
    (hr : r ∈ s) :
    phiF G B t z (s.erase r) = ∏ w ∈ nbrsIn G s r, phiF G B t z (compIn G (s.erase r) w) := by
  unfold phiF
  rw [Zw_erase_root hG _ hs hr, Zw_erase_root hG _ hs hr, Finset.prod_div_distrib]

/-- `Φ^f(s − N[r]) = ∏_w Φ^f(C_w − w) = ∏_w Φ^b_w`. -/
theorem phiF_outside_root (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s) {r : V}
    (hr : r ∈ s) :
    phiF G B t z (outsideClosedNbhd G s r) =
      ∏ w ∈ nbrsIn G s r, phiF G B t z ((compIn G (s.erase r) w).erase w) := by
  unfold phiF
  rw [Zw_outside_root hG _ hs hr, Zw_outside_root hG _ hs hr, Finset.prod_div_distrib]

end Laplace

/-! ### The toy units -/

section Toy

variable (B : Finset V) (t z : ℝ)

variable (G) in
/-- `β(s, r) = ∏_{w ∈ ch_B(r)} (1 − (1 − z) p_w)` (a factor `1` for the children outside `B`). -/
noncomputable def betaB (s : Finset V) (r : V) : ℝ :=
  ∏ w ∈ nbrsIn G s r,
    if w ∈ B then 1 - (1 - z) * rootProb G t (compIn G (s.erase r) w) w else 1

variable (G) in
/-- The toy factor `τ(s, r) = p_r + (1 − p_r) β(s, r)` (T23 Lemma A). -/
noncomputable def tauC (s : Finset V) (r : V) : ℝ :=
  rootProb G t s r + (1 - rootProb G t s r) * betaB G B t z s r

variable (G) in
/-- `ζ(s, r) = p_r z^{[r ∈ B]} + (1 − p_r) β(s, r)`. -/
noncomputable def zetaF (s : Finset V) (r : V) : ℝ :=
  rootProb G t s r * (if r ∈ B then z else 1) + (1 - rootProb G t s r) * betaB G B t z s r

variable (G) in
/-- The local factor of the toy product: `τ` at C-vertices, `1` at B-vertices. -/
noncomputable def toyLocal (s : Finset V) (r : V) : ℝ :=
  if r ∈ B then 1 else tauC G B t z s r

variable (G) in
/-- **The toy product** `∏_{c ∈ C ∩ s} τ_c` over the rooted vertex set `(s, r)`. -/
noncomputable def toy (s : Finset V) (r : V) : ℝ :=
  treeProd G (toyLocal G B t z) s r

variable {B t z}

theorem one_sub_mul_nonneg {p : ℝ} (hz1 : z ≤ 1) (hp1 : p ≤ 1) (hz0 : 0 ≤ z) :
    0 ≤ 1 - (1 - z) * p := by nlinarith

theorem betaB_nonneg (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (s : Finset V) (r : V) :
    0 ≤ betaB G B t z s r := by
  apply Finset.prod_nonneg
  intro w hw
  split_ifs
  · exact one_sub_mul_nonneg hz1 (rootProb_le_one ht (self_mem_branch hw)) hz0
  · exact zero_le_one

theorem betaB_le_one (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (s : Finset V) (r : V) :
    betaB G B t z s r ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro w hw
    split_ifs
    · exact one_sub_mul_nonneg hz1 (rootProb_le_one ht (self_mem_branch hw)) hz0
    · exact zero_le_one
  · intro w _
    split_ifs
    · nlinarith [rootProb_nonneg (G := G) ht (compIn G (s.erase r) w) w]
    · exact le_rfl

/-- At a B-vertex, `β = 1` (its children are outside the independent set `B`). -/
theorem betaB_eq_one (hB : IsIndepFinset G B) {s : Finset V} {r : V} (hrB : r ∈ B) :
    betaB G B t z s r = 1 := by
  apply Finset.prod_eq_one
  intro w hw
  rw [if_neg]
  intro hwB
  exact hB r hrB w hwB (mem_nbrsIn.mp hw).2

theorem tauC_nonneg (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) {s : Finset V} {r : V}
    (hr : r ∈ s) : 0 ≤ tauC G B t z s r :=
  add_nonneg (rootProb_nonneg ht s r)
    (mul_nonneg (by linarith [rootProb_le_one (G := G) ht hr]) (betaB_nonneg ht hz0 hz1 s r))

theorem tauC_le_one (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) {s : Finset V} {r : V}
    (hr : r ∈ s) : tauC G B t z s r ≤ 1 := by
  unfold tauC
  have h1 := rootProb_le_one (G := G) ht hr
  have h2 := betaB_le_one (G := G) (B := B) ht hz0 hz1 s r
  nlinarith

theorem betaB_le_tauC (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (s : Finset V) (r : V) :
    betaB G B t z s r ≤ tauC G B t z s r := by
  unfold tauC
  have h0 := rootProb_nonneg (G := G) ht s r
  have h2 := betaB_le_one (G := G) (B := B) ht hz0 hz1 s r
  nlinarith

theorem toyLocal_nonneg (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) {s : Finset V} {r : V}
    (hr : r ∈ s) : 0 ≤ toyLocal G B t z s r := by
  unfold toyLocal
  split_ifs
  · exact zero_le_one
  · exact tauC_nonneg ht hz0 hz1 hr

theorem toyLocal_le_one (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) {s : Finset V} {r : V}
    (hr : r ∈ s) : toyLocal G B t z s r ≤ 1 := by
  unfold toyLocal
  split_ifs
  · exact le_rfl
  · exact tauC_le_one ht hz0 hz1 hr

theorem toy_eq {s : Finset V} {r : V} (hr : r ∈ s) :
    toy G B t z s r =
      toyLocal G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w :=
  treeProd_eq _ hr

theorem toy_nonneg (hG : G.IsAcyclic) (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) : 0 ≤ toy G B t z s r :=
  treeProd_nonneg hG (fun _ _ _ hr => toyLocal_nonneg ht hz0 hz1 hr) hs hr

theorem toy_le_one (hG : G.IsAcyclic) (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) : toy G B t z s r ≤ 1 := by
  refine rooted_induction hG (P := fun s r => toy G B t z s r ≤ 1) ?_ hs hr
  intro s r hs hr ih
  rw [toy_eq hr]
  have h0 : ∀ w ∈ nbrsIn G s r, 0 ≤ toy G B t z (compIn G (s.erase r) w) w := fun w hw =>
    toy_nonneg hG ht hz0 hz1 (compIn_branch hG hs hr hw).1 (compIn_branch hG hs hr hw).2.1
  have h1 : ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w ≤ 1 :=
    Finset.prod_le_one₀ h0 ih
  have h2 := toyLocal_le_one (B := B) (z := z) (G := G) ht hz0 hz1 hr
  have h3 := toyLocal_nonneg (B := B) (z := z) (G := G) ht hz0 hz1 hr
  have h4 : 0 ≤ ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w := Finset.prod_nonneg h0
  nlinarith

/-- `ζ · Toy = (1 − (1 − z) p)^{[r ∈ B]} · toy`. -/
theorem zetaF_mul_below (hB : IsIndepFinset G B) {s : Finset V} {r : V} (hr : r ∈ s) :
    zetaF G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w =
      (if r ∈ B then 1 - (1 - z) * rootProb G t s r else 1) * toy G B t z s r := by
  rw [toy_eq hr]
  unfold zetaF toyLocal tauC
  by_cases hrB : r ∈ B
  · simp only [if_pos hrB, betaB_eq_one hB hrB]
    ring
  · simp only [if_neg hrB]
    ring

/-- `β · Toy ≤ toy`. -/
theorem betaB_mul_below_le (hB : IsIndepFinset G B) (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    {s : Finset V} {r : V} (hr : r ∈ s)
    (h0 : 0 ≤ ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w) :
    betaB G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w ≤
      toy G B t z s r := by
  rw [toy_eq hr]
  unfold toyLocal
  by_cases hrB : r ∈ B
  · rw [if_pos hrB, betaB_eq_one hB hrB]
  · rw [if_neg hrB]
    exact mul_le_mul_of_nonneg_right (betaB_le_tauC ht hz0 hz1 s r) h0

/-- **T23 Lemma A, the induction claims.**  For a rooted connected vertex set `(s, r)`, with
`Toy_r = ∏_w toy(C_w, w)` the product of the toy factors `τ` over the C-vertices strictly below
`r`: `Φ^b_r = Φ^f(s − r) ≤ β · Toy_r` and `Φ^f(s) ≤ ζ · Toy_r` (`ζ = τ` at a C-root,
`ζ = 1 − (1 − z) p_r` at a B-root). -/
theorem lemmaA_tree (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (ht : 0 ≤ t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    phiF G B t z (s.erase r) ≤
        betaB G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w ∧
      phiF G B t z s ≤
        zetaF G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w := by
  refine rooted_induction hG (P := fun s r =>
    phiF G B t z (s.erase r) ≤
        betaB G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w ∧
      phiF G B t z s ≤
        zetaF G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w) ?_ hs hr
  intro s r hs hr ih
  have hp0 : 0 ≤ rootProb G t s r := rootProb_nonneg ht s r
  have hp1 : rootProb G t s r ≤ 1 := rootProb_le_one ht hr
  have hmem : ∀ w ∈ nbrsIn G s r,
      ConnectedIn G (compIn G (s.erase r) w) ∧ w ∈ compIn G (s.erase r) w :=
    fun w hw => ⟨(compIn_branch hG hs hr hw).1, (compIn_branch hG hs hr hw).2.1⟩
  have htoy0 : ∀ w ∈ nbrsIn G s r, 0 ≤ toy G B t z (compIn G (s.erase r) w) w :=
    fun w hw => toy_nonneg hG ht hz0 hz1 (hmem w hw).1 (hmem w hw).2
  have hbelow0 : 0 ≤ ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w :=
    Finset.prod_nonneg htoy0
  -- part (i): `Φ^b_r ≤ β · Toy_r`
  have hi : phiF G B t z (s.erase r) ≤
      betaB G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w := by
    rw [phiF_erase_root hG hs hr]
    calc ∏ w ∈ nbrsIn G s r, phiF G B t z (compIn G (s.erase r) w)
        ≤ ∏ w ∈ nbrsIn G s r, (zetaF G B t z (compIn G (s.erase r) w) w *
            ∏ u ∈ nbrsIn G (compIn G (s.erase r) w) w,
              toy G B t z (compIn G ((compIn G (s.erase r) w).erase w) u) u) :=
          Finset.prod_le_prod₀ (fun w _ => phiF_nonneg ht hz0 _) (fun w hw => (ih w hw).2)
      _ = ∏ w ∈ nbrsIn G s r,
            ((if w ∈ B then 1 - (1 - z) * rootProb G t (compIn G (s.erase r) w) w else 1) *
              toy G B t z (compIn G (s.erase r) w) w) :=
          Finset.prod_congr rfl (fun w hw => zetaF_mul_below hB (hmem w hw).2)
      _ = betaB G B t z s r * ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w := by
          rw [Finset.prod_mul_distrib]
          rfl
  refine ⟨hi, ?_⟩
  -- part (ii): `Φ^f(s) ≤ ζ · Toy_r`
  have hout : phiF G B t z (outsideClosedNbhd G s r) ≤
      ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w := by
    rw [phiF_outside_root hG hs hr]
    apply Finset.prod_le_prod₀ (fun w _ => phiF_nonneg ht hz0 _)
    intro w hw
    have hb0 : 0 ≤ ∏ u ∈ nbrsIn G (compIn G (s.erase r) w) w,
        toy G B t z (compIn G ((compIn G (s.erase r) w).erase w) u) u := by
      apply Finset.prod_nonneg
      intro u hu
      obtain ⟨hC, hwC, _⟩ := compIn_branch hG (hmem w hw).1 (hmem w hw).2 hu
      exact toy_nonneg hG ht hz0 hz1 hC hwC
    exact (ih w hw).1.trans (betaB_mul_below_le hB ht hz0 hz1 (hmem w hw).2 hb0)
  have hzr : 0 ≤ (if r ∈ B then z else 1) := by
    split_ifs
    · exact hz0
    · exact zero_le_one
  rw [phiF_rooted ht hr]
  unfold zetaF
  calc rootProb G t s r * (if r ∈ B then z else 1) * phiF G B t z (outsideClosedNbhd G s r) +
        (1 - rootProb G t s r) * phiF G B t z (s.erase r)
      ≤ rootProb G t s r * (if r ∈ B then z else 1) *
            ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w +
          (1 - rootProb G t s r) * (betaB G B t z s r *
            ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w) :=
        add_le_add (mul_le_mul_of_nonneg_left hout (mul_nonneg hp0 hzr))
          (mul_le_mul_of_nonneg_left hi (by linarith))
    _ = (rootProb G t s r * (if r ∈ B then z else 1) +
          (1 - rootProb G t s r) * betaB G B t z s r) *
          ∏ w ∈ nbrsIn G s r, toy G B t z (compIn G (s.erase r) w) w := by ring

/-- **T23 Lemma A (tree form)**: for a rooted connected vertex set `(s, r)`,
`E_{G[s]}[z^{K_B}] ≤ ∏_{c ∈ C ∩ s} τ_c` (the toy product; any root). -/
theorem phiF_le_toy (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (ht : 0 ≤ t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    phiF G B t z s ≤ toy G B t z s r := by
  have h := (lemmaA_tree hG hB ht hz0 hz1 hs hr).2
  rw [zetaF_mul_below hB hr] at h
  have htoy := toy_nonneg (B := B) (z := z) hG ht hz0 hz1 hs hr
  refine h.trans ?_
  split_ifs
  · have := one_sub_mul_nonneg hz1 (rootProb_le_one (G := G) ht hr) hz0
    have h2 : 1 - (1 - z) * rootProb G t s r ≤ 1 := by
      nlinarith [rootProb_nonneg (G := G) ht s r]
    nlinarith
  · linarith

end Toy

/-! ### The forest form of Lemma A -/

section Forest

variable (B : Finset V) (t z : ℝ)

variable (G) in
/-- The Lemma A factor of a component `K` of `G[s]`: the toy product `∏_{c ∈ C ∩ K} τ_c` rooted at
a C-vertex of `K`, or `∏_{b ∈ K} (1 − (1 − z) q)` if `K ⊆ B` (then `K` is one isolated B-vertex). -/
noncomputable def compToy (K : Finset V) : ℝ :=
  if h : ∃ c ∈ K, c ∉ B then toy G B t z K h.choose else ∏ _b ∈ K, (1 - (1 - z) * actQ t)

variable {B t z}

theorem one_sub_mul_actQ (ht : 0 ≤ t) : 1 - (1 - z) * actQ t = (1 + t * z) / (1 + t) := by
  unfold actQ
  have : (1 + t) ≠ 0 := by linarith
  field_simp
  ring

theorem compToy_nonneg (hG : G.IsAcyclic) (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    {K : Finset V} (hK : ConnectedIn G K) : 0 ≤ compToy G B t z K := by
  unfold compToy
  split_ifs with h
  · exact toy_nonneg hG ht hz0 hz1 hK h.choose_spec.1
  · apply Finset.prod_nonneg
    intro _ _
    rw [one_sub_mul_actQ ht]
    positivity

/-- **T23 Lemma A (forest form)**: for every vertex set `s`, `E_{G[s]}[z^{K_B}]` is at most the
product over the components of `G[s]` of the toy products `∏_{c ∈ C ∩ K} τ_c`, an isolated
B-vertex contributing `1 − (1 − z) q`. -/
theorem lemmaA_forest (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (ht : 0 ≤ t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) (s : Finset V) : phiF G B t z s ≤ compProd G (compToy G B t z) s := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hne : s.Nonempty
    · set x := hne.choose with hx
      have hxs : x ∈ s := hne.choose_spec
      set K := compIn G s x with hK
      have hKc : ConnectedIn G K := connectedIn_compIn _ _
      have hxK : x ∈ K := self_mem_compIn hxs
      have hsub : s \ K ⊂ s := Finset.sdiff_ssubset (compIn_subset _ _) ⟨x, hxK⟩
      rw [compProd_eq _ hne, phiF_comp_split s x]
      have h1 : phiF G B t z K ≤ compToy G B t z K := by
        unfold compToy
        split_ifs with h
        · exact phiF_le_toy hG hB ht hz0 hz1 hKc h.choose_spec.1
        · push_neg at h
          have hKB : K ⊆ B := fun c hc => h c hc
          rw [eq_singleton_of_subset_indep hB hKc hKB hxK, Finset.prod_singleton, phiF_singleton,
            one_sub_mul_actQ ht]
          unfold lapW
          rw [if_pos (hKB hxK)]
      exact mul_le_mul h1 (ih _ hsub) (phiF_nonneg ht hz0 _) (compToy_nonneg hG ht hz0 hz1 hKc)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [phiF_empty, compProd_empty]

end Forest

end Erdos993Lean.Analytic.Tail
