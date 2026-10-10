module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.Fallback

/-!
# The tail input T3, part 7: Lemma B (the mean of the free count, exactly)

Source: T23 §3, Lemma B, and
the per-unit proof §2:

  `m = E M = (1/q) ∑_{c ∈ C} (1 − π_c) s_c` (+ one for each isolated B-vertex),
  `s_c = ∑_{b ∈ ch_B(c)} p_b`, `π_c = r_c p_c`, `r_c = 1 − π_{parent(c)}`, `r_root = 1`,
  `r_c ≥ 1/(1 + λ(1 − p_c))`.

On a rooted tree `(s, r)` the top-down factor `r_c` is the parameter `ρ` of `mSum`, which is
passed to a child `w` as `1 − ρ p_r` (the probability that the parent `r` is unoccupied,
`mu_root`, `mu_branch` in `Tail/Marginal.lean`).

Main results:
* `sB`, `mSum` (by well-founded recursion): `mSum s r ρ = (1 − ρ p_r) s_r + ∑_w mSum(C_w, w, 1 − ρ p_r)`,
  i.e. `∑_c (1 − π_c) s_c` over the C-vertices of the tree (`s_r = 0` at a B-vertex);
* `lemmaB_tree` (**exact**): `massB s r ρ = mSum s r ρ`; with `ρ = 1` and a C-root this is
  `∑_{b ∈ B ∩ s} π_b(s) = ∑_c (1 − π_c) s_c`;
* `lemmaB_component`: for a component with a C-root `c`: `∑_{b ∈ B ∩ K} π_b = mSum K c 1`;
* `rmin_le_child` (**`r_c ≥ 1/(1 + λ(1 − p_c))`**): `1/(1 + t(1 − p_w)) ≤ 1 − ρ p_r` for every child
  `w` and `ρ ∈ [0, 1]`;
* `mSum_le_max`: replacing every `r_c` by its lower bound, `mSum ≤ ∑_c (1 − h(p_c)) s_c`,
  `h(p) = p/(1 + t(1 − p))` (the form consumed by Theorem T3-2).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- `s_r = ∑_{w ∈ ch_B(r)} p_w`. -/
noncomputable def sB (B : Finset V) (t : ℝ) (s : Finset V) (r : V) : ℝ :=
  ∑ w ∈ nbrsIn G s r, if w ∈ B then rootProb G t (compIn G (s.erase r) w) w else 0

-- `hr` is used by the termination proof only.
set_option linter.unusedVariables false in
variable (G) in
/-- `mSum s r ρ = ∑_{c ∈ C ∩ s} (1 − π_c) s_c` on the rooted tree `(s, r)`, where the root has
`π_r = ρ p_r` and each child `w` of a vertex `v` has `r_w = 1 − π_v`. -/
noncomputable def mSum (B : Finset V) (t : ℝ) (s : Finset V) (r : V) (ρ : ℝ) : ℝ :=
  if hr : r ∈ s then
    (1 - ρ * rootProb G t s r) * sB G B t s r +
      ∑ w ∈ (nbrsIn G s r).attach,
        mSum B t (compIn G (s.erase r) w.1) w.1 (1 - ρ * rootProb G t s r)
  else 0
termination_by s.card
decreasing_by
  exact lt_of_le_of_lt (Finset.card_le_card (compIn_subset _ _)) (Finset.card_erase_lt_of_mem hr)

section LemmaB

variable {B : Finset V} {t : ℝ}

theorem mSum_eq {s : Finset V} {r : V} (hr : r ∈ s) (ρ : ℝ) :
    mSum G B t s r ρ = (1 - ρ * rootProb G t s r) * sB G B t s r +
      ∑ w ∈ nbrsIn G s r, mSum G B t (compIn G (s.erase r) w) w (1 - ρ * rootProb G t s r) := by
  rw [mSum, dif_pos hr]
  congr 1
  exact Finset.sum_attach (nbrsIn G s r)
    (fun w => mSum G B t (compIn G (s.erase r) w) w (1 - ρ * rootProb G t s r))

theorem sB_nonneg (ht : 0 ≤ t) (s : Finset V) (r : V) : 0 ≤ sB G B t s r :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact rootProb_nonneg ht _ _
    · exact le_rfl

/-- At a B-vertex `s_r = 0` (the children of a B-vertex are C-vertices). -/
theorem sB_eq_zero (hB : IsIndepFinset G B) {s : Finset V} {r : V} (hrB : r ∈ B) :
    sB G B t s r = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  rw [if_neg]
  intro hwB
  exact hB r hrB w hwB (mem_nbrsIn.mp hw).2

/-- **Lemma B on a rooted tree (exact)**: `∑_{b ∈ B ∩ (s − r)} μ_b = ∑_c (1 − π_c) s_c`. -/
theorem lemmaB_tree (hG : G.IsAcyclic) (ht : 0 ≤ t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) (ρ : ℝ) : massB G B t s r ρ = mSum G B t s r ρ := by
  refine rooted_induction hG
    (P := fun s r => ∀ ρ : ℝ, massB G B t s r ρ = mSum G B t s r ρ) ?_ hs hr ρ
  intro s r hs hr ih ρ
  rw [massB_rec hG ht hs hr, mSum_eq hr, sB, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rw [ih w hw]
  congr 1
  split_ifs
  · rfl
  · rw [mul_zero]

/-- **Lemma B on a component**: for a C-vertex `c` of `K`,
`∑_{b ∈ B ∩ K} π_b(K) = ∑_{c' ∈ C ∩ K} (1 − π_{c'}) s_{c'}`. -/
theorem lemmaB_component (hG : G.IsAcyclic) (ht : 0 ≤ t) {K : Finset V} (hK : ConnectedIn G K)
    {c : V} (hc : c ∈ K) (hcB : c ∉ B) :
    ∑ b ∈ K.filter (· ∈ B), marg G t K b = mSum G B t K c 1 := by
  rw [sum_marg_eq_massB hcB, lemmaB_tree hG ht hK hc]

/-- **`r_w ≥ 1/(1 + λ(1 − p_w))`** (T23 Lemma B): for every child `w` of `r` and `ρ ∈ [0, 1]`,
the factor `1 − ρ p_r` passed to `w` is at least `1/(1 + t(1 − p_w))`. -/
theorem rmin_le_child (hG : G.IsAcyclic) (ht : 0 < t) {s : Finset V} (hs : ConnectedIn G s)
    {r w : V} (hr : r ∈ s) (hw : w ∈ nbrsIn G s r) {ρ : ℝ} (hρ1 : ρ ≤ 1) :
    1 / (1 + t * (1 - rootProb G t (compIn G (s.erase r) w) w)) ≤ 1 - ρ * rootProb G t s r := by
  have hodds := rootProb_odds hG ht hs hr
  have hp0 := rootProb_nonneg (G := G) ht.le s r
  have hp1 := rootProb_lt_one (G := G) ht.le hr
  have hw0 := rootProb_nonneg (G := G) ht.le (compIn G (s.erase r) w) w
  have hw1 := rootProb_lt_one (G := G) ht.le (self_mem_branch hw)
  -- the odds `R = p/(1 − p) = t ∏ (1 − p_u) ≤ t (1 − p_w)`
  have hprod : ∏ u ∈ nbrsIn G s r, (1 - rootProb G t (compIn G (s.erase r) u) u) ≤
      1 - rootProb G t (compIn G (s.erase r) w) w := by
    rw [← Finset.mul_prod_erase _ _ hw]
    have h1 : ∏ u ∈ (nbrsIn G s r).erase w, (1 - rootProb G t (compIn G (s.erase r) u) u) ≤ 1 :=
      Finset.prod_le_one₀
        (fun u hu => by
          linarith [rootProb_lt_one (G := G) ht.le (self_mem_branch (Finset.mem_of_mem_erase hu))])
        (fun u _ => by linarith [rootProb_nonneg (G := G) ht.le (compIn G (s.erase r) u) u])
    have h0 : 0 ≤ ∏ u ∈ (nbrsIn G s r).erase w, (1 - rootProb G t (compIn G (s.erase r) u) u) :=
      Finset.prod_nonneg (fun u hu => by
        linarith [rootProb_lt_one (G := G) ht.le (self_mem_branch (Finset.mem_of_mem_erase hu))])
    nlinarith
  have hR : rootProb G t s r / (1 - rootProb G t s r) ≤
      t * (1 - rootProb G t (compIn G (s.erase r) w) w) := by
    rw [hodds]
    exact mul_le_mul_of_nonneg_left hprod ht.le
  have h1p : 0 < 1 - rootProb G t s r := by linarith
  have hle : rootProb G t s r ≤
      t * (1 - rootProb G t (compIn G (s.erase r) w) w) * (1 - rootProb G t s r) :=
    (div_le_iff₀ h1p).mp hR
  -- `1 − p = 1/(1 + R) ≥ 1/(1 + t(1 − p_w))`, and `1 − ρ p ≥ 1 − p`
  have hD : 0 < 1 + t * (1 - rootProb G t (compIn G (s.erase r) w) w) := by nlinarith
  rw [div_le_iff₀ hD]
  have h2 : 1 ≤ (1 - rootProb G t s r) * (1 + t * (1 - rootProb G t (compIn G (s.erase r) w) w)) := by
    nlinarith [hle]
  have h3 : (1 - rootProb G t s r) * (1 + t * (1 - rootProb G t (compIn G (s.erase r) w) w)) ≤
      (1 - ρ * rootProb G t s r) * (1 + t * (1 - rootProb G t (compIn G (s.erase r) w) w)) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hD.le
  linarith

/-- The mean contribution with every `r_c` replaced by its lower bound `1/(1 + t(1 − p_c))`:
`(1 − h(p_c)) s_c`, `h(p) = p/(1 + t(1 − p))`. -/
noncomputable def hmin (t p : ℝ) : ℝ := p / (1 + t * (1 - p))

variable (G) in
/-- `∑_c (1 − h(p_c)) s_c` over the rooted tree. -/
noncomputable def mSumMax (B : Finset V) (t : ℝ) (s : Finset V) (r : V) : ℝ :=
  treeSum G (fun s r => (1 - hmin t (rootProb G t s r)) * sB G B t s r) s r

/-- **The worst `r_c` is the smallest** (T23 Theorem T3-2 proof): for `ρ` between the lower bound
`1/(1 + t(1 − p_r))` and `1`, `mSum s r ρ ≤ ∑_c (1 − h(p_c)) s_c`. -/
theorem mSum_le_max (hG : G.IsAcyclic) (ht : 0 < t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) {ρ : ℝ} (hρ0 : 1 / (1 + t * (1 - rootProb G t s r)) ≤ ρ)
    (hρ1 : ρ ≤ 1) : mSum G B t s r ρ ≤ mSumMax G B t s r := by
  refine rooted_induction hG (P := fun s r => ∀ ρ : ℝ,
    1 / (1 + t * (1 - rootProb G t s r)) ≤ ρ → ρ ≤ 1 → mSum G B t s r ρ ≤ mSumMax G B t s r)
    ?_ hs hr ρ hρ0 hρ1
  intro s r hs hr ih ρ hρ0 hρ1
  unfold mSumMax
  rw [mSum_eq hr, treeSum_eq _ hr]
  have hp0 := rootProb_nonneg (G := G) ht.le s r
  have hp1 := rootProb_lt_one (G := G) ht.le hr
  have hD : 0 < 1 + t * (1 - rootProb G t s r) := by nlinarith
  apply add_le_add
  · -- `1 − ρ p ≤ 1 − h(p)` since `ρ ≥ 1/(1 + t(1 − p))`
    apply mul_le_mul_of_nonneg_right _ (sB_nonneg ht.le s r)
    unfold hmin
    have : rootProb G t s r / (1 + t * (1 - rootProb G t s r)) =
        1 / (1 + t * (1 - rootProb G t s r)) * rootProb G t s r := by ring
    rw [this]
    nlinarith
  · apply Finset.sum_le_sum
    intro w hw
    have hρ'1 : 1 - ρ * rootProb G t s r ≤ 1 := by
      have : 0 ≤ ρ := le_trans (by positivity) hρ0
      nlinarith
    exact ih w hw _ (rmin_le_child hG ht hs hr hw hρ1) hρ'1

theorem one_div_le_one_of_rootProb (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    1 / (1 + t * (1 - rootProb G t s r)) ≤ 1 := by
  have hp1 := rootProb_le_one (G := G) ht hr
  rw [div_le_one (by nlinarith)]
  nlinarith

end LemmaB

end Erdos993Lean.Analytic.Tail
