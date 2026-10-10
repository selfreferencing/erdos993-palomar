module

public import Erdos993Lean.Analytic.O2.Fold

/-!
# O2: the original-law records and the innovation identity

Source: the O2 proof, §1 (the
actual objects, the recursions `p/(λ(1−p)) = ∏(1 − p_u)`, `z = 1 − ∑ p_u z_u`, `r_root = 1`,
`r_v = 1 − π_parent`), Lemma 1 (the physical domain and the innovation identity (1)),
and its implementation map §2, obligations 1–2.

On a rooted vertex set `(s, r)` of an acyclic graph at activity `λ > 0` (with `rootProb` and the
moments `meanB`/`varB` with the counting set `univ`, i.e. the total count `K`):

* `zR G λ s r = 1 + U(s − N[r]) − U(s − r)`: the signed total-count response
  `E_f(K | r occupied) − E_f(K | r vacant)` of the subtree (no sign assumption);
* `port_univ_eq`: `U(s) − U(s − r) = p z`; **`zR_rec`**: `z = 1 − ∑_{w child} p_w z_w`;
* **`dfold_innov`** (identity (1) on a subtree with boundary `ρ`): the fold of the innovations
  `ρ_v p_v (1 − p_v) z_v²` is `ρ V(s) + (1 − ρ) V(s − r)`; at `ρ = 1` it is `Var K` of the subtree;
* `logMass_eq_Tmass`: `T = log(λ(1−p)/p)` is the children's total log-mass `∑_w −log(1 − p_w)`;
  `logG_eq`: `G(p) = y − T` with `y = −log(1 − p)`;
* `rootProb_le_parentBound`: the parent's cavity probability is at most `λ(1−p_w)/(1+λ(1−p_w))`;
* **`physRecord_child`**: the inherited record `(p_w, 1 − ρ p_r, p_r)` of every child is a
  `PhysRecord` (Lemma 1 and the retained-`Y` bound) as soon as `ρ ≤ 1` and `ρ(1 + λ(1 − p_r)) ≥ 1`;
  `PhysRecord.rho_le_one`, `PhysRecord.one_le_rho_mul` give these back.

Scalarity check.  `p, z, ρ, t` are fields of the actual rooted subtree (produced by `rootProb`,
`meanB` and the inherited parent fields of `dfold`); they are consumed by the local payment of the
same vertex and by the exact edge cancellations of `Ledger.lean`.  `V = varB` is the variance of the
actual total count.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.O2

open Finset Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

section Response

variable [Fintype V]

variable (G) in
/-- **The signed total-count response** of the rooted subtree `(s, r)`:
`z = E_f(K | r occupied) − E_f(K | r vacant) = 1 + U(s − N[r]) − U(s − r)`. -/
noncomputable def zR (lam : ℝ) (s : Finset V) (r : V) : ℝ :=
  1 + meanB G univ lam (outsideClosedNbhd G s r) - meanB G univ lam (s.erase r)

theorem aB_univ (r : V) : aB (univ : Finset V) r = 1 := by
  simp [aB]

/-- `U(s) − U(s − r) = p z`. -/
theorem port_univ_eq {lam : ℝ} (hl : 0 ≤ lam) {s : Finset V} {r : V} (hr : r ∈ s) :
    port G univ lam s r = rootProb G lam s r * zR G lam s r := by
  unfold port zR
  rw [meanB_root hl hr, aB_univ]
  ring

/-- **The response recursion** `z = 1 − ∑_{w child} p_w z_w`. -/
theorem zR_rec (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 ≤ lam) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    zR G lam s r = 1 - ∑ w ∈ nbrsIn G s r,
      rootProb G lam (compIn G (s.erase r) w) w * zR G lam (compIn G (s.erase r) w) w := by
  have h := mixture_gap (B := (univ : Finset V)) hG hl hs hr
  rw [aB_univ] at h
  rw [Finset.sum_congr rfl (fun w hw => (port_univ_eq hl (self_mem_branch hw)).symm)]
  unfold zR
  linarith

/-- A root without children has `z = 1`. -/
theorem zR_of_nbrsIn_empty (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 ≤ lam) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (h : nbrsIn G s r = ∅) : zR G lam s r = 1 := by
  rw [zR_rec hG hl hs hr, h, Finset.sum_empty, sub_zero]

/-- **The innovation identity (1)** on a subtree with boundary `ρ` (the probability that the parent
of the root is vacant): `∑_v ρ_v p_v (1 − p_v) z_v² = ρ V(s) + (1 − ρ) V(s − r)`, where `V` is the
variance of the total count. -/
theorem dfold_innov (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 ≤ lam) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (ρ t : ℝ) :
    dfold G lam (fun s v ρ _ => ρ * rootProb G lam s v * (1 - rootProb G lam s v) *
        zR G lam s v ^ 2) s r ρ t =
      ρ * varB G univ lam s + (1 - ρ) * varB G univ lam (s.erase r) := by
  refine rooted_induction hG (P := fun s r => ∀ ρ t : ℝ,
    dfold G lam (fun s v ρ _ => ρ * rootProb G lam s v * (1 - rootProb G lam s v) *
        zR G lam s v ^ 2) s r ρ t =
      ρ * varB G univ lam s + (1 - ρ) * varB G univ lam (s.erase r)) ?_ hs hr ρ t
  intro s r hs hr ih ρ t
  rw [dfold_eq _ _ hr, Finset.sum_congr rfl (fun w hw => ih w hw _ _), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← varB_erase_root hG hl hs hr,
    ← varB_outside_root hG hl hs hr, varB_root hl hr, aB_univ]
  unfold zR
  ring

end Response

/-! ### Log-masses -/

theorem one_sub_rootProb_pos {lam : ℝ} (hl : 0 ≤ lam) {s : Finset V} {r : V} (hr : r ∈ s) :
    0 < 1 - rootProb G lam s r := by
  have := rootProb_lt_one (G := G) hl hr
  linarith

/-- The product of the children's vacancy probabilities is `e^{−T}`. -/
theorem prod_one_sub_eq_exp (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 ≤ lam) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    ∏ w ∈ nbrsIn G s r, (1 - rootProb G lam (compIn G (s.erase r) w) w) =
      Real.exp (-Tmass G lam s r) := by
  rw [Tmass, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun w hw => ?_
  exact one_sub_rootProb_eq_exp hl (compIn_branch hG hs hr hw).2.1

/-- **`T = log(λ(1−p)/p)` is the children's total log-mass.** -/
theorem logMass_eq_Tmass (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    logMass lam (rootProb G lam s r) = Tmass G lam s r := by
  have hodds := rootProb_odds hG hl hs hr
  rw [prod_one_sub_eq_exp hG hl.le hs hr] at hodds
  have hp := rootProb_pos (G := G) hl s r
  have hq := one_sub_rootProb_pos (G := G) hl.le hr
  rw [div_eq_iff hq.ne'] at hodds
  have hE : Real.exp (Tmass G lam s r) * rootProb G lam s r = lam * (1 - rootProb G lam s r) := by
    calc Real.exp (Tmass G lam s r) * rootProb G lam s r
        = Real.exp (Tmass G lam s r) *
            (lam * Real.exp (-Tmass G lam s r) * (1 - rootProb G lam s r)) := by rw [← hodds]
      _ = lam * (1 - rootProb G lam s r) *
            (Real.exp (Tmass G lam s r) * Real.exp (-Tmass G lam s r)) := by ring
      _ = lam * (1 - rootProb G lam s r) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hkey : lam * (1 - rootProb G lam s r) / rootProb G lam s r = Real.exp (Tmass G lam s r) := by
    rw [div_eq_iff hp.ne', ← hE]
  rw [logMass, hkey, Real.log_exp]

/-- `G(p) = y − T`: `log(p/(λ(1−p)²)) = −log(1 − p) − log(λ(1−p)/p)`. -/
theorem logG_eq {lam p : ℝ} (hl : 0 < lam) (hp : 0 < p) (hp1 : p < 1) :
    logG lam p = -Real.log (1 - p) - logMass lam p := by
  have h1 : 0 < 1 - p := by linarith
  unfold logG logMass
  rw [Real.log_div hp.ne' (by positivity), Real.log_div (by positivity) hp.ne',
    Real.log_mul hl.ne' (by positivity), Real.log_mul hl.ne' h1.ne', Real.log_pow]
  push_cast
  ring

/-! ### The inherited physical record -/

/-- The parent's cavity probability is at most `λ(1 − p_w)/(1 + λ(1 − p_w))` for every child `w`
(the parent's child product contains `1 − p_w`). -/
theorem rootProb_le_parentBound (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) {w : V} (hw : w ∈ nbrsIn G s r) :
    rootProb G lam s r ≤ lam * (1 - rootProb G lam (compIn G (s.erase r) w) w) /
      (1 + lam * (1 - rootProb G lam (compIn G (s.erase r) w) w)) := by
  have hodds := rootProb_odds hG hl hs hr
  have hwC := (compIn_branch hG hs hr hw).2.1
  set pw := rootProb G lam (compIn G (s.erase r) w) w with hpw
  set p := rootProb G lam s r with hp
  have hpw1 : 0 < 1 - pw := one_sub_rootProb_pos hl.le hwC
  have hq : 0 < 1 - p := one_sub_rootProb_pos hl.le hr
  have hprod : ∏ w' ∈ nbrsIn G s r, (1 - rootProb G lam (compIn G (s.erase r) w') w') ≤ 1 - pw := by
    rw [← Finset.mul_prod_erase _ _ hw]
    refine mul_le_of_le_one_right hpw1.le ?_
    refine Finset.prod_le_one₀ (fun w' hw' => ?_) (fun w' hw' => ?_)
    · exact (one_sub_rootProb_pos hl.le
        (compIn_branch hG hs hr (Finset.mem_of_mem_erase hw')).2.1).le
    · have := rootProb_nonneg (G := G) hl.le (compIn G (s.erase r) w') w'
      linarith
  have h1 : p / (1 - p) ≤ lam * (1 - pw) := by
    rw [hodds]
    exact mul_le_mul_of_nonneg_left hprod hl.le
  rw [div_le_iff₀ hq] at h1
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem PhysRecord.rho_le_one {lam p r t : ℝ} (h : PhysRecord lam p r t) : r ≤ 1 := h.2.2.1

/-- A physical record has `r (1 + λ(1 − p)) ≥ 1` (Lemma 1's lower bound on `r`). -/
theorem PhysRecord.one_le_rho_mul {lam p r t : ℝ} (hl : 0 < lam) (h : PhysRecord lam p r t) :
    1 ≤ r * (1 + lam * (1 - p)) := by
  obtain ⟨hp0, hpq, _, h1, h2, _⟩ := h
  have hq : p < 1 := lt_of_le_of_lt hpq (by unfold actQ; rw [div_lt_one (by linarith)]; linarith)
  have hd : 0 < 1 + lam * (1 - p) := by nlinarith
  rw [le_div_iff₀ hd] at h2
  nlinarith

/-- **The inherited record of a child is physical** (Lemma 1 and the retained-`Y` bound). -/
theorem physRecord_child (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hρ0 : 1 ≤ ρ * (1 + lam * (1 - rootProb G lam s r))) {w : V} (hw : w ∈ nbrsIn G s r) :
    PhysRecord lam (rootProb G lam (compIn G (s.erase r) w) w) (1 - ρ * rootProb G lam s r)
      (rootProb G lam s r) := by
  have hwC := (compIn_branch hG hs hr hw).2.1
  have hbound := rootProb_le_parentBound hG hl hs hr hw
  set pw := rootProb G lam (compIn G (s.erase r) w) w with hpw
  set p := rootProb G lam s r with hp
  have hp0 : 0 < p := rootProb_pos hl s r
  have hp1 : 0 < 1 - p := one_sub_rootProb_pos hl.le hr
  have hρ : 0 ≤ ρ := by
    by_contra hneg
    push_neg at hneg
    have : ρ * (1 + lam * (1 - p)) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  refine ⟨rootProb_pos hl _ _, rootProb_le_actQ hl.le hwC, ?_, ?_, hbound, ?_⟩
  · nlinarith
  · nlinarith
  · have hd : 0 < 1 + lam * (1 - (1 - ρ * p)) := by nlinarith
    rw [le_div_iff₀ hd]
    nlinarith

end Erdos993Lean.Analytic.O2
