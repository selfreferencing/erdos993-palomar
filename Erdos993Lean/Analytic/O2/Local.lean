module

public import Erdos993Lean.Analytic.O2.Source
public import Erdos993Lean.Analytic.O2.Packing
public import Erdos993Lean.Analytic.O2.Basic

/-!
# O2: the local ledger at one vertex

Source: the O2 proof, §4
(Lemma 3: consumed-credit conservation, every child receipt is "precisely the negative entry received
by its own original child from v, once"), §5 (the payment (11)) and Theorem 5 (the eight-term ledger
(22), the residuals `Δ_u, Δ_v, Δ_s` of (20)–(21)).

**Scalar level.**  The payment of a nonroot record splits into an own part and an incoming part
(the charges that use the parent's fields `t`, `1 − r = π_parent`):
`p Φ(p, r, t, z) = ownR(p, z, r) − incR(p, z, r, t)` (`BandData.pay_eq`), and for a root
`p PhiRoot(p, z) = ownR(p, z, 1) − ℓ y` (`BandData.payRoot_eq`, `y = −log(1 − p)`).

**Tree level.**  At a vertex `v` of a rooted subtree with inherited `(ρ, t)`, the own part minus the
incoming parts of its children (inherited `(1 − ρ p_v, p_v)`) is the local ledger
(`BandData.own_sub_inc_eq`):

  `ownR_v − ∑_{w child} incR_w = c ρ p g − ρ p(1−p) z² − u(p) Δ_u − v(p) Δ_v − ρ p s(p) Δ_s − w ρ p Δ_w`,

where `Δ_u = ∑ p_w h_w (z_w)₋² − (z_v − 1)₊²/T`, `Δ_v = ∑ p_w h_w (z_w)₊² − (1 − z_v)₊²/T`,
`Δ_s = ∑ p_w (1 − p_w) z_w² − (1 − z_v)²/H`, `Δ_w = ∑ p_w − φ` (the `τ` receipts cancel exactly by
`z = 1 − ∑ p_w z_w`, the logarithmic receipts by `T = ∑ y_w`).  **`dU_nonneg`, `dV_nonneg`,
`dS_nonneg`, `dW_nonneg`**: the four residuals are nonnegative (Cauchy with the actual child masses,
and the packing bounds (7), (8)).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.O2

open Finset Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve

/-! ### Scalar level -/

namespace BandData

variable (b : BandData)

/-- The own part of `p Φ` (no parent field). -/
noncomputable def ownR (lam p z ρ : ℝ) : ℝ :=
  b.price lam * ρ * p * src lam p ρ - ρ * p * (1 - p) * z ^ 2 +
    b.uF lam p * (max (z - 1) 0) ^ 2 / logMass lam p +
    b.vF lam p * (max (1 - z) 0) ^ 2 / logMass lam p +
    ρ * p * b.sF lam p * (1 - z) ^ 2 / packH lam p + ρ * p * b.tauF lam p * (z - 1) +
    b.wF lam * (ρ * p * (z - 1 + packPhi lam p)) + b.ellF lam * logMass lam p

/-- The incoming part of `p Φ`: the charges that use the parent's fields. -/
noncomputable def incR (lam p z ρ t : ℝ) : ℝ :=
  p * b.uF lam t * hFun p * (max (-z) 0) ^ 2 + p * b.vF lam t * hFun p * (max z 0) ^ 2 +
    (1 - ρ) * p * b.sF lam t * (1 - p) * z ^ 2 - (1 - ρ) * p * b.tauF lam t * z +
    b.wF lam * ((1 - ρ) * p * (1 - z)) + b.ellF lam * (-Real.log (1 - p))

/-- **`p Φ = own − incoming`**. -/
theorem pay_eq {lam p : ℝ} (hl : 0 < lam) (hp : 0 < p) (hp1 : p < 1) (ρ t z : ℝ) :
    p * b.Phi lam p ρ t z = b.ownR lam p z ρ - b.incR lam p z ρ t := by
  have hp0 : p ≠ 0 := hp.ne'
  have e1 : p * (b.uF lam p * (max (z - 1) 0) ^ 2 / (p * logMass lam p)) =
      b.uF lam p * (max (z - 1) 0) ^ 2 / logMass lam p := by
    rw [mul_div_assoc', mul_div_mul_left _ _ hp0]
  have e2 : p * (b.vF lam p * (max (1 - z) 0) ^ 2 / (p * logMass lam p)) =
      b.vF lam p * (max (1 - z) 0) ^ 2 / logMass lam p := by
    rw [mul_div_assoc', mul_div_mul_left _ _ hp0]
  have e3 : p * (b.ellF lam * logG lam p / p) = b.ellF lam * logG lam p := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hp0]
  have e4 : logG lam p = -Real.log (1 - p) - logMass lam p := logG_eq hl hp hp1
  unfold Phi Ru Rv Rs Rtau Rw ownR incR
  linear_combination e1 + e2 - e3 - b.ellF lam * e4

/-- **`p PhiRoot = own(r = 1) − ℓ y`**, `y = −log(1 − p)`. -/
theorem payRoot_eq {lam p : ℝ} (hl : 0 < lam) (hp : 0 < p) (hp1 : p < 1) (z : ℝ) :
    p * b.PhiRoot lam p z = b.ownR lam p z 1 - b.ellF lam * (-Real.log (1 - p)) := by
  have hp0 : p ≠ 0 := hp.ne'
  have e1 : p * (b.uF lam p * (max (z - 1) 0) ^ 2 / (p * logMass lam p)) =
      b.uF lam p * (max (z - 1) 0) ^ 2 / logMass lam p := by
    rw [mul_div_assoc', mul_div_mul_left _ _ hp0]
  have e2 : p * (b.vF lam p * (max (1 - z) 0) ^ 2 / (p * logMass lam p)) =
      b.vF lam p * (max (1 - z) 0) ^ 2 / logMass lam p := by
    rw [mul_div_assoc', mul_div_mul_left _ _ hp0]
  have e3 : p * (b.ellF lam * logG lam p / p) = b.ellF lam * logG lam p := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hp0]
  have e4 : logG lam p = -Real.log (1 - p) - logMass lam p := logG_eq hl hp hp1
  unfold PhiRoot Rw ownR
  linear_combination e1 + e2 - e3 - b.ellF lam * e4

end BandData

/-! ### Tree level -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

section Residuals

variable (G)

/-- `Δ_u(v) = ∑_w p_w h(p_w) (z_w)₋² − (z_v − 1)₊²/T_v`. -/
noncomputable def dU (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
      hFun (rootProb G lam (compIn G (s.erase v) w) w) *
      (max (-zR G lam (compIn G (s.erase v) w) w) 0) ^ 2 -
    (max (zR G lam s v - 1) 0) ^ 2 / logMass lam (rootProb G lam s v)

/-- `Δ_v(v) = ∑_w p_w h(p_w) (z_w)₊² − (1 − z_v)₊²/T_v`. -/
noncomputable def dV (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
      hFun (rootProb G lam (compIn G (s.erase v) w) w) *
      (max (zR G lam (compIn G (s.erase v) w) w) 0) ^ 2 -
    (max (1 - zR G lam s v) 0) ^ 2 / logMass lam (rootProb G lam s v)

/-- `Δ_s(v) = ∑_w p_w (1 − p_w) z_w² − (1 − z_v)²/H_v`. -/
noncomputable def dS (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
      (1 - rootProb G lam (compIn G (s.erase v) w) w) * zR G lam (compIn G (s.erase v) w) w ^ 2 -
    (1 - zR G lam s v) ^ 2 / packH lam (rootProb G lam s v)

/-- `Δ_w(v) = ∑_w p_w − φ_v` (the packed child-mass slack). -/
noncomputable def dW (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w - packPhi lam (rootProb G lam s v)

end Residuals

section Nonneg

variable {lam : ℝ}

omit [Fintype V] in
theorem yLog_le_log (hl : 0 < lam) {s : Finset V} {r : V} (hr : r ∈ s) :
    yLog G lam s r ≤ Real.log (1 + lam) := by
  have hp := rootProb_le_actQ (G := G) hl.le hr
  have hp1 := one_sub_rootProb_pos (G := G) hl.le hr
  unfold yLog
  rw [← Real.log_inv]
  apply Real.log_le_log (inv_pos.mpr hp1)
  rw [inv_le_comm₀ hp1 (by linarith), ← one_div]
  unfold actQ at hp
  rw [le_div_iff₀ (by linarith)] at hp
  rw [div_le_iff₀ (by linarith)]
  nlinarith

omit [Fintype V] in
theorem exp_yLog (hl : 0 ≤ lam) {s : Finset V} {r : V} (hr : r ∈ s) :
    Real.exp (yLog G lam s r) = 1 / (1 - rootProb G lam s r) := by
  unfold yLog
  rw [Real.exp_neg, Real.exp_log (one_sub_rootProb_pos hl hr), one_div]

omit [Fintype V] in
theorem hFun_eq (s : Finset V) (r : V) :
    hFun (rootProb G lam s r) = rootProb G lam s r / yLog G lam s r := rfl

omit [Fintype V] in
theorem Tmass_eq_sum (s : Finset V) (r : V) :
    Tmass G lam s r = ∑ w ∈ nbrsIn G s r, yLog G lam (compIn G (s.erase r) w) w := rfl

/-- **`Δ_u ≥ 0`**: `(z_v − 1)₊ ≤ ∑ p_w (z_w)₋` and Cauchy with the child masses `y_w`. -/
theorem dU_nonneg (hG : G.IsAcyclic) (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s) {v : V}
    (hv : v ∈ s) : 0 ≤ dU G lam s v := by
  have hy : ∀ w ∈ nbrsIn G s v, 0 < yLog G lam (compIn G (s.erase v) w) w := fun w hw =>
    yLog_pos hG hl (compIn_branch hG hs hv hw).1 (compIn_branch hG hs hv hw).2.1
  have hrec := zR_rec hG hl.le hs hv
  have hb : max (zR G lam s v - 1) 0 ≤ ∑ w ∈ nbrsIn G s v,
      rootProb G lam (compIn G (s.erase v) w) w *
        max (-zR G lam (compIn G (s.erase v) w) w) 0 := by
    have hsum_nonneg : 0 ≤ ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
        max (-zR G lam (compIn G (s.erase v) w) w) 0 :=
      Finset.sum_nonneg fun w _ => mul_nonneg (rootProb_nonneg hl.le _ _) (le_max_right _ _)
    refine max_le ?_ hsum_nonneg
    have : zR G lam s v - 1 = ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
        (-zR G lam (compIn G (s.erase v) w) w) := by
      rw [hrec]
      simp only [mul_neg, Finset.sum_neg_distrib]
      ring
    rw [this]
    exact Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (le_max_left _ _) (rootProb_nonneg hl.le _ _)
  have hC := sq_div_le_of_le_sum (nbrsIn G s v)
    (fun w => rootProb G lam (compIn G (s.erase v) w) w *
      max (-zR G lam (compIn G (s.erase v) w) w) 0)
    (fun w => yLog G lam (compIn G (s.erase v) w) w) hy (le_max_right _ _) hb
  rw [← Tmass_eq_sum, ← logMass_eq_Tmass hG hl hs hv] at hC
  have hterm : ∀ w ∈ nbrsIn G s v, (rootProb G lam (compIn G (s.erase v) w) w *
      max (-zR G lam (compIn G (s.erase v) w) w) 0) ^ 2 / yLog G lam (compIn G (s.erase v) w) w =
      rootProb G lam (compIn G (s.erase v) w) w * hFun (rootProb G lam (compIn G (s.erase v) w) w) *
        (max (-zR G lam (compIn G (s.erase v) w) w) 0) ^ 2 := by
    intro w _
    rw [hFun_eq]
    ring
  rw [Finset.sum_congr rfl hterm] at hC
  unfold dU
  linarith

/-- **`Δ_v ≥ 0`**: `(1 − z_v)₊ ≤ ∑ p_w (z_w)₊` and Cauchy with the child masses. -/
theorem dV_nonneg (hG : G.IsAcyclic) (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s) {v : V}
    (hv : v ∈ s) : 0 ≤ dV G lam s v := by
  have hy : ∀ w ∈ nbrsIn G s v, 0 < yLog G lam (compIn G (s.erase v) w) w := fun w hw =>
    yLog_pos hG hl (compIn_branch hG hs hv hw).1 (compIn_branch hG hs hv hw).2.1
  have hrec := zR_rec hG hl.le hs hv
  have hb : max (1 - zR G lam s v) 0 ≤ ∑ w ∈ nbrsIn G s v,
      rootProb G lam (compIn G (s.erase v) w) w *
        max (zR G lam (compIn G (s.erase v) w) w) 0 := by
    have hsum_nonneg : 0 ≤ ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
        max (zR G lam (compIn G (s.erase v) w) w) 0 :=
      Finset.sum_nonneg fun w _ => mul_nonneg (rootProb_nonneg hl.le _ _) (le_max_right _ _)
    refine max_le ?_ hsum_nonneg
    have : 1 - zR G lam s v = ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
        zR G lam (compIn G (s.erase v) w) w := by
      rw [hrec]; ring
    rw [this]
    exact Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (le_max_left _ _) (rootProb_nonneg hl.le _ _)
  have hC := sq_div_le_of_le_sum (nbrsIn G s v)
    (fun w => rootProb G lam (compIn G (s.erase v) w) w *
      max (zR G lam (compIn G (s.erase v) w) w) 0)
    (fun w => yLog G lam (compIn G (s.erase v) w) w) hy (le_max_right _ _) hb
  rw [← Tmass_eq_sum, ← logMass_eq_Tmass hG hl hs hv] at hC
  have hterm : ∀ w ∈ nbrsIn G s v, (rootProb G lam (compIn G (s.erase v) w) w *
      max (zR G lam (compIn G (s.erase v) w) w) 0) ^ 2 / yLog G lam (compIn G (s.erase v) w) w =
      rootProb G lam (compIn G (s.erase v) w) w * hFun (rootProb G lam (compIn G (s.erase v) w) w) *
        (max (zR G lam (compIn G (s.erase v) w) w) 0) ^ 2 := by
    intro w _
    rw [hFun_eq]
    ring
  rw [Finset.sum_congr rfl hterm] at hC
  unfold dV
  linarith

omit [Fintype V] in
/-- The packing bound (7) on the actual child list: `∑ p_w/(1 − p_w) ≤ H_v`. -/
theorem sum_odds_le_packH (hG : G.IsAcyclic) (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s)
    {v : V} (hv : v ∈ s) :
    ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w /
      (1 - rootProb G lam (compIn G (s.erase v) w) w) ≤ packH lam (rootProb G lam s v) := by
  have hL : 0 < Real.log (1 + lam) := Real.log_pos (by linarith)
  have h := sum_le_packB (nbrsIn G s v) (fun w => yLog G lam (compIn G (s.erase v) w) w)
    (c := 1) hL (fun w hw => (yLog_pos hG hl (compIn_branch hG hs hv hw).1
      (compIn_branch hG hs hv hw).2.1).le)
    (fun w hw => yLog_le_log hl (compIn_branch hG hs hv hw).2.1)
  rw [← Tmass_eq_sum, ← logMass_eq_Tmass hG hl hs hv, ← packH_eq hl] at h
  have hterm : ∀ w ∈ nbrsIn G s v, Real.exp (1 * yLog G lam (compIn G (s.erase v) w) w) - 1 =
      rootProb G lam (compIn G (s.erase v) w) w /
        (1 - rootProb G lam (compIn G (s.erase v) w) w) := by
    intro w hw
    have hwC := (compIn_branch hG hs hv hw).2.1
    have h1 := one_sub_rootProb_pos (G := G) hl.le hwC
    rw [one_mul, exp_yLog hl.le hwC, div_sub_one h1.ne']
    congr 1
    ring
  rwa [Finset.sum_congr rfl hterm] at h

omit [Fintype V] in
/-- The packing bound (8) on the actual child list: `∑ p_w ≥ φ_v`. -/
theorem packPhi_le_sum (hG : G.IsAcyclic) (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s)
    {v : V} (hv : v ∈ s) :
    packPhi lam (rootProb G lam s v) ≤
      ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w := by
  have hL : 0 < Real.log (1 + lam) := Real.log_pos (by linarith)
  have h := sum_le_packB (nbrsIn G s v) (fun w => yLog G lam (compIn G (s.erase v) w) w)
    (c := -1) hL (fun w hw => (yLog_pos hG hl (compIn_branch hG hs hv hw).1
      (compIn_branch hG hs hv hw).2.1).le)
    (fun w hw => yLog_le_log hl (compIn_branch hG hs hv hw).2.1)
  rw [← Tmass_eq_sum, ← logMass_eq_Tmass hG hl hs hv] at h
  have hterm : ∀ w ∈ nbrsIn G s v, Real.exp (-1 * yLog G lam (compIn G (s.erase v) w) w) - 1 =
      -rootProb G lam (compIn G (s.erase v) w) w := by
    intro w hw
    have hwC := (compIn_branch hG hs hv hw).2.1
    rw [neg_one_mul]
    unfold yLog
    rw [neg_neg, Real.exp_log (one_sub_rootProb_pos hl.le hwC)]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at h
  rw [packPhi_eq hl]
  linarith

/-- **`Δ_s ≥ 0`**: weighted Cauchy and the packing bound (7). -/
theorem dS_nonneg (hG : G.IsAcyclic) (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s) {v : V}
    (hv : v ∈ s) : 0 ≤ dS G lam s v := by
  have hrec := zR_rec hG hl.le hs hv
  have h := sq_div_le_of_le_odds (nbrsIn G s v)
    (fun w => rootProb G lam (compIn G (s.erase v) w) w)
    (fun w => zR G lam (compIn G (s.erase v) w) w)
    (fun w hw => rootProb_pos hl _ _)
    (fun w hw => rootProb_lt_one hl.le (compIn_branch hG hs hv hw).2.1)
    (sum_odds_le_packH hG hl hs hv)
  have h1 : 1 - zR G lam s v = ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
      zR G lam (compIn G (s.erase v) w) w := by
    rw [hrec]; ring
  unfold dS
  rw [h1]
  linarith

omit [Fintype V] in
/-- **`Δ_w ≥ 0`**: the packing bound (8). -/
theorem dW_nonneg (hG : G.IsAcyclic) (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s) {v : V}
    (hv : v ∈ s) : 0 ≤ dW G lam s v := by
  unfold dW
  linarith [packPhi_le_sum hG hl hs hv]

end Nonneg

/-! ### The per-vertex ledger -/

section Terms

variable (G)

/-- The source term `ρ p g(p, ρ)` (its price-weighted sum is `c ∑ π g`). -/
noncomputable def gT (lam : ℝ) (s : Finset V) (v : V) (ρ _t : ℝ) : ℝ :=
  ρ * rootProb G lam s v * src lam (rootProb G lam s v) ρ

/-- The innovation `ρ p (1 − p) z²` (its sum is `Var K`, `dfold_innov`). -/
noncomputable def innT (lam : ℝ) (s : Finset V) (v : V) (ρ _t : ℝ) : ℝ :=
  ρ * rootProb G lam s v * (1 - rootProb G lam s v) * zR G lam s v ^ 2

end Terms

namespace BandData

variable (b : BandData) (G)

/-- The own part at a vertex of a rooted subtree. -/
noncomputable def ownT (lam : ℝ) (s : Finset V) (v : V) (ρ _t : ℝ) : ℝ :=
  b.ownR lam (rootProb G lam s v) (zR G lam s v) ρ

/-- The incoming part at a vertex of a rooted subtree (inherited `(ρ, t)`). -/
noncomputable def incT (lam : ℝ) (s : Finset V) (v : V) (ρ t : ℝ) : ℝ :=
  b.incR lam (rootProb G lam s v) (zR G lam s v) ρ t

/-- The payment term `p Φ` of a nonroot vertex. -/
noncomputable def payT (lam : ℝ) (s : Finset V) (v : V) (ρ t : ℝ) : ℝ :=
  rootProb G lam s v * b.Phi lam (rootProb G lam s v) ρ t (zR G lam s v)

/-- The residual credits `u Δ_u + v Δ_v + ρ p s Δ_s + w ρ p Δ_w`. -/
noncomputable def resT (lam : ℝ) (s : Finset V) (v : V) (ρ _t : ℝ) : ℝ :=
  b.uF lam (rootProb G lam s v) * dU G lam s v + b.vF lam (rootProb G lam s v) * dV G lam s v +
    ρ * rootProb G lam s v * b.sF lam (rootProb G lam s v) * dS G lam s v +
    b.wF lam * (ρ * rootProb G lam s v * dW G lam s v)

/-- The local ledger `c ρ p g − ρ p (1 − p) z² − residuals`. -/
noncomputable def locT (lam : ℝ) (s : Finset V) (v : V) (ρ t : ℝ) : ℝ :=
  b.price lam * gT G lam s v ρ t - innT G lam s v ρ t - b.resT G lam s v ρ t

variable {b G}

/-- **The per-vertex ledger**: the own part minus the incoming parts of the children is the local
ledger (the `τ` and logarithmic receipts cancel exactly on the actual child edges). -/
theorem own_sub_inc_eq (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam) {s : Finset V}
    (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) (ρ t : ℝ) :
    b.ownT G lam s v ρ t - ∑ w ∈ nbrsIn G s v, b.incT G lam (compIn G (s.erase v) w) w
      (1 - ρ * rootProb G lam s v) (rootProb G lam s v) = b.locT G lam s v ρ t := by
  set p := rootProb G lam s v with hp
  have hS4 : ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w *
      zR G lam (compIn G (s.erase v) w) w = 1 - zR G lam s v := by
    rw [zR_rec hG hl.le hs hv]; ring
  have hS6 : ∑ w ∈ nbrsIn G s v, -Real.log (1 - rootProb G lam (compIn G (s.erase v) w) w) =
      logMass lam p := by
    rw [hp, logMass_eq_Tmass hG hl hs hv]
    rfl
  have hterm : ∀ w ∈ nbrsIn G s v, b.incT G lam (compIn G (s.erase v) w) w (1 - ρ * p) p =
      b.uF lam p * (rootProb G lam (compIn G (s.erase v) w) w *
          hFun (rootProb G lam (compIn G (s.erase v) w) w) *
          (max (-zR G lam (compIn G (s.erase v) w) w) 0) ^ 2) +
        b.vF lam p * (rootProb G lam (compIn G (s.erase v) w) w *
          hFun (rootProb G lam (compIn G (s.erase v) w) w) *
          (max (zR G lam (compIn G (s.erase v) w) w) 0) ^ 2) +
        ρ * p * b.sF lam p * (rootProb G lam (compIn G (s.erase v) w) w *
          (1 - rootProb G lam (compIn G (s.erase v) w) w) *
          zR G lam (compIn G (s.erase v) w) w ^ 2) -
        ρ * p * b.tauF lam p * (rootProb G lam (compIn G (s.erase v) w) w *
          zR G lam (compIn G (s.erase v) w) w) +
        b.wF lam * (ρ * p) * (rootProb G lam (compIn G (s.erase v) w) w -
          rootProb G lam (compIn G (s.erase v) w) w * zR G lam (compIn G (s.erase v) w) w) +
        b.ellF lam * (-Real.log (1 - rootProb G lam (compIn G (s.erase v) w) w)) := by
    intro w _
    unfold incT incR
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hS4, hS6]
  unfold ownT ownR locT gT innT resT dU dV dS dW
  rw [← hp]
  ring

/-- The payment of every vertex of a rooted subtree splits as own minus incoming. -/
theorem payT_eq {lam : ℝ} (hl : 0 < lam) {s : Finset V} {v : V} (hv : v ∈ s) (ρ t : ℝ) :
    b.payT G lam s v ρ t = b.ownT G lam s v ρ t - b.incT G lam s v ρ t :=
  b.pay_eq hl (rootProb_pos hl s v) (rootProb_lt_one hl.le hv) ρ t _

end BandData

end Erdos993Lean.Analytic.O2
