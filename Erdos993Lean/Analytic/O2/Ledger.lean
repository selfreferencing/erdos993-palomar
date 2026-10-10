module

public import Erdos993Lean.Analytic.O2.Local

/-!
# O2: the eight-term ledger on a component and `Var K ≤ c ∑ π s'`

Source: the O2 proof, Theorem 4
(the conditional payment: multiply (11) by `p` and sum), Theorem 5 (the complete nonnegative ledger
(22)), Lemma 2 (the retained source), and its implementation map §2, obligations 4–6.

On a component `K` (connected, closed under adjacency) of a finite acyclic graph, rooted at `r`, at
activity `λ > 0` in a band `b`:

* **`BandData.component_ledger`** (the exact ledger): the root payment `p_r PhiRoot` plus the folds of
  the nonroot payments `p_v Φ_v` (each with its actual parent's fields) equals
  `c ∑ ρ p g − ∑ ρ p(1−p)z² − ∑ (u Δ_u + v Δ_v + ρ p s Δ_s + w ρ p Δ_w) − ℓ y_r`;
  together with the innovation identity (`dfold_innov`, `∑ ρ p (1−p) z² = Var K`) this is (22)
  restricted to the component, the first two terms of (22) being consumed by `gT_le` and the
  competitor (`dp_closed`, file `Source.lean`);
* the nonnegativity of every payment (`BandData.OK`, the inherited `PhysRecord`), of the residuals
  (`dU_nonneg` …), of the root credit `ℓ y_r`;
* **`gT_le`** (Lemma 2 along the tree): `ρ_v p_v g(p_v, ρ_v) ≤ π_v s'_v` at every vertex, from the
  inherited invariant `SrcInv` (the actual marginals are the local mixtures `mu`, and the only
  neighbour outside a subtree is the parent, with marginal `1 − ρ`);
* **`BandData.varB_le_component`**: `Var K ≤ c ∑_{v ∈ K} π_v s'_v`, and
  **`BandData.varB_le_closed`**: the same on every vertex set closed under adjacency (components
  add), in particular on the whole vertex set.

Scalarity check.  The ledger keeps the actual records `(p_v, ρ_v, t_v, z_v)` of the actual rooted
tree; the only scalars are the output price `c = γ/(1+λ)` and the band multipliers `w, ℓ` (chosen
once per activity), consumed here; `Var K` is the variance of the actual total count.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.O2

open Finset Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Folding the payments -/

namespace BandData

variable {b : BandData} {lam : ℝ}

/-- **The payments of a subtree** are its local ledgers minus the incoming part of its root. -/
theorem dfold_pay_eq (hG : G.IsAcyclic) (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) (ρ t : ℝ) :
    dfold G lam (b.payT G lam) s r ρ t =
      dfold G lam (b.locT G lam) s r ρ t - b.incT G lam s r ρ t := by
  have h1 : dfold G lam (b.payT G lam) s r ρ t = dfold G lam
      (fun s v ρ t => b.ownT G lam s v ρ t - b.incT G lam s v ρ t) s r ρ t :=
    dfold_congr_of_inv hG lam (fun _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ v ρ t _ hv _ => b.payT_eq hl hv ρ t) hs hr trivial
  rw [h1, dfold_telescope lam (b.ownT G lam) (b.incT G lam) hr ρ t]
  congr 1
  exact dfold_congr_of_inv hG lam (fun _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ v ρ t hs hv _ => own_sub_inc_eq hG hl hs hv ρ t) hs hr trivial

/-- **The exact ledger on a component rooted at `r`.** -/
theorem component_ledger (hG : G.IsAcyclic) (hl : 0 < lam) {K : Finset V}
    (hK : ConnectedIn G K) {r : V} (hr : r ∈ K) :
    rootProb G lam K r * b.PhiRoot lam (rootProb G lam K r) (zR G lam K r) +
      ∑ w ∈ nbrsIn G K r, dfold G lam (b.payT G lam) (compIn G (K.erase r) w) w
        (1 - 1 * rootProb G lam K r) (rootProb G lam K r) =
      dfold G lam (b.locT G lam) K r 1 0 - b.ellF lam * yLog G lam K r := by
  rw [b.payRoot_eq hl (rootProb_pos hl K r) (rootProb_lt_one hl.le hr),
    Finset.sum_congr rfl (fun w hw => dfold_pay_eq hG hl (compIn_branch hG hK hr hw).1
      (compIn_branch hG hK hr hw).2.1 (1 - 1 * rootProb G lam K r) (rootProb G lam K r)),
    Finset.sum_sub_distrib, dfold_eq _ _ hr]
  have hloc := own_sub_inc_eq (b := b) hG hl hK hr 1 0
  unfold ownT at hloc
  unfold yLog
  linarith

/-- The local ledger splits as `c · source − innovation − residuals`. -/
theorem dfold_locT (s : Finset V) (r : V) (ρ t : ℝ) :
    dfold G lam (b.locT G lam) s r ρ t = b.price lam * dfold G lam (gT G lam) s r ρ t -
      dfold G lam (innT G lam) s r ρ t - dfold G lam (b.resT G lam) s r ρ t := by
  rw [← dfold_mul_left, ← dfold_sub, ← dfold_sub]
  rfl

end BandData

/-! ### The inherited invariants -/

variable (G) in
/-- **The source invariant** of a subtree `(s, v)` with inherited `ρ`: every actual marginal in `s`
is the local mixture `mu`, and the only neighbour of `s` outside `s` is the parent of `v`, whose
marginal is `1 − ρ`. -/
def SrcInv (lam : ℝ) (s : Finset V) (v : V) (ρ _t : ℝ) : Prop :=
  (∀ x ∈ s, gMarg G lam x = mu G lam s v ρ x) ∧
    (∀ x ∈ s, ∀ y, G.Adj x y → y ∉ s → x = v ∧ gMarg G lam y = 1 - ρ) ∧ 0 ≤ ρ ∧ ρ ≤ 1

theorem srcInv_child (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam) {s : Finset V} {v : V}
    (hv : v ∈ s) {ρ t : ℝ} (h : SrcInv G lam s v ρ t) {w : V} (hw : w ∈ nbrsIn G s v) :
    SrcInv G lam (compIn G (s.erase v) w) w (1 - ρ * rootProb G lam s v) (rootProb G lam s v) := by
  obtain ⟨ha, hb, hρ0, hρ1⟩ := h
  have hp0 := rootProb_nonneg (G := G) hl.le s v
  have hp1 := rootProb_lt_one (G := G) hl.le hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [ha x (Finset.mem_of_mem_erase (compIn_subset _ _ hx)), mu_branch hG hl.le hv hw hx ρ]
  · intro x hx y hxy hy
    have hxs : x ∈ s.erase v := compIn_subset _ _ hx
    by_cases hys : y ∈ s
    · by_cases hyv : y = v
      · rw [hyv] at hxy
        refine ⟨eq_of_mem_branch_of_adj hG (mem_nbrsIn.mp hw).2 hx hxy.symm, ?_⟩
        rw [hyv, ha v hv, mu_root hv]
        ring
      · exact absurd (mem_compIn_of_adjIn hx ⟨hxs, Finset.mem_erase.mpr ⟨hyv, hys⟩, hxy⟩) hy
    · exact absurd (hb x (Finset.mem_of_mem_erase hxs) y hxy hys).1 (Finset.mem_erase.mp hxs).1
  · nlinarith
  · nlinarith

theorem srcInv_top {lam : ℝ} (hl : 0 < lam) {K : Finset V}
    (hKc : ∀ v ∈ K, ∀ w, G.Adj v w → w ∈ K) {r : V} (t : ℝ) : SrcInv G lam K r 1 t := by
  refine ⟨?_, fun x hx y hxy hy => absurd (hKc x hx y hxy) hy, zero_le_one, le_rfl⟩
  intro x hx
  rw [mu_one]
  unfold gMarg
  rw [← marg_of_mem (G := G) (Finset.mem_univ x)]
  refine marg_of_closed hl.le (Finset.subset_univ K) ?_ hx
  intro a ha b hb hab
  exact (Finset.mem_sdiff.mp hb).2 (hKc a ha b hab)

omit [Fintype V] in
/-- A child's cavity probability is at most `H_c(p_parent)`. -/
theorem child_le_cavH (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam) {s : Finset V}
    (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) {w : V} (hw : w ∈ nbrsIn G s v) :
    rootProb G lam (compIn G (s.erase v) w) w ≤ cavH lam (rootProb G lam s v) := by
  have hwC := (compIn_branch hG hs hv hw).2.1
  have hb := rootProb_le_parentBound hG hl hs hv hw
  set pw := rootProb G lam (compIn G (s.erase v) w) w
  set p := rootProb G lam s v
  have hp1 : 0 < 1 - p := one_sub_rootProb_pos hl.le hv
  have hpw1 : 0 < 1 - pw := one_sub_rootProb_pos hl.le hwC
  refine le_min (rootProb_le_actQ hl.le hwC) ?_
  rw [le_div_iff₀ (by positivity)] at hb
  have : p / (lam * (1 - p)) ≤ 1 - pw := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Lemma 2 along the tree**: `ρ_v p_v g(p_v, ρ_v) ≤ π_v s'_v`. -/
theorem gT_le (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s)
    {v : V} (hv : v ∈ s) {ρ t : ℝ} (h : SrcInv G lam s v ρ t) :
    gT G lam s v ρ t ≤ gMarg G lam v * sRef G lam v := by
  obtain ⟨ha, hb, hρ0, hρ1⟩ := h
  have hπ : gMarg G lam v = ρ * rootProb G lam s v := by rw [ha v hv, mu_root hv]
  have hp0 := rootProb_nonneg (G := G) hl.le s v
  have hp1 := rootProb_lt_one (G := G) hl.le hv
  have hnb : ∀ y, G.Adj v y → gMarg G lam y ≤ mUp lam (rootProb G lam s v) ρ := by
    intro y hvy
    by_cases hys : y ∈ s
    · have hyN : y ∈ nbrsIn G s v := mem_nbrsIn.mpr ⟨hys, hvy⟩
      have hyC := self_mem_branch hyN
      rw [ha y hys, mu_branch hG hl.le hv hyN hyC ρ, mu_root hyC]
      refine le_trans ?_ (le_max_right _ _)
      rw [mul_comm (rootProb G lam s v) ρ]
      exact mul_le_mul_of_nonneg_left (child_le_cavH hG hl hs hv hyN) (by nlinarith)
    · rw [(hb v hv y hvy hys).2]
      exact le_max_left _ _
  have hsrc := src_le_sRef hl hπ hρ1 hnb
  unfold gT
  rw [hπ]
  exact mul_le_mul_of_nonneg_left hsrc (mul_nonneg hρ0 hp0)

/-! ### The component bound -/

namespace BandData

variable {b : BandData} {lam : ℝ}

/-- **`Var K ≤ c ∑_{v ∈ K} π_v s'_v` on a component.** -/
theorem varB_le_component (hok : b.OK) (hlam : b.InBand lam) (hG : G.IsAcyclic) {K : Finset V}
    (hK : ConnectedIn G K) (hKc : ∀ v ∈ K, ∀ w, G.Adj v w → w ∈ K) {r : V} (hr : r ∈ K) :
    varB G univ lam K ≤ b.price lam * ∑ v ∈ K, gMarg G lam v * sRef G lam v := by
  have hl := hlam.pos hok.guards
  -- the payments are nonnegative
  have hp0 := rootProb_pos (G := G) hl K r
  have hzleaf : ∀ {s : Finset V} {v : V}, ConnectedIn G s → v ∈ s →
      rootProb G lam s v = actQ lam → zR G lam s v = 1 := by
    intro s v hs hv hpq
    refine zR_of_nbrsIn_empty hG hl.le hs hv ?_
    by_contra hne
    exact (rootProb_lt_actQ hl hv (Finset.nonempty_iff_ne_empty.mpr hne)).ne hpq
  have hroot : 0 ≤ rootProb G lam K r * b.PhiRoot lam (rootProb G lam K r) (zR G lam K r) :=
    mul_nonneg hp0.le (hok.phiRoot_nonneg hlam hp0 (rootProb_le_actQ hl.le hr) (hzleaf hK hr))
  have hchild : ∀ w ∈ nbrsIn G K r, 0 ≤ dfold G lam (b.payT G lam) (compIn G (K.erase r) w) w
      (1 - 1 * rootProb G lam K r) (rootProb G lam K r) := by
    intro w hw
    refine dfold_nonneg_of_inv hG lam (fun s v ρ t => PhysRecord lam (rootProb G lam s v) ρ t)
      ?_ ?_ (compIn_branch hG hK hr hw).1 (compIn_branch hG hK hr hw).2.1
      (physRecord_child hG hl hK hr le_rfl (by nlinarith [rootProb_lt_one (G := G) hl.le hr]) hw)
    · intro s v ρ t hs hv hrec w' hw'
      exact physRecord_child hG hl hs hv hrec.rho_le_one (hrec.one_le_rho_mul hl) hw'
    · intro s v ρ t hs hv hrec
      exact mul_nonneg (rootProb_nonneg hl.le _ _)
        (hok.phi_nonneg hlam hrec (hzleaf hs hv))
  have hledger := component_ledger (b := b) hG hl hK hr
  have hpay := add_nonneg hroot (Finset.sum_nonneg hchild)
  rw [hledger, dfold_locT] at hpay
  -- the innovations are the variance
  have hinn : dfold G lam (innT G lam) K r 1 0 = varB G univ lam K := by
    have := dfold_innov hG hl.le hK hr 1 0
    rw [one_mul, sub_self, zero_mul, add_zero] at this
    exact this
  -- the residual credits are nonnegative
  have hres : 0 ≤ dfold G lam (b.resT G lam) K r 1 0 := by
    refine dfold_nonneg_of_inv hG lam (fun _ _ ρ _ => 0 ≤ ρ ∧ ρ ≤ 1) ?_ ?_ hK hr
      ⟨zero_le_one, le_rfl⟩
    · intro s v ρ t hs hv hρ w' hw'
      have hp0 := rootProb_nonneg (G := G) hl.le s v
      have hp1 := rootProb_lt_one (G := G) hl.le hv
      constructor <;> nlinarith [hρ.1, hρ.2]
    · intro s v ρ t hs hv hρ
      have hp0 := rootProb_nonneg (G := G) hl.le s v
      unfold resT
      have h1 := mul_nonneg (b.uF_nonneg hok.guards hlam (rootProb G lam s v)) (dU_nonneg hG hl hs hv)
      have h2 := mul_nonneg (b.vF_nonneg hok.guards hlam (rootProb G lam s v)) (dV_nonneg hG hl hs hv)
      have h3 := mul_nonneg (mul_nonneg (mul_nonneg hρ.1 hp0)
        (b.sF_nonneg hok.guards hlam (rootProb G lam s v))) (dS_nonneg hG hl hs hv)
      have h4 := mul_nonneg (b.wF_nonneg hok.guards hlam)
        (mul_nonneg (mul_nonneg hρ.1 hp0) (dW_nonneg hG hl hs hv))
      linarith
  -- the root credit is nonnegative
  have hy : 0 ≤ b.ellF lam * yLog G lam K r :=
    mul_nonneg (b.ellF_nonneg hok.guards hlam) (yLog_pos hG hl hK hr).le
  -- the source
  have hsrc : dfold G lam (gT G lam) K r 1 0 ≤ ∑ v ∈ K, gMarg G lam v * sRef G lam v := by
    rw [← dfold_const hG lam (fun v => gMarg G lam v * sRef G lam v) hK hr 1 0]
    exact dfold_le_of_inv hG lam (SrcInv G lam) (fun s v ρ t _ hv h w hw => srcInv_child hG hl hv h hw)
      (fun s v ρ t hs hv h => gT_le hG hl hs hv h) hK hr (srcInv_top hl hKc 0)
  have hc := b.price_nonneg hok.guards hlam
  rw [hinn] at hpay
  nlinarith [mul_le_mul_of_nonneg_left hsrc hc]

/-- **`Var(s) ≤ c ∑_{v ∈ s} π_v s'_v` on every vertex set closed under adjacency** (components
add). -/
theorem varB_le_closed (hok : b.OK) (hlam : b.InBand lam) (hG : G.IsAcyclic) :
    ∀ s : Finset V, (∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s) →
      varB G univ lam s ≤ b.price lam * ∑ v ∈ s, gMarg G lam v * sRef G lam v := by
  have hl := hlam.pos hok.guards
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro hsc
  rcases s.eq_empty_or_nonempty with hs0 | ⟨x, hx⟩
  · rw [hs0, varB_empty, Finset.sum_empty, mul_zero]
  · have hKs : compIn G s x ⊆ s := compIn_subset _ _
    have hxK : x ∈ compIn G s x := self_mem_compIn hx
    have hKc : ∀ v ∈ compIn G s x, ∀ w, G.Adj v w → w ∈ compIn G s x := fun v hv w hvw =>
      mem_compIn_of_adjIn hv ⟨hKs hv, hsc v (hKs hv) w hvw, hvw⟩
    have hno : ∀ a ∈ compIn G s x, ∀ b ∈ s \ compIn G s x, ¬ G.Adj a b := by
      intro a ha b hb hab
      rw [Finset.mem_sdiff] at hb
      exact hb.2 (mem_compIn_of_adjIn ha ⟨hKs ha, hb.1, hab⟩)
    have hRc : ∀ v ∈ s \ compIn G s x, ∀ w, G.Adj v w → w ∈ s \ compIn G s x := by
      intro v hv w hvw
      rw [Finset.mem_sdiff] at hv ⊢
      refine ⟨hsc v hv.1 w hvw, fun hwK => hv.2 ?_⟩
      exact mem_compIn_of_adjIn hwK ⟨hKs hwK, hv.1, hvw.symm⟩
    have hK1 := varB_le_component hok hlam hG (connectedIn_compIn s x) hKc hxK
    have hR1 := ih (s \ compIn G s x) (Finset.sdiff_ssubset hKs ⟨x, hxK⟩) hRc
    have hsplit : s = compIn G s x ∪ (s \ compIn G s x) := (Finset.union_sdiff_of_subset hKs).symm
    rw [hsplit, varB_union hl.le Finset.disjoint_sdiff hno, Finset.sum_union Finset.disjoint_sdiff]
    linarith

end BandData

end Erdos993Lean.Analytic.O2
