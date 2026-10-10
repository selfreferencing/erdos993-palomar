module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.LemmaB
public import Erdos993Lean.Analytic.Tail.Boundary

/-!
# The tail input T3, part 10: the reduced unit inequality `U ≥ 0` (Theorem T3-2, repaired)

Sources: T23 §3, Theorem T3-2
as repaired in
the repaired potential proof (activity-dependent `k(λ) = a r(λ)`, general `z = t ∈ [0, 1)`
through `ρ(λ, z) = rFallback λ z`, the domain split `Y_B > 0` / `Y_B = 0`).

For `Y_B > 0`, `Y_C ≥ 0` and `x ∈ (0, min(q, 1 − e^{−Y_B})]`, with `s = Y_B + Y_C`,
`p_c = λ e^{−s}/(1 + λ e^{−s})` (`pC`), `k = a r(λ)` (`kK`), `c = (ℓ/q)(1 − p_c/(1 + λ(1 − p_c)))`
(`T3c`):

  `U_z = −log(p_c + (1 − p_c) e^{−ρ Y_B}) + (a − k) Y_C + [Y_C > 0] k That_+(Y_C) − a L(p_c)`
  `      + Y_B · [a T(x) + [x < q] k That_+(T(x)) − k L(x) − c x] / L(x)`       (`T3U`).

`T3UNonneg λ z a ℓ` states `U_z ≥ 0` on this domain, **pointwise in `x`** (this is `U ≥ 0` with the
inner infimum over `x`, because `Y_B > 0`).  It is the only numerical input of Theorem T3-2; the
`Y_B = 0` boundary is `boundary_lemma` (proved).

Main result: `unit_step` — at a C-vertex with B-child probabilities `(p_i)_{i ∈ I}` and C-child
probabilities `(p_j)_{j ∈ J}` (at least one child), the unit surplus plus the children's
potentials dominates the potential `Ψ(p_c) = a L(p_c) + k T(p_c)`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

/-- `k(λ) = a r(λ)`. -/
noncomputable def kK (lam a : ℝ) : ℝ := a * rK lam

/-- `c(s) = (ℓ/q)(1 − h(p_c(s)))`, `h(p) = p/(1 + λ(1 − p))`. -/
noncomputable def T3c (lam ell s : ℝ) : ℝ := ell / actQ lam * (1 - hmin lam (pC lam s))

/-- `φ(x) = a T(x) + [x < q] k That_+(T(x)) − k L(x) − c(s) x`. -/
noncomputable def T3phi (lam a ell s x : ℝ) : ℝ :=
  a * Tf lam x + (if x < actQ lam then kK lam a * ThatPlus lam (Tf lam x) else 0) -
    kK lam a * Lf x - T3c lam ell s * x

/-- The part of `U_z` without the B-children:
`−log(p_c + (1 − p_c) e^{−ρ Y_B}) + (a − k) Y_C + [Y_C > 0] k That_+(Y_C) − a L(p_c)`. -/
noncomputable def T3A (lam z a YB YC : ℝ) : ℝ :=
  -Real.log (pC lam (YB + YC) + (1 - pC lam (YB + YC)) * Real.exp (-(rFallback lam z * YB))) +
    (a - kK lam a) * YC + (if 0 < YC then kK lam a * ThatPlus lam YC else 0) -
    a * Lf (pC lam (YB + YC))

/-- **The reduced unit expression** `U_z(Y_B, Y_C; x) = A + Y_B φ(x)/L(x)`. -/
noncomputable def T3U (lam z a ell YB YC x : ℝ) : ℝ :=
  T3A lam z a YB YC + YB * (T3phi lam a ell (YB + YC) x / Lf x)

/-- **The certification target of T3-2 (the domain `Y_B > 0`)**: `U_z ≥ 0` for all `Y_B > 0`,
`Y_C ≥ 0`, `0 < x ≤ min(q, 1 − e^{−Y_B})`. -/
def T3UNonneg (lam z a ell : ℝ) : Prop :=
  ∀ YB YC x : ℝ, 0 < YB → 0 ≤ YC → 0 < x → x ≤ actQ lam → x ≤ 1 - Real.exp (-YB) →
    0 ≤ T3U lam z a ell YB YC x

theorem Lf_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < Lf p := by
  unfold Lf
  have : Real.log (1 - p) < 0 := Real.log_neg (by linarith) (by linarith)
  linarith

theorem kK_nonneg {lam a : ℝ} (hlam0 : 0 < lam) (ha : 0 ≤ a) : 0 ≤ kK lam a :=
  mul_nonneg ha (rK_nonneg hlam0)

/-- **The unit step of Theorem T3-2.**  Let a C-vertex have B-children with downward
probabilities `p_i` (`i ∈ I`) and C-children with `p_j` (`j ∈ J`), at least one child, all in
`(0, q]`; let `p_c = p_c(Y_B + Y_C)` (Lemma C) and `τ ≤ p_c + (1 − p_c) e^{−ρ Y_B}` (Lemma A with
`Y_z ≥ ρ Y_B`).  If `U_z ≥ 0` on `Y_B > 0` (`T3UNonneg`) and `0 < λ ≤ 6`, `a ≥ 0`, then
`Ψ(p_c) ≤ σ_c + ∑_{i ∈ I} [a T(p_i) + [p_i < q] k That_+(T(p_i))] + ∑_{j ∈ J} Ψ(p_j)`, where
`σ_c = −log τ − c(s) ∑_i p_i` is the unit surplus. -/
theorem unit_step {ι : Type*} {lam z a ell : ℝ} (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (ha : 0 ≤ a)
    (hU : T3UNonneg lam z a ell) (I J : Finset ι) (p : ι → ℝ)
    (hpI0 : ∀ i ∈ I, 0 < p i) (hpIq : ∀ i ∈ I, p i ≤ actQ lam)
    (hpJ0 : ∀ j ∈ J, 0 < p j) (hpJq : ∀ j ∈ J, p j ≤ actQ lam)
    (hne : I.Nonempty ∨ J.Nonempty) {pr τ : ℝ}
    (hpr : pr = pC lam (∑ i ∈ I, Lf (p i) + ∑ j ∈ J, Lf (p j))) (hτ0 : 0 < τ)
    (hτ : τ ≤ pr + (1 - pr) * Real.exp (-(rFallback lam z * ∑ i ∈ I, Lf (p i)))) :
    a * Lf pr + kK lam a * Tf lam pr ≤
      (-Real.log τ - T3c lam ell (∑ i ∈ I, Lf (p i) + ∑ j ∈ J, Lf (p j)) * ∑ i ∈ I, p i) +
        ∑ i ∈ I, (a * Tf lam (p i) +
          (if p i < actQ lam then kK lam a * ThatPlus lam (Tf lam (p i)) else 0)) +
        ∑ j ∈ J, (a * Lf (p j) + kK lam a * Tf lam (p j)) := by
  have hq1 := actQ_lt_one hlam0.le
  have hk0 := kK_nonneg hlam0 ha
  have hLI : ∀ i ∈ I, 0 < Lf (p i) := fun i hi => Lf_pos (hpI0 i hi) (lt_of_le_of_lt (hpIq i hi) hq1)
  have hLJ : ∀ j ∈ J, 0 < Lf (p j) := fun j hj => Lf_pos (hpJ0 j hj) (lt_of_le_of_lt (hpJq j hj) hq1)
  obtain ⟨YB, hYB⟩ : ∃ YB, YB = ∑ i ∈ I, Lf (p i) := ⟨_, rfl⟩
  obtain ⟨YC, hYC⟩ : ∃ YC, YC = ∑ j ∈ J, Lf (p j) := ⟨_, rfl⟩
  rw [← hYB, ← hYC] at hpr ⊢
  rw [← hYB] at hτ
  have hYB0 : 0 ≤ YB := hYB ▸ Finset.sum_nonneg (fun i hi => (hLI i hi).le)
  have hYC0 : 0 ≤ YC := hYC ▸ Finset.sum_nonneg (fun j hj => (hLJ j hj).le)
  -- `T(p_c) = Y_B + Y_C`
  have hTpr : Tf lam pr = YB + YC := by rw [hpr, Tf_pC hlam0]
  -- the gain: `−log τ ≥ −log(p_c + (1 − p_c) e^{−ρ Y_B})`
  have hgain : -Real.log (pr + (1 - pr) * Real.exp (-(rFallback lam z * YB))) ≤ -Real.log τ := by
    have := Real.log_le_log hτ0 hτ
    linarith
  -- the C-children: `∑_J Ψ ≥ a Y_C + [Y_C > 0] k That_+(Y_C)` (Lemma C)
  have hJ : a * YC + (if 0 < YC then kK lam a * ThatPlus lam YC else 0) ≤
      ∑ j ∈ J, (a * Lf (p j) + kK lam a * Tf lam (p j)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hYC]
    split_ifs with hpos
    · have hJne : J.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        rw [hYC, h, Finset.sum_empty] at hpos
        exact lt_irrefl 0 hpos
      have := lemmaC_ineq hJne hlam0 hpJ0 hpJq
      rw [← hYC] at this
      nlinarith [mul_le_mul_of_nonneg_left this hk0]
    · have : 0 ≤ ∑ j ∈ J, Tf lam (p j) :=
        Finset.sum_nonneg (fun j hj => Tf_nonneg hlam0 (hpJ0 j hj) (hpJq j hj))
      nlinarith [mul_nonneg hk0 this]
  -- the B-children: `∑_I ψ = ∑_I φ + k Y_B + c ∑_I p`
  have hI : ∑ i ∈ I, (a * Tf lam (p i) +
      (if p i < actQ lam then kK lam a * ThatPlus lam (Tf lam (p i)) else 0)) =
      ∑ i ∈ I, T3phi lam a ell (YB + YC) (p i) + kK lam a * YB +
        T3c lam ell (YB + YC) * ∑ i ∈ I, p i := by
    unfold T3phi
    rw [hYB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- the key inequality `A + ∑_I φ ≥ 0`
  have hkey : 0 ≤ T3A lam z a YB YC + ∑ i ∈ I, T3phi lam a ell (YB + YC) (p i) := by
    rcases I.eq_empty_or_nonempty with hIe | hIne
    · -- `Y_B = 0`: the boundary lemma
      have hYB0' : YB = 0 := by rw [hYB, hIe, Finset.sum_empty]
      have hJne : J.Nonempty := by
        rcases hne with h | h
        · rw [hIe] at h
          exact absurd h Finset.not_nonempty_empty
        · exact h
      have hYCpos : 0 < YC := hYC ▸ Finset.sum_pos (fun j hj => hLJ j hj) hJne
      rw [hIe, Finset.sum_empty, add_zero]
      unfold T3A
      rw [hYB0', zero_add, mul_zero, neg_zero, Real.exp_zero, mul_one, add_sub_cancel,
        Real.log_one, neg_zero, zero_add, if_pos hYCpos]
      exact boundary_lemma hlam0 hlam6 ha hYCpos
    · -- `Y_B > 0`: `U_z ≥ 0` at every B-child, summed with weights `L(p_i)` (knapsack)
      have hYBpos : 0 < YB := hYB ▸ Finset.sum_pos (fun i hi => hLI i hi) hIne
      have hφ : ∀ i ∈ I, -T3A lam z a YB YC / YB * Lf (p i) ≤ T3phi lam a ell (YB + YC) (p i) := by
        intro i hi
        have hLpos := hLI i hi
        have hx1 : p i ≤ 1 - Real.exp (-YB) := by
          have hle : Lf (p i) ≤ YB := hYB ▸ Finset.single_le_sum (fun j hj => (hLI j hj).le) hi
          have he := exp_neg_Lf (lt_of_le_of_lt (hpIq i hi) hq1)
          have hexp : Real.exp (-YB) ≤ Real.exp (-Lf (p i)) := Real.exp_le_exp.mpr (by linarith)
          linarith
        have h := hU YB YC (p i) hYBpos hYC0 (hpI0 i hi) (hpIq i hi) hx1
        unfold T3U at h
        have h2 : -T3A lam z a YB YC ≤ YB * (T3phi lam a ell (YB + YC) (p i) / Lf (p i)) := by
          linarith
        have e : YB * (T3phi lam a ell (YB + YC) (p i) / Lf (p i)) * Lf (p i) =
            YB * T3phi lam a ell (YB + YC) (p i) := by
          field_simp
        rw [div_mul_eq_mul_div, div_le_iff₀ hYBpos]
        nlinarith [mul_le_mul_of_nonneg_right h2 hLpos.le]
      have hsum := Finset.sum_le_sum hφ
      rw [← Finset.mul_sum, ← hYB, div_mul_cancel₀ _ hYBpos.ne'] at hsum
      linarith
  -- assemble
  rw [hI]
  have hΨ : a * Lf pr + kK lam a * Tf lam pr = a * Lf pr + kK lam a * YB + kK lam a * YC := by
    rw [hTpr]
    ring
  rw [hΨ]
  unfold T3A at hkey
  rw [← hpr] at hkey
  linarith [hgain, hJ]

end Erdos993Lean.Analytic.Tail
