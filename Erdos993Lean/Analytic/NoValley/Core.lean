module

public import Mathlib
public import Erdos993Lean.Analytic.Defs

/-!
# The no-valley lemma T1 with an abstract fibre bound (T1 Theorem 6.1)

Source: the note T1, §1 (the weak valley in
kernel form), Theorem 3.1 (the pointwise loss form, here abstracted into a fibre lower bound `h`),
Lemma 5.1 (mixing over the free count `M`: quadratic minorant plus Abel-summation tail pricing) and
Theorem 6.1 (the explicit threshold).  The interface (`kappa`, `delta`, `Mixture`, `ExplicitThreshold`,
`NoValleyAt`, `T1Core`) is `Erdos993Lean/Analytic/Defs.lean`.

Let `X` be a probability mixture of shifted binomials (`K = Y + Bin(M, q)` given the state), with
`E M = m`, and let `k` be a rank with `E δ = 0`, `E δ² ≤ θ q(1 − q) m`, `Var M ≤ D m` and
`P(M ≤ M') ≤ T(M')` for `M' < M1`, where `δ = k − Y − qM`.  Suppose `X` has a weak valley at `k`.

1. **The expected kernel** (`Mixture.sum_kappa_eq`): with `j = k − Y`,
   `E κ(M, j) = [(1 − q) P_k − q P_{k−1}]/q + [q P_k − (1 − q) P_{k+1}]/(1 − q)`, by linearity;
   under the weak valley both brackets are `≤ 0`, so `E κ ≤ 0` (`Mixture.sum_kappa_nonpos`).
2. **The fibre bound**: pointwise `κ(M, j) ≥ h(M) − c δ − ν δ²`, hence
   `E κ ≥ E h(M) − c E δ − ν E δ² ≥ E h(M) − ν θ q(1 − q) m`.
3. **Mixing over `M` (T1 Lemma 5.1)**: with `π(M) = α + β(M − m) − γ(M − m)²`,
   `E π(M) = α − γ Var M ≥ α − γ D m` (`Mixture.sum_quadMinorant_eq`); `h ≥ π` from `M1` on and
   `h ≥ π − S` below `M1`; the tail prices are paid by Abel summation (`Mixture.tail_price_le`):
   `E[S(M) 1_{M < M1}] = ∑_{M' < M1} (S̃(M') − S̃(M' + 1)) P(M ≤ M') ≤ ∑_{M' < M1} S(M') (T(M') − T(M' − 1))`
   where `S̃ = S` on `[0, M1)` and `S̃(M1) = 0`; every Abel coefficient is `≥ 0` (by monotonicity of
   `S`, and by `S ≥ 0` for the last one).
4. Hence `0 ≥ E κ ≥ α − γ D m − ∑ S ΔT − ν θ q(1 − q) m > 0`, a contradiction.

## Main result

* `t1Core : T1Core` — T1's explicit threshold condition implies the no-valley property
  (T1 Theorem 3.1 + Lemma 5.1 = Theorem 6.1, with the fibre lower bound `h` abstract).

Auxiliary results (reusable): `NoValley.sum_range_ite_le_sub` (telescoping over a tail of
`range`), `NoValley.sum_range_abel` (Abel summation by parts), `Mixture.sum_kappa_eq`, `Mixture.sum_kappa_nonpos`,
`Mixture.sum_quadMinorant_eq`, `Mixture.tail_price_le`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic

open Finset

namespace NoValley

/-! ## Two finite-sum lemmas -/

/-- Telescoping over the tail `[a, n)` of `range n`: for `a ≤ n`,
`∑_{i < n} [a ≤ i] (f i − f (i + 1)) = f a − f n`. -/
theorem sum_range_ite_le_sub (f : ℕ → ℝ) {a n : ℕ} (h : a ≤ n) :
    ∑ i ∈ range n, (if a ≤ i then f i - f (i + 1) else 0) = f a - f n := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [sub_self]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg (not_le.mpr (mem_range.mp hi))]
  | succ n han ih =>
    rw [Finset.sum_range_succ, ih, if_pos han]
    ring

/-- **Abel summation by parts** on `range (n + 1)`:
`∑_{i ≤ n} (f i − f (i + 1)) T i + f (n + 1) T n = ∑_{i ≤ n} f i (T i − T (i − 1))`, with `T(−1) = 0`. -/
theorem sum_range_abel (f T : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (f i - f (i + 1)) * T i + f (n + 1) * T n =
      ∑ i ∈ range (n + 1), f i * (T i - if i = 0 then 0 else T (i - 1)) := by
  induction n with
  | zero =>
    rw [zero_add, Finset.sum_range_one, Finset.sum_range_one, if_pos rfl]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ (fun i => (f i - f (i + 1)) * T i) (n + 1),
      Finset.sum_range_succ (fun i => f i * (T i - if i = 0 then 0 else T (i - 1))) (n + 1), ← ih,
      if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
    ring

end NoValley

namespace Mixture

open NoValley

variable {ι : Type*} (X : Mixture ι)

/-! ## Step 1: the expected valley kernel -/

/-- **The expected valley kernel (T1 §1).**  With `j = k − Y`,
`E κ(M, j) = [(1 − q) P_k − q P_{k−1}]/q + [q P_k − (1 − q) P_{k+1}]/(1 − q)`. -/
theorem sum_kappa_eq (q : ℝ) (k : ℤ) :
    ∑ σ ∈ X.S, X.w σ * kappa q (X.M σ) (k - X.Y σ) =
      ((1 - q) * X.prob q k - q * X.prob q (k - 1)) / q +
        (q * X.prob q k - (1 - q) * X.prob q (k + 1)) / (1 - q) := by
  have hσ : ∀ σ ∈ X.S, X.w σ * kappa q (X.M σ) (k - X.Y σ) =
      ((1 - q) * (X.w σ * binom (X.M σ) q (k - X.Y σ)) -
          q * (X.w σ * binom (X.M σ) q (k - 1 - X.Y σ))) / q +
        (q * (X.w σ * binom (X.M σ) q (k - X.Y σ)) -
          (1 - q) * (X.w σ * binom (X.M σ) q (k + 1 - X.Y σ))) / (1 - q) := by
    intro σ _
    have e1 : k - 1 - (X.Y σ : ℤ) = k - X.Y σ - 1 := by ring
    have e2 : k + 1 - (X.Y σ : ℤ) = k - X.Y σ + 1 := by ring
    rw [e1, e2, kappa]
    ring
  rw [Finset.sum_congr rfl hσ, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- **Under a weak valley the expected valley kernel is nonpositive (T1 §1).** -/
theorem sum_kappa_nonpos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {k : ℤ} (hv : X.WeakValley q k) :
    ∑ σ ∈ X.S, X.w σ * kappa q (X.M σ) (k - X.Y σ) ≤ 0 := by
  rw [X.sum_kappa_eq q k]
  obtain ⟨hL, hR⟩ := hv
  have h1 : ((1 - q) * X.prob q k - q * X.prob q (k - 1)) / q ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hq0.le
  have h2 : (q * X.prob q k - (1 - q) * X.prob q (k + 1)) / (1 - q) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

/-! ## Step 3: mixing over the free count (T1 Lemma 5.1) -/

/-- **The quadratic minorant in expectation (T1 Lemma 5.1).**  For a probability mixture with
`E M = m`: `E[α + β(M − m) − γ(M − m)²] = α − γ Var M`. -/
theorem sum_quadMinorant_eq (hX : X.IsProb) {m : ℝ} (hm : X.meanM = m) (α β γ : ℝ) :
    ∑ σ ∈ X.S, X.w σ * (α + β * ((X.M σ : ℝ) - m) - γ * ((X.M σ : ℝ) - m) ^ 2) =
      α - γ * X.varM := by
  obtain ⟨-, hw1⟩ := hX
  have hmean : ∑ σ ∈ X.S, X.w σ * (X.M σ : ℝ) = m := hm
  have hvar : X.varM = ∑ σ ∈ X.S, X.w σ * ((X.M σ : ℝ) - m) ^ 2 := by
    unfold varM expect
    rw [hm]
  have hσ : ∀ σ ∈ X.S, X.w σ * (α + β * ((X.M σ : ℝ) - m) - γ * ((X.M σ : ℝ) - m) ^ 2) =
      (α - β * m) * X.w σ + β * (X.w σ * (X.M σ : ℝ)) - γ * (X.w σ * ((X.M σ : ℝ) - m) ^ 2) := by
    intro σ _
    ring
  rw [Finset.sum_congr rfl hσ, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hw1, hmean, ← hvar]
  ring

/-- **Tail pricing by Abel summation (T1 Lemma 5.1, the tail part).**  If `S ≥ 0` is
nonincreasing on `[0, M1)` and `P(M ≤ M') ≤ T(M')` for `M' < M1`, then
`E[S(M) 1_{M < M1}] ≤ ∑_{M' < M1} S(M') (T(M') − T(M' − 1))` with `T(−1) = 0`.  (The Abel identity
`E[S(M) 1_{M < M1}] = ∑_{M' < M1} (S̃(M') − S̃(M' + 1)) P(M ≤ M')` is exact, so the sign of the
weights is not needed here.) -/
theorem tail_price_le (S T : ℕ → ℝ) (M1 : ℕ)
    (hS0 : ∀ M : ℕ, M < M1 → 0 ≤ S M) (hSmono : ∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M)
    (hT : ∀ M' : ℕ, M' < M1 → X.cdfM M' ≤ T M') :
    ∑ σ ∈ X.S, X.w σ * (if X.M σ < M1 then S (X.M σ) else 0) ≤
      ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1)) := by
  -- the truncated price `S̃ = S` on `[0, M1)`, `0` from `M1` on
  set St : ℕ → ℝ := fun M => if M < M1 then S M else 0 with hSt
  -- per-state telescoping: `S(M) 1_{M < M1} = ∑_{M' < M1} [M ≤ M'] (S̃ M' − S̃ (M' + 1))`
  have key : ∀ σ, (if X.M σ < M1 then S (X.M σ) else 0) =
      ∑ M' ∈ range M1, (if X.M σ ≤ M' then St M' - St (M' + 1) else 0) := by
    intro σ
    by_cases hσ : X.M σ < M1
    · rw [if_pos hσ, sum_range_ite_le_sub St hσ.le]
      simp [hSt, hσ]
    · rw [if_neg hσ]
      symm
      refine Finset.sum_eq_zero fun M' hM' => ?_
      rw [if_neg]
      intro hle
      exact hσ (lt_of_le_of_lt hle (mem_range.mp hM'))
  -- the Abel coefficients are nonnegative
  have coef : ∀ M' ∈ range M1, 0 ≤ St M' - St (M' + 1) := by
    intro M' hM'
    have hM'1 := mem_range.mp hM'
    simp only [hSt, if_pos hM'1]
    by_cases h2 : M' + 1 < M1
    · rw [if_pos h2]
      linarith [hSmono M' h2]
    · rw [if_neg h2]
      linarith [hS0 M' hM'1]
  -- re-Abel: `∑ (S̃ M' − S̃ (M' + 1)) T M' = ∑ S M' (T M' − T (M' − 1))`
  have reabel : ∑ M' ∈ range M1, (St M' - St (M' + 1)) * T M' =
      ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1)) := by
    rcases Nat.eq_zero_or_pos M1 with h0 | hpos
    · subst h0
      simp
    · obtain ⟨n, rfl⟩ : ∃ n, M1 = n + 1 := ⟨M1 - 1, by omega⟩
      have hlast : St (n + 1) = 0 := by simp [hSt]
      have hab := sum_range_abel St T n
      rw [hlast, zero_mul, add_zero] at hab
      rw [hab]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hSt, if_pos (mem_range.mp hi)]
  calc ∑ σ ∈ X.S, X.w σ * (if X.M σ < M1 then S (X.M σ) else 0)
      = ∑ σ ∈ X.S, ∑ M' ∈ range M1,
          X.w σ * (if X.M σ ≤ M' then St M' - St (M' + 1) else 0) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [key σ, Finset.mul_sum]
    _ = ∑ M' ∈ range M1, (St M' - St (M' + 1)) * X.cdfM M' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun M' _ => ?_
        unfold cdfM
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        split_ifs <;> ring
    _ ≤ ∑ M' ∈ range M1, (St M' - St (M' + 1)) * T M' := by
        refine Finset.sum_le_sum fun M' hM' => ?_
        exact mul_le_mul_of_nonneg_left (hT M' (mem_range.mp hM')) (coef M' hM')
    _ = ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1)) := reabel

end Mixture

/-! ## The no-valley lemma -/

/-- **T1's no-valley lemma (T1 Theorem 6.1 = Theorem 3.1 + Lemma 5.1, fibre bound abstract).**
If the explicit threshold condition holds for `(q, m, θ, D, T, M1)` with `0 < q < 1`, then no
probability mixture with `E M = m`, `E δ = 0`, `E δ² ≤ θ q(1 − q) m`, `Var M ≤ D m` and
`P(M ≤ M') ≤ T(M')` for `M' < M1` has a weak valley at the rank `k`. -/
theorem t1Core : T1Core := by
  intro q m θ D T M1 hq0 hq1 hET ι X k hX hmean hδ hδ2 hvar htail hvalley
  obtain ⟨ν, c, α, β, γ, h, S, hν, hγ, hpt, hquad, hS, hS0, hSmono, hthr⟩ := hET
  have hw : ∀ σ ∈ X.S, 0 ≤ X.w σ := hX.1
  -- (1) `E κ ≤ 0` under the weak valley
  have hEκ := X.sum_kappa_nonpos hq0 hq1 hvalley
  -- (2) the fibre bound, summed: `E h ≤ E κ + c E δ + ν E δ²`
  have hEh : ∑ σ ∈ X.S, X.w σ * h (X.M σ) ≤
      ∑ σ ∈ X.S, X.w σ * kappa q (X.M σ) (k - X.Y σ) +
        c * X.expect (fun M Y => delta q k M Y) + ν * X.expect (fun M Y => delta q k M Y ^ 2) := by
    unfold Mixture.expect
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun σ hσ => ?_
    have hp := hpt (X.M σ) (k - X.Y σ)
    have hcast : (((k - (X.Y σ : ℤ) : ℤ) : ℝ) - q * (X.M σ : ℝ)) = delta q k (X.M σ) (X.Y σ) := by
      unfold delta
      push_cast
      ring
    rw [hcast] at hp
    have := mul_le_mul_of_nonneg_left hp (hw σ hσ)
    have e : X.w σ * (kappa q (X.M σ) (k - X.Y σ) + c * delta q k (X.M σ) (X.Y σ) +
        ν * delta q k (X.M σ) (X.Y σ) ^ 2) =
        X.w σ * kappa q (X.M σ) (k - X.Y σ) + c * (X.w σ * delta q k (X.M σ) (X.Y σ)) +
          ν * (X.w σ * delta q k (X.M σ) (X.Y σ) ^ 2) := by ring
    linarith
  -- (3) Lemma 5.1: `E h ≥ E π − E[S 1_{M < M1}]`
  have hEπ := X.sum_quadMinorant_eq hX hmean α β γ
  have hhπ : ∑ σ ∈ X.S, X.w σ * (α + β * ((X.M σ : ℝ) - m) - γ * ((X.M σ : ℝ) - m) ^ 2) -
      ∑ σ ∈ X.S, X.w σ * (if X.M σ < M1 then S (X.M σ) else 0) ≤
      ∑ σ ∈ X.S, X.w σ * h (X.M σ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun σ hσ => ?_
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hw σ hσ)
    by_cases hM : X.M σ < M1
    · rw [if_pos hM]
      linarith [hS (X.M σ) hM]
    · rw [if_neg hM, sub_zero]
      exact hquad (X.M σ) (not_lt.mp hM)
  have htailS := X.tail_price_le S T M1 hS0 hSmono htail
  -- (4) the contradiction
  have hνδ2 : ν * X.expect (fun M Y => delta q k M Y ^ 2) ≤ ν * (θ * (q * (1 - q)) * m) :=
    mul_le_mul_of_nonneg_left hδ2 hν.le
  have hγvar : γ * X.varM ≤ γ * (D * m) := mul_le_mul_of_nonneg_left hvar hγ
  rw [hδ, mul_zero, add_zero] at hEh
  nlinarith

end Erdos993Lean.Analytic
