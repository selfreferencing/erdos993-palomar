module

public import Mathlib
public import Erdos993Lean.Analytic.HardCore.Binomial

/-!
# Moments of a finite mixture of shifted binomials

Sources: T. Zhang, *Exact Certificates
for Unimodality of Forest Independence Polynomials*, v1.1, equations (45)–(46); the note
T23 §1.

For an arbitrary `X : Mixture ι` (states `σ`, weights `w σ`, free count `M σ`, fixed count `Y σ`;
conditionally on `σ`, `K = Y σ + Bin(M σ, q)`, law `P_i = X.prob q i`):

* linearity of `Mixture.expect` (`expect_add`, `expect_sub`, `expect_const_mul`, `expect_const`,
  `expect_congr`, `expect_nonneg`, `expect_mono`);
* `prob_of_neg` (`P_i = 0` for `i < 0`), `prob_nonneg`, `prob_eq_expect` (`P_i = E b_M(i − Y)`);
* conditional binomial moments at a fixed shift (`sum_natCast_add_mul_binom`,
  `sum_sq_sub_mul_binom`): `Σ_k (Y + k) b_M(k) = Y + qM`,
  `Σ_k (Y + k − c)² b_M(k) = (Y + qM − c)² + q(1 − q)M`;
* over a range `[0, N]` containing every `Y σ + [0, M σ]` (`sum_range_mul_prob`):
  `Σ_i P_i = Σ_σ w σ` (`sum_range_prob`), `Σ_i i P_i = E[Y + qM]` (`sum_range_mul_prob_self`),
  `Σ_i (i − c)² P_i = E[(Y + qM − c)²] + q(1 − q) E M` (`sum_range_sq_mul_prob`);
* **`moments_of_sum_eq_one`**: if `Σ_σ w σ = 1`, the law of `K` has total
  mass `1`, mean `μ_K = E[Y + qM]` and second central moment `E[(Y + qM − μ_K)²] + q(1 − q) E M`;
* `varM_eq` (`Var M = E M² − m²` for a probability mixture).

Namespaces: the conditional binomial moments are in `Erdos993Lean.Analytic.HardCore`; the
`Mixture` API is in `Erdos993Lean.Analytic.Mixture` (dot notation `X.expect_add`, ...).

Grade: PROVED IN LEAN (standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean.Analytic

open Finset

namespace HardCore

/-! ## Conditional binomial moments at a fixed shift -/

/-- `Σ_{k ≤ M} (Y + k) b_M(k) = Y + qM`. -/
theorem sum_natCast_add_mul_binom (M Y : ℕ) (q : ℝ) :
    ∑ k ∈ range (M + 1), ((Y + k : ℕ) : ℝ) * binom M q k = Y + q * M := by
  have e : ∀ k ∈ range (M + 1), ((Y + k : ℕ) : ℝ) * binom M q k =
      ((Y : ℝ) + 1 * k + 0 * (k : ℝ) ^ 2) * binom M q k := by
    intro k _
    push_cast
    ring
  rw [Finset.sum_congr rfl e, sum_quad_mul_binom]
  ring

/-- `Σ_{k ≤ M} (Y + k − c)² b_M(k) = (Y + qM − c)² + q(1 − q)M`. -/
theorem sum_sq_sub_mul_binom (M Y : ℕ) (q c : ℝ) :
    ∑ k ∈ range (M + 1), (((Y + k : ℕ) : ℝ) - c) ^ 2 * binom M q k =
      ((Y : ℝ) + q * M - c) ^ 2 + q * (1 - q) * M := by
  have e : ∀ k ∈ range (M + 1), (((Y + k : ℕ) : ℝ) - c) ^ 2 * binom M q k =
      (((Y : ℝ) - c) ^ 2 + 2 * ((Y : ℝ) - c) * k + 1 * (k : ℝ) ^ 2) * binom M q k := by
    intro k _
    push_cast
    ring
  rw [Finset.sum_congr rfl e, sum_quad_mul_binom]
  ring

/-- `Σ_{k ≤ M} [Y + k = i] b_M(k) = b_M(i − Y)`. -/
theorem sum_ite_mul_binom (M Y i : ℕ) (q : ℝ) :
    ∑ k ∈ range (M + 1), (if Y + k = i then (1 : ℝ) else 0) * binom M q k =
      binom M q ((i : ℤ) - Y) := by
  by_cases hYi : Y ≤ i
  · have e : ∀ k ∈ range (M + 1), (if Y + k = i then (1 : ℝ) else 0) * binom M q k =
        if i - Y = k then binom M q k else 0 := by
      intro k _
      by_cases hk : Y + k = i
      · rw [if_pos hk, if_pos (by omega), one_mul]
      · rw [if_neg hk, if_neg (by omega), zero_mul]
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq,
      show ((i : ℤ) - Y) = ((i - Y : ℕ) : ℤ) by omega]
    split_ifs with h
    · rfl
    · rw [Finset.mem_range] at h
      rw [binom_of_lt (by omega)]
  · rw [binom_of_neg (by omega)]
    exact Finset.sum_eq_zero fun k _ => by rw [if_neg (by omega), zero_mul]

end HardCore

open HardCore

namespace Mixture

variable {ι : Type*} (X : Mixture ι)

/-! ## Linearity of the expectation -/

theorem expect_add (g h : ℕ → ℕ → ℝ) :
    X.expect (fun M Y => g M Y + h M Y) = X.expect g + X.expect h := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem expect_sub (g h : ℕ → ℕ → ℝ) :
    X.expect (fun M Y => g M Y - h M Y) = X.expect g - X.expect h := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem expect_const_mul (c : ℝ) (g : ℕ → ℕ → ℝ) :
    X.expect (fun M Y => c * g M Y) = c * X.expect g := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem expect_const (c : ℝ) : X.expect (fun _ _ => c) = c * ∑ σ ∈ X.S, X.w σ := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem expect_congr {g h : ℕ → ℕ → ℝ}
    (hgh : ∀ σ ∈ X.S, g (X.M σ) (X.Y σ) = h (X.M σ) (X.Y σ)) : X.expect g = X.expect h := by
  unfold expect
  exact Finset.sum_congr rfl fun σ hσ => by rw [hgh σ hσ]

theorem expect_nonneg (hw : ∀ σ ∈ X.S, 0 ≤ X.w σ) {g : ℕ → ℕ → ℝ}
    (hg : ∀ σ ∈ X.S, 0 ≤ g (X.M σ) (X.Y σ)) : 0 ≤ X.expect g := by
  unfold expect
  exact Finset.sum_nonneg fun σ hσ => mul_nonneg (hw σ hσ) (hg σ hσ)

theorem expect_mono (hw : ∀ σ ∈ X.S, 0 ≤ X.w σ) {g h : ℕ → ℕ → ℝ}
    (hgh : ∀ σ ∈ X.S, g (X.M σ) (X.Y σ) ≤ h (X.M σ) (X.Y σ)) : X.expect g ≤ X.expect h := by
  unfold expect
  exact Finset.sum_le_sum fun σ hσ => mul_le_mul_of_nonneg_left (hgh σ hσ) (hw σ hσ)

/-! ## The law of `K` -/

/-- `P(K = i) = E b_M(i − Y)`. -/
theorem prob_eq_expect (q : ℝ) (i : ℤ) :
    X.prob q i = X.expect fun M Y => binom M q (i - (Y : ℤ)) := rfl

/-- `P(K = i) = 0` for `i < 0`. -/
theorem prob_of_neg (q : ℝ) {i : ℤ} (hi : i < 0) : X.prob q i = 0 := by
  unfold prob
  exact Finset.sum_eq_zero fun σ _ => by rw [binom_of_neg (by omega), mul_zero]

theorem prob_nonneg (hw : ∀ σ ∈ X.S, 0 ≤ X.w σ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : ℤ) :
    0 ≤ X.prob q i := by
  unfold prob
  exact Finset.sum_nonneg fun σ hσ => mul_nonneg (hw σ hσ) (binom_nonneg hq0 hq1 _)

/-- Sums against the law of `K` over a range `[0, N]` containing every `Y σ + [0, M σ]` are
expectations of the conditional binomial sums. -/
theorem sum_range_mul_prob (q : ℝ) (f : ℕ → ℝ) {N : ℕ} (hN : ∀ σ ∈ X.S, X.Y σ + X.M σ ≤ N) :
    ∑ i ∈ range (N + 1), f i * X.prob q i =
      X.expect fun M Y => ∑ k ∈ range (M + 1), f (Y + k) * binom M q k := by
  unfold prob expect
  calc ∑ i ∈ range (N + 1), f i * ∑ σ ∈ X.S, X.w σ * binom (X.M σ) q (i - (X.Y σ : ℤ))
      = ∑ σ ∈ X.S, X.w σ * ∑ i ∈ range (N + 1), f i * binom (X.M σ) q (i - (X.Y σ : ℤ)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => by ring
    _ = _ := Finset.sum_congr rfl fun σ hσ => by rw [sum_range_mul_binom_sub q f (hN σ hσ)]

/-- Total mass: `Σ_{i ≤ N} P_i = Σ_σ w σ`. -/
theorem sum_range_prob (q : ℝ) {N : ℕ} (hN : ∀ σ ∈ X.S, X.Y σ + X.M σ ≤ N) :
    ∑ i ∈ range (N + 1), X.prob q i = ∑ σ ∈ X.S, X.w σ := by
  have h := X.sum_range_mul_prob q (fun _ => 1) hN
  simp only [one_mul, sum_binom] at h
  rw [h, expect_const, one_mul]

/-- Mean: `Σ_{i ≤ N} i P_i = E[Y + qM]`. -/
theorem sum_range_mul_prob_self (q : ℝ) {N : ℕ} (hN : ∀ σ ∈ X.S, X.Y σ + X.M σ ≤ N) :
    ∑ i ∈ range (N + 1), (i : ℝ) * X.prob q i = X.expect fun M Y => (Y : ℝ) + q * M := by
  rw [X.sum_range_mul_prob q (fun i => (i : ℝ)) hN]
  simp only [sum_natCast_add_mul_binom]

/-- Second moment about any centre `c`: `Σ_{i ≤ N} (i − c)² P_i = E[(Y + qM − c)²] + q(1 − q) E M`. -/
theorem sum_range_sq_mul_prob (q c : ℝ) {N : ℕ} (hN : ∀ σ ∈ X.S, X.Y σ + X.M σ ≤ N) :
    ∑ i ∈ range (N + 1), ((i : ℝ) - c) ^ 2 * X.prob q i =
      X.expect (fun M Y => ((Y : ℝ) + q * M - c) ^ 2) + q * (1 - q) * X.meanM := by
  rw [X.sum_range_mul_prob q (fun i => ((i : ℝ) - c) ^ 2) hN, meanM, ← expect_const_mul,
    ← expect_add]
  simp only [sum_sq_sub_mul_binom]

/-- **The moments of `K` for a probability mixture.**  If the weights sum
to one and `[0, N]` contains every `Y σ + [0, M σ]`, then the law `P_i = X.prob q i` of `K` has total
mass `1`, mean `μ_K = E[Y + qM]`, and second central moment `E[(Y + qM − μ_K)²] + q(1 − q) E M`. -/
theorem moments_of_sum_eq_one (q : ℝ) {N : ℕ} (hN : ∀ σ ∈ X.S, X.Y σ + X.M σ ≤ N)
    (hw : ∑ σ ∈ X.S, X.w σ = 1) :
    ∑ i ∈ range (N + 1), X.prob q i = 1 ∧
      ∑ i ∈ range (N + 1), (i : ℝ) * X.prob q i = X.expect (fun M Y => (Y : ℝ) + q * M) ∧
      ∑ i ∈ range (N + 1),
          ((i : ℝ) - X.expect (fun M Y => (Y : ℝ) + q * M)) ^ 2 * X.prob q i =
        X.expect (fun M Y => ((Y : ℝ) + q * M - X.expect (fun M Y => (Y : ℝ) + q * M)) ^ 2) +
          q * (1 - q) * X.meanM :=
  ⟨(X.sum_range_prob q hN).trans hw, X.sum_range_mul_prob_self q hN,
    X.sum_range_sq_mul_prob q _ hN⟩

/-- `Var M = E M² − m²` for a probability mixture. -/
theorem varM_eq (hw : ∑ σ ∈ X.S, X.w σ = 1) :
    X.varM = X.expect (fun M _ => (M : ℝ) ^ 2) - X.meanM ^ 2 := by
  unfold varM
  have h1 : X.expect (fun M _ => ((M : ℝ) - X.meanM) ^ 2) =
      X.expect (fun M _ => (M : ℝ) ^ 2) - 2 * X.meanM * X.expect (fun M _ => (M : ℝ)) +
        X.meanM ^ 2 * ∑ σ ∈ X.S, X.w σ := by
    unfold expect
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [h1, hw, ← meanM]
  ring

end Mixture

end Erdos993Lean.Analytic
