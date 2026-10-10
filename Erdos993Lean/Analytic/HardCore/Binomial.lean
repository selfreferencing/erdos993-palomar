module

public import Mathlib
public import Erdos993Lean.Analytic.Defs

/-!
# Binomial point masses: total mass, mean, second moment, generating function, tilting

Sources: T. Zhang, *Exact Certificates
for Unimodality of Forest Independence Polynomials*, v1.1, equations (45)–(46); the note
T23 §1.

For the binomial point mass `binom M q j = C(M, j) q^j (1 − q)^(M − j)` of `Defs.lean` (zero outside
`0 ≤ j ≤ M`):

* `binom_natCast`: the closed form at every natural `j` (for `j > M` both sides vanish);
  `binom_of_neg`, `binom_of_lt`: vanishing outside `[0, M]`; `binom_nonneg` for `q ∈ [0, 1]`.
* `sum_binom`, `sum_mul_binom`, `sum_sq_mul_binom`: `Σ_j b_M(j) = 1`, `Σ_j j b_M(j) = qM` and
  `Σ_j j² b_M(j) = q(1 − q)M + q²M²` (evaluations of Mathlib's Bernstein identities);
  `sum_quad_mul_binom`: the same for a quadratic `a + bj + cj²`;
  `sum_pow_mul_binom`: the generating function `Σ_j s^j b_M(j) = (1 − q + qs)^M`.
* `one_add_pow_mul_binom`: the tilt `(1 + t)^M b_M(k; t/(1 + t)) = C(M, k) t^k`, and
  `sum_powerset_mul_pow`: `Σ_{T ⊆ A} g(|T|) t^|T| = (1 + t)^|A| Σ_{k ≤ |A|} g(k) b_|A|(k; t/(1 + t))`.
* `sum_range_mul_binom_sub`: the reindexing `Σ_{i ≤ N} f(i) b_M(i − Y) = Σ_{k ≤ M} f(Y + k) b_M(k)`
  for `Y + M ≤ N`.

Namespace: `Erdos993Lean.Analytic.HardCore` (a helper namespace, like `NoValley`
and `Tail`).

Grade: PROVED IN LEAN (standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.HardCore

open Finset

/-! ## The point mass at natural arguments -/

/-- The closed form of `binom` at a natural argument (for `j > M` both sides are `0`). -/
theorem binom_natCast (M : ℕ) (q : ℝ) (j : ℕ) :
    binom M q (j : ℤ) = (M.choose j : ℝ) * q ^ j * (1 - q) ^ (M - j) := by
  unfold binom
  by_cases h : j ≤ M
  · rw [if_pos ⟨Int.natCast_nonneg j, by exact_mod_cast h⟩, Int.toNat_natCast]
  · rw [if_neg (fun h' => h (by exact_mod_cast h'.2)), Nat.choose_eq_zero_of_lt (not_le.mp h)]
    simp

theorem binom_of_neg {M : ℕ} {q : ℝ} {j : ℤ} (hj : j < 0) : binom M q j = 0 := by
  unfold binom
  rw [if_neg (fun h => absurd h.1 (not_le.mpr hj))]

theorem binom_of_lt {M : ℕ} {q : ℝ} {j : ℤ} (hj : (M : ℤ) < j) : binom M q j = 0 := by
  unfold binom
  rw [if_neg (fun h => absurd h.2 (not_le.mpr hj))]

theorem binom_nonneg {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℤ) :
    0 ≤ binom M q j := by
  unfold binom
  split_ifs
  · have : 0 ≤ 1 - q := by linarith
    positivity
  · exact le_rfl

/-- `binom` at natural arguments is the value of Mathlib's Bernstein polynomial. -/
theorem binom_eq_eval_bernstein (M : ℕ) (q : ℝ) (j : ℕ) :
    binom M q (j : ℤ) = (bernsteinPolynomial ℝ M j).eval q := by
  rw [binom_natCast]
  simp [bernsteinPolynomial]

/-! ## Moment sums -/

/-- Total mass: `Σ_{j ≤ M} b_M(j) = 1`. -/
theorem sum_binom (M : ℕ) (q : ℝ) : ∑ k ∈ range (M + 1), binom M q k = 1 := by
  have h := congrArg (Polynomial.eval q) (bernsteinPolynomial.sum ℝ M)
  rw [Polynomial.eval_finset_sum, Polynomial.eval_one] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => binom_eq_eval_bernstein M q k

/-- Mean: `Σ_{j ≤ M} j b_M(j) = qM`. -/
theorem sum_mul_binom (M : ℕ) (q : ℝ) :
    ∑ k ∈ range (M + 1), (k : ℝ) * binom M q k = q * M := by
  have h := congrArg (Polynomial.eval q) (bernsteinPolynomial.sum_smul ℝ M)
  rw [Polynomial.eval_finset_sum] at h
  simp only [nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] at h
  rw [mul_comm q, ← h]
  exact Finset.sum_congr rfl fun k _ => by rw [binom_eq_eval_bernstein]

/-- Second moment: `Σ_{j ≤ M} j² b_M(j) = q(1 − q)M + q²M²`. -/
theorem sum_sq_mul_binom (M : ℕ) (q : ℝ) :
    ∑ k ∈ range (M + 1), (k : ℝ) ^ 2 * binom M q k = q * (1 - q) * M + q ^ 2 * M ^ 2 := by
  have h := congrArg (Polynomial.eval q) (bernsteinPolynomial.variance ℝ M)
  rw [Polynomial.eval_finset_sum] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_natCast, Polynomial.eval_one, nsmul_eq_mul] at h
  have h2 : ∑ k ∈ range (M + 1), ((M : ℝ) * q - k) ^ 2 * binom M q k = M * q * (1 - q) := by
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by rw [binom_eq_eval_bernstein]
  have e : ∀ k ∈ range (M + 1), (k : ℝ) ^ 2 * binom M q k =
      ((M : ℝ) * q - k) ^ 2 * binom M q k - ((M : ℝ) * q) ^ 2 * binom M q k +
        2 * ((M : ℝ) * q) * ((k : ℝ) * binom M q k) := by
    intro k _
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, h2, sum_binom, sum_mul_binom]
  ring

/-- The moments of a quadratic: `Σ_j (a + bj + cj²) b_M(j) = a + b qM + c (q(1 − q)M + q²M²)`. -/
theorem sum_quad_mul_binom (M : ℕ) (q a b c : ℝ) :
    ∑ k ∈ range (M + 1), (a + b * k + c * (k : ℝ) ^ 2) * binom M q k =
      a + b * (q * M) + c * (q * (1 - q) * M + q ^ 2 * M ^ 2) := by
  have e : ∀ k ∈ range (M + 1), (a + b * k + c * (k : ℝ) ^ 2) * binom M q k =
      a * binom M q k + b * ((k : ℝ) * binom M q k) + c * ((k : ℝ) ^ 2 * binom M q k) := by
    intro k _
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_binom, sum_mul_binom, sum_sq_mul_binom, mul_one]

/-- The generating function: `Σ_{j ≤ M} s^j b_M(j) = (1 − q + qs)^M`. -/
theorem sum_pow_mul_binom (M : ℕ) (q s : ℝ) :
    ∑ k ∈ range (M + 1), s ^ k * binom M q k = (1 - q + q * s) ^ M := by
  rw [show 1 - q + q * s = q * s + (1 - q) by ring, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [binom_natCast, mul_pow]
  ring

/-! ## The activity-to-probability map and tilting -/

theorem one_add_mul_actQ {t : ℝ} (ht : 1 + t ≠ 0) : (1 + t) * actQ t = t := by
  unfold actQ
  field_simp

theorem one_add_mul_one_sub_actQ {t : ℝ} (ht : 1 + t ≠ 0) : (1 + t) * (1 - actQ t) = 1 := by
  rw [mul_sub, mul_one, one_add_mul_actQ ht]
  ring

theorem actQ_pos {t : ℝ} (ht : 0 < t) : 0 < actQ t := by
  unfold actQ
  positivity

theorem actQ_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ actQ t := by
  unfold actQ
  positivity

theorem actQ_lt_one {t : ℝ} (ht : 0 ≤ t) : actQ t < 1 := by
  unfold actQ
  rw [div_lt_one (by linarith)]
  linarith

theorem one_sub_actQ_pos {t : ℝ} (ht : 0 ≤ t) : 0 < 1 - actQ t := by
  have := actQ_lt_one ht
  linarith

/-- **The tilt**: `(1 + t)^M b_M(k; t/(1 + t)) = C(M, k) t^k` for `k ≤ M`. -/
theorem one_add_pow_mul_binom {t : ℝ} (ht : 1 + t ≠ 0) {M k : ℕ} (hk : k ≤ M) :
    (1 + t) ^ M * binom M (actQ t) k = (M.choose k : ℝ) * t ^ k := by
  have hM : (1 + t) ^ M = (1 + t) ^ k * (1 + t) ^ (M - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [binom_natCast, hM]
  calc (1 + t) ^ k * (1 + t) ^ (M - k) * ((M.choose k : ℝ) * actQ t ^ k * (1 - actQ t) ^ (M - k))
      = (M.choose k : ℝ) * ((1 + t) * actQ t) ^ k * ((1 + t) * (1 - actQ t)) ^ (M - k) := by
        rw [mul_pow, mul_pow]
        ring
    _ = (M.choose k : ℝ) * t ^ k := by
        rw [one_add_mul_actQ ht, one_add_mul_one_sub_actQ ht, one_pow, mul_one]

/-- Sums over the subsets of a finite set, grouped by size and tilted:
`Σ_{T ⊆ A} g(|T|) t^|T| = (1 + t)^|A| Σ_{k ≤ |A|} g(k) b_|A|(k; t/(1 + t))`. -/
theorem sum_powerset_mul_pow {α : Type*} (A : Finset α) (g : ℕ → ℝ) {t : ℝ} (ht : 1 + t ≠ 0) :
    ∑ T ∈ A.powerset, g T.card * t ^ T.card =
      (1 + t) ^ A.card * ∑ k ∈ range (A.card + 1), g k * binom A.card (actQ t) k := by
  rw [Finset.sum_powerset_apply_card (fun m => g m * t ^ m), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ A.card := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [nsmul_eq_mul, show ((A.card.choose k : ℕ) : ℝ) * (g k * t ^ k) =
      g k * ((A.card.choose k : ℝ) * t ^ k) by ring, ← one_add_pow_mul_binom ht hk']
  ring

/-! ## Reindexing -/

/-- Shifting a binomial point mass: `Σ_{i ≤ N} f(i) b_M(i − Y) = Σ_{k ≤ M} f(Y + k) b_M(k)` when
`Y + M ≤ N`. -/
theorem sum_range_mul_binom_sub (q : ℝ) (f : ℕ → ℝ) {M Y N : ℕ} (h : Y + M ≤ N) :
    ∑ i ∈ range (N + 1), f i * binom M q ((i : ℤ) - Y) =
      ∑ k ∈ range (M + 1), f (Y + k) * binom M q k := by
  have hsub : (range (M + 1)).map (addLeftEmbedding Y) ⊆ range (N + 1) := by
    intro i hi
    simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply] at hi ⊢
    obtain ⟨k, hk, rfl⟩ := hi
    omega
  have hzero : ∀ i ∈ range (N + 1), i ∉ (range (M + 1)).map (addLeftEmbedding Y) →
      f i * binom M q ((i : ℤ) - Y) = 0 := by
    intro i _ hi
    simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply, not_exists,
      not_and] at hi
    rcases lt_or_ge i Y with hiY | hiY
    · rw [binom_of_neg (by omega), mul_zero]
    · have hlt : M + 1 ≤ i - Y := by
        by_contra hc
        exact hi (i - Y) (by omega) (by omega)
      rw [binom_of_lt (by omega), mul_zero]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_map]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [addLeftEmbedding_apply, Nat.cast_add, add_sub_cancel_left]

end Erdos993Lean.Analytic.HardCore
