module

public import Mathlib
public import Erdos993Lean.Analytic.HardCore.Mixture

/-!
# The variance of the free count `M`

Source: the note
T23 §1: "`Var M = (Var K_B − (1 − q)W)/q²`,
`K_B = |S ∩ B|`; `D := Var M / m`", and "`E δ² = V − (1 − q)W`; `θ = V/((1 − q)W) − 1`".

For a forest `F`, an independent set `B`, `t > 0` and `q = t/(1 + t)`:

* `varKB F t B = Var K_B`, the hard-core variance of `K_B = |S ∩ B|` (whose mean is `W`,
  `weightW_eq_sum`);
* `varKB_eq_expect`: `Var K_B = E[(qM − W)² + q(1 − q)M]` (conditionally on `σ`,
  `K_B ~ Bin(M σ, q)`);
* **E5** `forestMixture_varM`: `Var M = (Var K_B − (1 − q) W) / q²`;
* `forestMixture_var_delta_le`: the input O2 in the form T1 consumes — at `μ_F(t) = k`,
  `V ≤ (1 + θ)(1 − q) W` gives `E δ² ≤ θ q(1 − q) m` (from Zhang (46) and `qm = W`).

Scalarity: `θ` summarizes the second moment of `δ` (produced by O2 as a bound on `V`, consumed by the
no-valley lemma through `NoValleyAt`); `Var M` (the object behind `D`, input O1) is expressed here
through `Var K_B` and `W`.

Namespace: `Erdos993Lean.Analytic.HardCore`.

Grade: PROVED IN LEAN (standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.HardCore

open Finset

/-- `Σ_{k ≤ M} (k − c)² b_M(k) = (qM − c)² + q(1 − q)M`. -/
theorem sum_sq_sub_mul_binom' (M : ℕ) (q c : ℝ) :
    ∑ k ∈ range (M + 1), ((k : ℝ) - c) ^ 2 * binom M q k =
      (q * M - c) ^ 2 + q * (1 - q) * M := by
  have e : ∀ k ∈ range (M + 1), ((k : ℝ) - c) ^ 2 * binom M q k =
      (c ^ 2 + (-2 * c) * k + 1 * (k : ℝ) ^ 2) * binom M q k := by
    intro k _
    ring
  rw [Finset.sum_congr rfl e, sum_quad_mul_binom]
  ring

variable (F : FiniteForest)

/-- `Var K_B`: the hard-core variance of `K_B = |S ∩ B|` (its mean is `W = weightW F t B`). -/
noncomputable def varKB (t : ℝ) (B : Finset (Fin F.n)) : ℝ :=
  (∑ S ∈ indepSets F, (((S ∩ B).card : ℝ) - weightW F t B) ^ 2 * t ^ S.card) / partitionFn F t

/-- `Var K_B = E[(qM − W)² + q(1 − q)M]`. -/
theorem varKB_eq_expect {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) :
    varKB F t B = (forestMixture F B t).expect
      (fun M _ => (actQ t * M - weightW F t B) ^ 2 + actQ t * (1 - actQ t) * M) := by
  have h := expect_eq_sum_indepSets F hB ht (fun _ k => ((k : ℝ) - weightW F t B) ^ 2)
  simp only [sum_sq_sub_mul_binom'] at h
  rw [h]
  rfl

/-- **E5, the `Var M` formula (T23 §1).**  `Var M = (Var K_B − (1 − q) W) / q²`. -/
theorem forestMixture_varM {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) :
    (forestMixture F B t).varM = (varKB F t B - (1 - actQ t) * weightW F t B) / actQ t ^ 2 := by
  have hq := actQ_pos ht
  set X := forestMixture F B t with hX
  have hW : weightW F t B = actQ t * X.meanM := (forestMixture_weight_eq F hB ht).symm
  have key : X.expect (fun M _ => (actQ t * M - weightW F t B) ^ 2 + actQ t * (1 - actQ t) * M) =
      actQ t ^ 2 * X.varM + actQ t * (1 - actQ t) * X.meanM := by
    calc X.expect (fun M _ => (actQ t * M - weightW F t B) ^ 2 + actQ t * (1 - actQ t) * M)
        = X.expect (fun M _ => actQ t ^ 2 * ((M : ℝ) - X.meanM) ^ 2 +
            actQ t * (1 - actQ t) * (M : ℝ)) := by
          congr 1
          funext M _
          rw [hW]
          ring
      _ = X.expect (fun M _ => actQ t ^ 2 * ((M : ℝ) - X.meanM) ^ 2) +
            X.expect (fun M _ => actQ t * (1 - actQ t) * (M : ℝ)) := X.expect_add _ _
      _ = actQ t ^ 2 * X.varM + actQ t * (1 - actQ t) * X.meanM := by
          rw [X.expect_const_mul, X.expect_const_mul]
          rfl
  rw [eq_div_iff (by positivity), varKB_eq_expect F hB ht, ← hX, key, hW]
  ring

/-- **O2 in T1's form.**  At `μ_F(t) = k`, the variance-ratio bound `V ≤ (1 + θ)(1 − q) W` gives
`E δ² ≤ θ q(1 − q) m` (Zhang (46) and `qm = W`). -/
theorem forestMixture_var_delta_le {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (k : ℕ)
    (hk : hardCoreMean F t = k) {θ : ℝ}
    (hV : hardCoreVar F t ≤ (1 + θ) * (1 - actQ t) * weightW F t B) :
    (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
      θ * (actQ t * (1 - actQ t)) * (forestMixture F B t).meanM := by
  rw [forestMixture_var_delta F hB ht k hk]
  rw [← forestMixture_weight_eq F hB ht] at hV
  linarith

end Erdos993Lean.Analytic.HardCore
