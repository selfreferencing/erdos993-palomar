module

public import Mathlib
public import Erdos993Lean.Analytic.HardCore.Basic
public import Erdos993Lean.Analytic.HardCore.Moments

/-!
# The conditional binomial mixture of the hard-core model of a forest (Zhang (45)–(46))

Sources: T. Zhang, *Exact Certificates
for Unimodality of Forest Independence Polynomials*, v1.1, equations (45)–(46); the note
T23 §1.

Fix a forest `F`, an activity `t > 0`, `q = t/(1 + t)` and an independent set `B`.  The hard-core
model draws an independent set `S` with probability `t^|S| / Z_F(t)`; its parts are `σ = S \ B` (a
state of `forestMixture F B t`) and `S ∩ B ⊆ free(σ)`.

* **The master formula** `expect_eq_sum_indepSets`: for every `g : ℕ → ℕ → ℝ`,
  `E_hc[g(|S \ B|, |S ∩ B|)] = E_mix[Σ_{k ≤ M} g(Y, k) b_M(k; q)]`, i.e. conditionally on `σ` the
  set `S ∩ B` is a uniform-`q` subset of `free(σ)` (so `|S ∩ B| ~ Bin(M σ, q)`) and `|S \ B| = Y σ`.
  It follows from the decomposition `sum_indepSets_eq_sum_states` and the tilt
  `(1 + t)^M b_M(k; q) = C(M, k) t^k`.
* Its instances: `forestMixture_isProb` (`g = 1`), `forestMixture_prob_eq`
  (`g = [y + k = i]`: `P(K = i) = i_i t^i / Z`), `hardCoreMean_eq_expect` (`μ = E[Y + qM]`),
  `hardCoreVar_eq_expect` (`V = E[(Y + qM − μ)²] + q(1 − q) m`, the law of total variance),
  `forestMixture_weight_eq` (`g = k`: `q m = W`).
* Zhang (46): `forestMixture_mean_delta` (`E δ = 0` at `μ = k`) and `forestMixture_var_delta`
  (`E δ² = V − q(1 − q) m`).
* **`mixtureFacts : MixtureFacts`** (`Defs.lean`), the main target of this file.

Namespaces: `mixtureFacts` is `Erdos993Lean.Analytic.mixtureFacts`; everything else is in
`Erdos993Lean.Analytic.HardCore`.

Grade: PROVED IN LEAN (standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean.Analytic

open Finset

namespace HardCore

variable (F : FiniteForest)

/-! ## The master formula -/

/-- The master formula before normalization:
`Σ_{S indep} g(|S \ B|, |S ∩ B|) t^|S| = Σ_σ t^|σ| (1 + t)^M(σ) Σ_{k ≤ M(σ)} g(|σ|, k) b_M(σ)(k; q)`. -/
theorem sum_indepSets_eq_sum_states_binom {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (g : ℕ → ℕ → ℝ) :
    ∑ S ∈ indepSets F, g (S \ B).card (S ∩ B).card * t ^ S.card =
      ∑ σ ∈ states F B, t ^ σ.card * (1 + t) ^ freeCount F B σ *
        ∑ k ∈ range (freeCount F B σ + 1), g σ.card k * binom (freeCount F B σ) (actQ t) k := by
  have ht' : (1 + t) ≠ 0 := by positivity
  rw [sum_indepSets_eq_sum_states F hB]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have key : ∀ T ∈ (freeSet F B σ).powerset,
      g ((σ ∪ T) \ B).card ((σ ∪ T) ∩ B).card * t ^ (σ ∪ T).card =
        t ^ σ.card * (g σ.card T.card * t ^ T.card) := by
    intro T hT
    obtain ⟨h1, h2, h3⟩ := union_parts F hσ (Finset.mem_powerset.mp hT)
    rw [h1, h2, h3, pow_add]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum,
    sum_powerset_mul_pow (freeSet F B σ) (g σ.card) ht', ← freeCount_eq_card]
  ring

/-- **The master formula (Zhang (45)).**  For an independent set `B` and `t > 0`, the hard-core
expectation of any function of `(|S \ B|, |S ∩ B|)` is the mixture expectation of its conditional
binomial expectation: `E_hc[g(|S \ B|, |S ∩ B|)] = E_mix[Σ_{k ≤ M} g(Y, k) b_M(k; q)]`. -/
theorem expect_eq_sum_indepSets {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (g : ℕ → ℕ → ℝ) :
    (forestMixture F B t).expect (fun M Y => ∑ k ∈ range (M + 1), g Y k * binom M (actQ t) k) =
      (∑ S ∈ indepSets F, g (S \ B).card (S ∩ B).card * t ^ S.card) / partitionFn F t := by
  rw [sum_indepSets_eq_sum_states_binom F hB ht g, Finset.sum_div]
  unfold Mixture.expect
  simp only [forestMixture_S, forestMixture_w, forestMixture_M, forestMixture_Y]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-! ## The mixture is a probability mixture, and the law of `K` -/

/-- `Σ_σ w σ = 1`. -/
theorem forestMixture_sum_w {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) :
    ∑ σ ∈ (forestMixture F B t).S, (forestMixture F B t).w σ = 1 := by
  have h := expect_eq_sum_indepSets F hB ht (fun _ _ => 1)
  simp only [one_mul, sum_binom] at h
  rw [← partitionFn_eq_sum, div_self (partitionFn_pos F ht.le).ne',
    Mixture.expect_const, one_mul] at h
  exact h

/-- **The forest mixture is a probability mixture** (the Z-identity
`Σ_σ t^|σ| (1 + t)^M(σ) = Z_F(t)`). -/
theorem forestMixture_isProb {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) :
    (forestMixture F B t).IsProb := by
  refine ⟨fun σ _ => ?_, forestMixture_sum_w F hB ht⟩
  rw [forestMixture_w]
  exact div_nonneg (by positivity) (partitionFn_pos F ht.le).le

/-- Every state satisfies `Y σ + M σ ≤ n`. -/
theorem forestMixture_support (B : Finset (Fin F.n)) (t : ℝ) :
    ∀ σ ∈ (forestMixture F B t).S, (forestMixture F B t).Y σ + (forestMixture F B t).M σ ≤ F.n :=
  fun _ hσ => card_add_freeCount_le F hσ

/-- **The law of `K` (Zhang (45)).**  `P(K = i) = i_i t^i / Z_F(t)` for every natural `i`. -/
theorem forestMixture_prob_eq {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (i : ℕ) :
    (forestMixture F B t).prob (actQ t) i =
      (independenceCount F i : ℝ) * t ^ i / partitionFn F t := by
  have h := expect_eq_sum_indepSets F hB ht (fun y k => if y + k = i then 1 else 0)
  simp only [sum_ite_mul_binom] at h
  rw [Mixture.prob_eq_expect, h]
  congr 1
  rw [← sum_indepSets_card_eq F t i]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.card_sdiff_add_card_inter]
  split_ifs <;> simp

/-- `P(K = i) = 0` for every integer `i < 0`. -/
theorem forestMixture_prob_of_neg (B : Finset (Fin F.n)) (t : ℝ) {i : ℤ} (hi : i < 0) :
    (forestMixture F B t).prob (actQ t) i = 0 :=
  Mixture.prob_of_neg _ _ hi

/-! ## Mean, variance and weight -/

/-- `μ_F(t) = E[Y + qM]`. -/
theorem hardCoreMean_eq_expect {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) :
    hardCoreMean F t = (forestMixture F B t).expect fun M Y => (Y : ℝ) + actQ t * M := by
  have h := expect_eq_sum_indepSets F hB ht (fun y k => ((y + k : ℕ) : ℝ))
  simp only [sum_natCast_add_mul_binom] at h
  rw [h, hardCoreMean_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.card_sdiff_add_card_inter]

/-- **The law of total variance for the mixture**: `V = E[(Y + qM − μ)²] + q(1 − q) m`. -/
theorem hardCoreVar_eq_expect {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) :
    hardCoreVar F t =
      (forestMixture F B t).expect (fun M Y => ((Y : ℝ) + actQ t * M - hardCoreMean F t) ^ 2) +
        actQ t * (1 - actQ t) * (forestMixture F B t).meanM := by
  have h := expect_eq_sum_indepSets F hB ht
    (fun y k => (((y + k : ℕ) : ℝ) - hardCoreMean F t) ^ 2)
  simp only [sum_sq_sub_mul_binom] at h
  rw [hardCoreVar_eq_sum, Mixture.meanM, ← Mixture.expect_const_mul, ← Mixture.expect_add, h]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.card_sdiff_add_card_inter]

/-- **Zhang (46), first half**: at `μ_F(t) = k`, `E δ = 0`. -/
theorem forestMixture_mean_delta {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (k : ℕ)
    (hk : hardCoreMean F t = k) :
    (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y) = 0 := by
  have e : (fun M Y => delta (actQ t) k M Y) =
      fun (M Y : ℕ) => (k : ℝ) - ((Y : ℝ) + actQ t * M) := by
    funext M Y
    unfold delta
    push_cast
    ring
  rw [e, Mixture.expect_sub, Mixture.expect_const, forestMixture_sum_w F hB ht,
    ← hardCoreMean_eq_expect F hB ht, hk]
  ring

/-- **Zhang (46), second half**: at `μ_F(t) = k`, `E δ² = V − q(1 − q) m`. -/
theorem forestMixture_var_delta {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (k : ℕ)
    (hk : hardCoreMean F t = k) :
    (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y ^ 2) =
      hardCoreVar F t - actQ t * (1 - actQ t) * (forestMixture F B t).meanM := by
  rw [hardCoreVar_eq_expect F hB ht, hk]
  have e : (fun M Y => delta (actQ t) k M Y ^ 2) =
      fun (M Y : ℕ) => ((Y : ℝ) + actQ t * M - k) ^ 2 := by
    funext M Y
    unfold delta
    push_cast
    ring
  rw [e]
  ring

/-- **Zhang (45): `q m = W`.**  Given `σ`, each free `B`-vertex is occupied with probability `q` and
a blocked one never is, so `Σ_{b ∈ B} π_b = E|S ∩ B| = q E M`. -/
theorem forestMixture_weight_eq {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) :
    actQ t * (forestMixture F B t).meanM = weightW F t B := by
  have h := expect_eq_sum_indepSets F hB ht (fun _ k => (k : ℝ))
  simp only [sum_mul_binom] at h
  rw [weightW_eq_sum, ← h, Mixture.meanM, ← Mixture.expect_const_mul]

end HardCore

open HardCore

/-! ## The main target -/

/-- **The main target: the facts about the forest mixture used by the assembly**
(Zhang (45)–(46)): maximum-weight sets exist; for every independent `B` and `t > 0` the forest
mixture is a probability mixture whose `K`-law is `i_i t^i / Z_F(t)`; at `μ_F(t) = k`,
`E δ = 0` and `E δ² = V − q(1 − q) m`; and `q m = W`. -/
theorem mixtureFacts : MixtureFacts where
  exists_maxWeight := fun F t _ => exists_isMaxWeight F t
  isProb := fun F _ _ ht hB => forestMixture_isProb F hB ht
  prob_eq := fun F _ _ ht hB i => forestMixture_prob_eq F hB ht i
  mean_delta := fun F _ _ ht hB k hk => forestMixture_mean_delta F hB ht k hk
  var_delta := fun F _ _ ht hB k hk => forestMixture_var_delta F hB ht k hk
  weight_eq := fun F _ _ ht hB => forestMixture_weight_eq F hB ht

end Erdos993Lean.Analytic
