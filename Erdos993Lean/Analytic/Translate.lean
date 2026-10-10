module

public import Erdos993Lean.Analytic.Defs
public import Erdos993Lean.Ceiling.Join

/-!
# From a weak valley of the counts to a weak valley of the mixture

Interface: `Analytic/Defs.lean`.
Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*, v1.1,
(45)–(46): the law of the size `K` of the hard-core set at activity `t` is
`P(K = i) = c_i t^i / Z_F(t)`, and the forest mixture reproduces it (`MixtureFacts.prob_eq`).

With `q = t/(1 + t)` one has `q/(1 − q) = t`, so for `P_i = c_i t^i / Z` with `Z > 0`:
`(1 − q) P_k ≤ q P_{k−1} ⇔ c_k ≤ c_{k−1}` and `q P_k ≤ (1 − q) P_{k+1} ⇔ c_k ≤ c_{k+1}`.

* `actQ_pos`, `actQ_lt_one`, `one_sub_actQ`: `0 < q < 1` and `1 − q = 1/(1 + t)` for `t > 0`.
* `weakValley_of_le`: if a mixture has `P(K = i) = c_i t^i / Z` for `i = k − 1, k, k + 1`
  (`t, Z > 0`, `k ≥ 1`), then `c_k ≤ c_{k−1}` and `c_k ≤ c_{k+1}` give a weak valley of the mixture
  at `k` (`Mixture.WeakValley`).
* `not_valley_of_not_weakValley`: the forest form (`c = independenceCount F`, `Z = Z_F(t)`): if the
  mixture has no weak valley at `k`, the independence sequence has none either, i.e.
  `¬ (i_k ≤ i_{k−1} ∧ i_k ≤ i_{k+1})`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic

theorem actQ_pos {t : ℝ} (ht : 0 < t) : 0 < actQ t := by
  unfold actQ
  have : 0 < 1 + t := by linarith
  positivity

theorem actQ_lt_one {t : ℝ} (ht : 0 ≤ t) : actQ t < 1 := by
  unfold actQ
  rw [div_lt_one (by linarith)]
  linarith

/-- `1 − q = 1/(1 + t)` for `q = t/(1 + t)` (so `q/(1 − q) = t`). -/
theorem one_sub_actQ {t : ℝ} (ht : 0 ≤ t) : 1 - actQ t = 1 / (1 + t) := by
  unfold actQ
  have h1 : (1 + t) ≠ 0 := by linarith
  field_simp
  ring

/-- **Weak valleys transfer from the counts to the mixture.**  If the mixture has
`P(K = i) = c_i t^i / Z` for `i = k − 1, k, k + 1` (`t > 0`, `Z > 0`, `k ≥ 1`), then `c_k ≤ c_{k−1}`
and `c_k ≤ c_{k+1}` make `k` a weak valley of the mixture at `q = t/(1 + t)`. -/
theorem weakValley_of_le {ι : Type*} (X : Mixture ι) {t Z : ℝ} (ht : 0 < t) (hZ : 0 < Z)
    (c : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hprev : X.prob (actQ t) ((k - 1 : ℕ) : ℤ) = c (k - 1) * t ^ (k - 1) / Z)
    (hcur : X.prob (actQ t) (k : ℤ) = c k * t ^ k / Z)
    (hnext : X.prob (actQ t) ((k + 1 : ℕ) : ℤ) = c (k + 1) * t ^ (k + 1) / Z)
    (h1 : c k ≤ c (k - 1)) (h2 : c k ≤ c (k + 1)) :
    X.WeakValley (actQ t) k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hprev h1
  have e1 : ((j + 1 : ℕ) : ℤ) - 1 = ((j : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((j + 1 : ℕ) : ℤ) + 1 = ((j + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
  have h1t : 0 < 1 + t := by linarith
  have h1t' : (1 + t) ≠ 0 := h1t.ne'
  have hZ' : Z ≠ 0 := hZ.ne'
  have hq : actQ t = t / (1 + t) := rfl
  have hq1 : 1 - actQ t = 1 / (1 + t) := one_sub_actQ ht.le
  have hD : 0 < (1 + t) * Z := by positivity
  unfold Mixture.WeakValley
  rw [e1, e2, hprev, hcur, hnext]
  constructor
  · have eL : (1 - actQ t) * (c (j + 1) * t ^ (j + 1) / Z) =
        c (j + 1) * t ^ (j + 1) / ((1 + t) * Z) := by
      rw [hq1]
      field_simp
    have eR : actQ t * (c j * t ^ j / Z) = c j * t ^ (j + 1) / ((1 + t) * Z) := by
      rw [hq]
      field_simp
      ring
    rw [eL, eR]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hD.le
  · have eL : actQ t * (c (j + 1) * t ^ (j + 1) / Z) =
        c (j + 1) * t ^ (j + 1 + 1) / ((1 + t) * Z) := by
      rw [hq]
      field_simp
      ring
    have eR : (1 - actQ t) * (c (j + 1 + 1) * t ^ (j + 1 + 1) / Z) =
        c (j + 1 + 1) * t ^ (j + 1 + 1) / ((1 + t) * Z) := by
      rw [hq1]
      field_simp
    rw [eL, eR]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) hD.le

/-- **The weak-valley translation** (forest form).  Let `t > 0`, `k ≥ 1`, and let a mixture have
`P(K = i) = i_F(i) t^i / Z_F(t)` for `i = k − 1, k, k + 1` (as `forestMixture` does,
`MixtureFacts.prob_eq`).  If the mixture has no weak valley at `k` for `q = t/(1 + t)`, then the
independence sequence has no weak valley at `k`: not both `i_k ≤ i_{k−1}` and `i_k ≤ i_{k+1}`. -/
theorem not_valley_of_not_weakValley (F : FiniteForest) {ι : Type*} (X : Mixture ι) {t : ℝ}
    (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k)
    (hprev : X.prob (actQ t) ((k - 1 : ℕ) : ℤ) =
      (independenceCount F (k - 1) : ℝ) * t ^ (k - 1) / partitionFn F t)
    (hcur : X.prob (actQ t) (k : ℤ) =
      (independenceCount F k : ℝ) * t ^ k / partitionFn F t)
    (hnext : X.prob (actQ t) ((k + 1 : ℕ) : ℤ) =
      (independenceCount F (k + 1) : ℝ) * t ^ (k + 1) / partitionFn F t)
    (hnv : ¬ X.WeakValley (actQ t) k) :
    ¬ (independenceCount F k ≤ independenceCount F (k - 1) ∧
        independenceCount F k ≤ independenceCount F (k + 1)) := by
  rintro ⟨h1, h2⟩
  have hZ : 0 < partitionFn F t := lt_of_lt_of_le one_pos (Join.one_le_partitionFn F ht.le)
  have h1' : (independenceCount F k : ℝ) ≤ independenceCount F (k - 1) := by exact_mod_cast h1
  have h2' : (independenceCount F k : ℝ) ≤ independenceCount F (k + 1) := by exact_mod_cast h2
  exact hnv (weakValley_of_le X ht hZ (fun i => (independenceCount F i : ℝ)) hk hprev hcur hnext
    h1' h2')

end Erdos993Lean.Analytic
