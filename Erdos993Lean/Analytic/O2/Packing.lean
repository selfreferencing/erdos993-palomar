module

public import Erdos993Lean.Analytic.O2.Defs

/-!
# O2: the packed child-mass bounds (7) and (8), and the child Cauchy residuals

Source: the O2 proof, §4
(eqs. (7), (8): the original child list has logarithmic masses `y_u = −log(1 − p_u) ∈ (0, L]`,
`L = log(1 + λ)`, with total exactly `T`; convexity of `e^y − 1` and concavity of `1 − e^{−y}`, by
moving mass between two coordinates, give `∑ p_u/(1 − p_u) ≤ H` and `∑ p_u ≥ φ`; the extremal
arrangement is `j` full masses `L` and a residual `T − jL`) and Lemma 3 / Theorem 5 (the Cauchy
residuals `Δ_u, Δ_v, Δ_s ≥ 0`).

* `exp_two_point`: `e^{cx} + e^{cy} ≤ e^{c·lo} + e^{c·hi}` when `lo ≤ x ≤ hi`, `x + y = lo + hi`
  (the exact identity `e^{c lo}(1 − e^{c(x−lo)})(1 − e^{c(hi−x)}) ≥ 0`);
* `packB c L T = j (e^{cL} − 1) + (e^{c(T − jL)} − 1)`, `j = ⌊T/L⌋₊`, and **`sum_le_packB`**: for
  every finite list of masses `y_i ∈ [0, L]`, `∑ (e^{c y_i} − 1) ≤ packB c L (∑ y_i)` (no degree
  bound; induction on the list, one mass at a time);
* `packH_eq`, `packPhi_eq`: `H = packB 1 L T` and `φ = −packB (−1) L T`;
* the Cauchy residuals: `sq_div_le_of_le_sum` (`b ≤ ∑ a_i` gives `b²/∑ y_i ≤ ∑ a_i²/y_i`) and
  `sq_div_le_of_le_odds` (`(∑ p_i z_i)²/H ≤ ∑ p_i(1 − p_i) z_i²` when `∑ p_i/(1 − p_i) ≤ H`).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.O2

open Finset Real

/-! ### Two-point exchange -/

/-- **Two-point exchange** for `y ↦ e^{cy}` (convex): moving the pair `(x, y)` apart to `(lo, hi)`
with the same sum does not decrease `e^{cx} + e^{cy}`. -/
theorem exp_two_point {c lo hi x y : ℝ} (hx1 : lo ≤ x) (hx2 : x ≤ hi) (hxy : x + y = lo + hi) :
    exp (c * x) + exp (c * y) ≤ exp (c * lo) + exp (c * hi) := by
  have ex : exp (c * x) = exp (c * lo) * exp (c * (x - lo)) := by
    rw [← exp_add]; ring_nf
  have ehi : exp (c * hi) = exp (c * lo) * exp (c * (x - lo)) * exp (c * (hi - x)) := by
    rw [← exp_add, ← exp_add]; ring_nf
  have ey : exp (c * y) = exp (c * lo) * exp (c * (hi - x)) := by
    rw [← exp_add]
    have hy : y = lo + hi - x := by linarith
    rw [hy]; ring_nf
  have ha := exp_pos (c * lo)
  rw [ex, ehi, ey]
  rcases le_total 0 c with hc | hc
  · have hu : 1 ≤ exp (c * (x - lo)) := one_le_exp (mul_nonneg hc (by linarith))
    have hw : 1 ≤ exp (c * (hi - x)) := one_le_exp (mul_nonneg hc (by linarith))
    nlinarith [mul_nonneg ha.le (mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hw))]
  · have hu : exp (c * (x - lo)) ≤ 1 := exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hc (by linarith))
    have hw : exp (c * (hi - x)) ≤ 1 := exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hc (by linarith))
    nlinarith [mul_nonneg ha.le (mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hw))]

/-! ### The packed extremal value -/

/-- The packed extremal value `j (e^{cL} − 1) + (e^{c(T − jL)} − 1)`, `j = ⌊T/L⌋₊`: `j` full masses
`L` and one residual mass `T − jL`. -/
noncomputable def packB (c L T : ℝ) : ℝ :=
  (⌊T / L⌋₊ : ℝ) * (exp (c * L) - 1) + (exp (c * (T - (⌊T / L⌋₊ : ℝ) * L)) - 1)

/-- **One mass at a time**: adding a mass `y ∈ [0, L]` to a total `T ≥ 0`. -/
theorem packB_step {c L T y : ℝ} (hL : 0 < L) (hT : 0 ≤ T) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    (exp (c * y) - 1) + packB c L T ≤ packB c L (T + y) := by
  unfold packB
  have hTL : 0 ≤ T / L := div_nonneg hT hL.le
  have hk1 : ((⌊T / L⌋₊ : ℕ) : ℝ) ≤ T / L := Nat.floor_le hTL
  have hk2 : T / L < (⌊T / L⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  set k := ⌊T / L⌋₊ with hk
  have hk1' : (k : ℝ) * L ≤ T := by rwa [le_div_iff₀ hL] at hk1
  have hk2' : T < ((k : ℝ) + 1) * L := by rwa [div_lt_iff₀ hL] at hk2
  have hTyL : 0 ≤ (T + y) / L := div_nonneg (by linarith) hL.le
  by_cases hcase : T - k * L + y < L
  · have hfl : ⌊(T + y) / L⌋₊ = k := by
      rw [Nat.floor_eq_iff hTyL]
      constructor
      · rw [le_div_iff₀ hL]; linarith
      · rw [div_lt_iff₀ hL]; linarith
    rw [hfl]
    have h2 := exp_two_point (c := c) (lo := 0) (hi := T - k * L + y) (x := T - k * L) (y := y)
      (by linarith) (by linarith) (by ring)
    have e1 : T + y - (k : ℝ) * L = T - k * L + y := by ring
    rw [e1]
    rw [mul_zero, exp_zero] at h2
    linarith
  · push_neg at hcase
    have hfl : ⌊(T + y) / L⌋₊ = k + 1 := by
      rw [Nat.floor_eq_iff hTyL]
      push_cast
      constructor
      · rw [le_div_iff₀ hL]; linarith
      · rw [div_lt_iff₀ hL]; linarith
    rw [hfl]
    push_cast
    have h2 := exp_two_point (c := c) (lo := T - k * L + y - L) (hi := L) (x := T - k * L) (y := y)
      (by linarith) (by linarith) (by ring)
    have e1 : T + y - ((k : ℝ) + 1) * L = T - k * L + y - L := by ring
    rw [e1]
    nlinarith

/-- **The packing bound**: for every finite family of masses `y_i ∈ [0, L]`,
`∑ (e^{c y_i} − 1) ≤ packB c L (∑ y_i)`. -/
theorem sum_le_packB {ι : Type*} [DecidableEq ι] (S : Finset ι) (y : ι → ℝ) {c L : ℝ}
    (hL : 0 < L) (hy0 : ∀ i ∈ S, 0 ≤ y i) (hyL : ∀ i ∈ S, y i ≤ L) :
    ∑ i ∈ S, (exp (c * y i) - 1) ≤ packB c L (∑ i ∈ S, y i) := by
  induction S using Finset.induction_on with
  | empty => simp [packB]
  | insert a S haS ih =>
    rw [Finset.sum_insert haS, Finset.sum_insert haS]
    have h1 := ih (fun i hi => hy0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hyL i (Finset.mem_insert_of_mem hi))
    have h2 := packB_step (c := c) hL
      (Finset.sum_nonneg fun i hi => hy0 i (Finset.mem_insert_of_mem hi))
      (hy0 a (Finset.mem_insert_self a S)) (hyL a (Finset.mem_insert_self a S))
    rw [add_comm (y a)]
    linarith

/-- `H = packB 1 L T` with `L = log(1 + λ)`, `T = log(λ(1−p)/p)`. -/
theorem packH_eq {lam : ℝ} (hl : 0 < lam) (p : ℝ) :
    packH lam p = packB 1 (Real.log (1 + lam)) (logMass lam p) := by
  have h1 : exp (Real.log (1 + lam)) = 1 + lam := exp_log (by linarith)
  unfold packH packB packRes packJ
  rw [one_mul, one_mul, h1]
  ring

/-- `φ = −packB (−1) L T`. -/
theorem packPhi_eq {lam : ℝ} (hl : 0 < lam) (p : ℝ) :
    packPhi lam p = -packB (-1) (Real.log (1 + lam)) (logMass lam p) := by
  have h1 : exp (-1 * Real.log (1 + lam)) = 1 / (1 + lam) := by
    rw [neg_one_mul, exp_neg, exp_log (by linarith), one_div]
  have h2 : ∀ x : ℝ, exp (-1 * x) = exp (-x) := fun x => by rw [neg_one_mul]
  unfold packPhi packB packRes packJ
  rw [h1, h2, actQ]
  field_simp
  ring

/-! ### The Cauchy residuals -/

/-- **Titu–Cauchy for a dominated response**: if `0 ≤ b ≤ ∑ a_i` with `a_i ≥ 0` and masses
`y_i > 0`, then `b²/∑ y_i ≤ ∑ a_i²/y_i` (both sides `0` for an empty family when `b = 0`). -/
theorem sq_div_le_of_le_sum {ι : Type*} (S : Finset ι) (a y : ι → ℝ) {b : ℝ}
    (hy : ∀ i ∈ S, 0 < y i) (hb0 : 0 ≤ b) (hb : b ≤ ∑ i ∈ S, a i) :
    b ^ 2 / ∑ i ∈ S, y i ≤ ∑ i ∈ S, a i ^ 2 / y i := by
  have hT := Finset.sq_sum_div_le_sum_sq_div S a hy
  have hY : 0 ≤ ∑ i ∈ S, y i := Finset.sum_nonneg fun i hi => (hy i hi).le
  have hsq : b ^ 2 ≤ (∑ i ∈ S, a i) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  calc b ^ 2 / ∑ i ∈ S, y i ≤ (∑ i ∈ S, a i) ^ 2 / ∑ i ∈ S, y i :=
        div_le_div_of_nonneg_right hsq hY
    _ ≤ ∑ i ∈ S, a i ^ 2 / y i := hT

/-- **Titu–Cauchy with the packed odds**: if `0 < p_i < 1` and `∑ p_i/(1 − p_i) ≤ H`, then
`(∑ p_i z_i)²/H ≤ ∑ p_i(1 − p_i) z_i²`. -/
theorem sq_div_le_of_le_odds {ι : Type*} (S : Finset ι) (p z : ι → ℝ) {H : ℝ}
    (hp0 : ∀ i ∈ S, 0 < p i) (hp1 : ∀ i ∈ S, p i < 1) (hH : ∑ i ∈ S, p i / (1 - p i) ≤ H) :
    (∑ i ∈ S, p i * z i) ^ 2 / H ≤ ∑ i ∈ S, p i * (1 - p i) * z i ^ 2 := by
  have hg : ∀ i ∈ S, 0 < p i / (1 - p i) := fun i hi =>
    div_pos (hp0 i hi) (by linarith [hp1 i hi])
  have hT := Finset.sq_sum_div_le_sum_sq_div S (fun i => p i * z i) hg
  have hterm : ∀ i ∈ S, (p i * z i) ^ 2 / (p i / (1 - p i)) = p i * (1 - p i) * z i ^ 2 := by
    intro i hi
    have h1 : (1 - p i) ≠ 0 := by linarith [hp1 i hi]
    have h2 : p i ≠ 0 := (hp0 i hi).ne'
    field_simp
  rw [Finset.sum_congr rfl hterm] at hT
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    simp
  · have hQ : 0 < ∑ i ∈ S, p i / (1 - p i) := Finset.sum_pos hg hS
    calc (∑ i ∈ S, p i * z i) ^ 2 / H ≤ (∑ i ∈ S, p i * z i) ^ 2 / ∑ i ∈ S, p i / (1 - p i) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hQ hH
      _ ≤ ∑ i ∈ S, p i * (1 - p i) * z i ^ 2 := hT

end Erdos993Lean.Analytic.O2
