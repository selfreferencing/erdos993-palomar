module

public import Mathlib
public import Erdos993Lean.Analytic.Defs

/-!
# The tail input T3, part 5: scalar functions and inequalities

Sources: T23 §3
and the audit of the tail input O3
("Surviving analytic fallback").

* `Lf p = L(p) = −log(1 − p)`, `Lz z p = L_z(p) = −log(1 − (1 − z) p)`,
  `Tf t p = T(p) = log(t(1 − p)/p)`, `That t Y = log t − Y − log(1 − e^{−Y})`, `ThatPlus = max(That, 0)`;
* `rFallback t z = r(t, z) = log((1 + t)/(1 + t z)) / log(1 + t)` (the fallback ratio).

Main results (the scalar steps of the fallback proof):
* `le_Lf`: `p ≤ L(p)`;
* `rFallback_mul_Lf_le_Lz`: for `0 ≤ p ≤ q = t/(1+t)`, `r L(p) ≤ L_z(p)` (concavity of `x ↦ x^r`
  on `[1 − q, 1]`; this is "`L_z/L` is decreasing and `p ≤ q`");
* `one_add_mul_exp_le`: for `0 ≤ u ≤ t`, `d ≥ 0`: `(1 + u) e^{−q d} ≤ 1 + u e^{−d}`
  (convexity of `exp`; this is "`f(x) = log(1 + t e^{−x})` has `f' ≥ −q`");
* `unit_bound`: if `P ≤ t e^{−Y}/(1 + t e^{−Y})` and `Y_z ≥ r Y` then
  `P + (1 − P) e^{−Y_z} ≤ exp(−r (1 − q) Y)` (one toy unit);
* `isolated_bound`: `(1 + t z)/(1 + t) ≤ exp(−r (1 − q) q)` (an isolated B-vertex).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Real

/-- `L(p) = −log(1 − p)`. -/
noncomputable def Lf (p : ℝ) : ℝ := -Real.log (1 - p)

/-- `L_z(p) = −log(1 − (1 − z) p)`. -/
noncomputable def Lz (z p : ℝ) : ℝ := -Real.log (1 - (1 - z) * p)

/-- `T(p) = log(t (1 − p)/p)`. -/
noncomputable def Tf (t p : ℝ) : ℝ := Real.log (t * (1 - p) / p)

/-- `That(Y) = log t − Y − log(1 − e^{−Y})` (`= T(p)` for `L(p) = Y`). -/
noncomputable def That (t Y : ℝ) : ℝ := Real.log t - Y - Real.log (1 - Real.exp (-Y))

/-- `That_+(Y) = max(That(Y), 0)`. -/
noncomputable def ThatPlus (t Y : ℝ) : ℝ := max (That t Y) 0

/-- **The fallback ratio** `r(t, z) = log((1 + t)/(1 + t z)) / log(1 + t)`. -/
noncomputable def rFallback (t z : ℝ) : ℝ := Real.log ((1 + t) / (1 + t * z)) / Real.log (1 + t)

section Basic

variable {t z p : ℝ}

theorem actQ_pos (ht : 0 < t) : 0 < actQ t := div_pos ht (by linarith)

theorem actQ_lt_one (ht : 0 ≤ t) : actQ t < 1 := by
  unfold actQ
  rw [div_lt_one (by linarith)]
  linarith

theorem one_sub_actQ (ht : 0 ≤ t) : 1 - actQ t = 1 / (1 + t) := by
  unfold actQ
  field_simp
  ring

theorem Lf_nonneg (hp0 : 0 ≤ p) (hp1 : p < 1) : 0 ≤ Lf p := by
  unfold Lf
  have : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

/-- `p ≤ L(p)`. -/
theorem le_Lf (hp1 : p < 1) : p ≤ Lf p := by
  unfold Lf
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - p by linarith)
  linarith

theorem exp_neg_Lf (hp1 : p < 1) : Real.exp (-Lf p) = 1 - p := by
  unfold Lf
  rw [neg_neg, Real.exp_log (by linarith)]

theorem exp_neg_Lz (h : 0 < 1 - (1 - z) * p) : Real.exp (-Lz z p) = 1 - (1 - z) * p := by
  unfold Lz
  rw [neg_neg, Real.exp_log h]

/-- `log(1 + t) ≥ q`. -/
theorem actQ_le_log (ht : 0 ≤ t) : actQ t ≤ Real.log (1 + t) := by
  have h1 : 0 < 1 + t := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h
  have h2 : (1 + t)⁻¹ - 1 = -actQ t := by
    unfold actQ
    field_simp
    ring
  linarith

theorem log_one_add_pos (ht : 0 < t) : 0 < Real.log (1 + t) := Real.log_pos (by linarith)

theorem rFallback_nonneg (ht : 0 < t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ rFallback t z := by
  unfold rFallback
  apply div_nonneg _ (log_one_add_pos ht).le
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem rFallback_le_one (ht : 0 < t) (hz0 : 0 ≤ z) : rFallback t z ≤ 1 := by
  unfold rFallback
  rw [div_le_one (log_one_add_pos ht)]
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg ht.le hz0]

/-- `r log(1 + t) = log((1 + t)/(1 + t z))`. -/
theorem rFallback_mul_log (ht : 0 < t) :
    rFallback t z * Real.log (1 + t) = Real.log ((1 + t) / (1 + t * z)) := by
  unfold rFallback
  field_simp [(log_one_add_pos ht).ne']

end Basic

/-! ### The concavity step: `r L(p) ≤ L_z(p)` for `p ≤ q` -/

/-- **`L_z(p) ≥ r(t, z) L(p)` for `0 ≤ p ≤ q`** (`L_z/L` is decreasing in `p`, and `p ≤ q`).
Proof: with `x = 1 − p ∈ [1 − q, 1]`, `z + (1 − z) x ≤ x^r` by concavity of `x ↦ x^r`, with
equality at both ends. -/
theorem rFallback_mul_Lf_le_Lz {t z p : ℝ} (ht : 0 < t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hp0 : 0 ≤ p) (hpq : p ≤ actQ t) : rFallback t z * Lf p ≤ Lz z p := by
  set q := actQ t with hq
  set r := rFallback t z with hr
  have hq0 : 0 < q := actQ_pos ht
  have hq1 : q < 1 := actQ_lt_one ht.le
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq1
  have hr0 : 0 ≤ r := rFallback_nonneg ht hz0 hz1
  have hr1 : r ≤ 1 := rFallback_le_one ht hz0
  have h1t : 0 < 1 + t := by linarith
  have h1tz : 0 < 1 + t * z := by positivity
  -- the left end `x0 = 1 − q = 1/(1 + t)`: `x0^r = (1 + t z)/(1 + t)`
  set x0 := 1 - q with hx0
  have hx0pos : 0 < x0 := by linarith
  have hx0eq : x0 = 1 / (1 + t) := one_sub_actQ ht.le
  have hx0r : x0 ^ r = (1 + t * z) / (1 + t) := by
    rw [Real.rpow_def_of_pos hx0pos, hx0eq, one_div, Real.log_inv]
    have hlog := rFallback_mul_log (z := z) ht
    rw [← hr] at hlog
    rw [show -Real.log (1 + t) * r = -(r * Real.log (1 + t)) by ring, hlog,
      Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  -- concavity with weights `θ = p/q` and `1 − θ`
  set θ := p / q with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hp0 hq0.le
  have hθ1 : θ ≤ 1 := (div_le_one hq0).mpr hpq
  have hconc := (Real.concaveOn_rpow hr0 hr1).2 (Set.mem_Ici.mpr hx0pos.le)
    (Set.mem_Ici.mpr zero_le_one) hθ0 (by linarith : 0 ≤ 1 - θ) (by ring : θ + (1 - θ) = 1)
  simp only [smul_eq_mul, Real.one_rpow, mul_one] at hconc
  have hx : θ * x0 + (1 - θ) = 1 - p := by
    rw [hθ, hx0]
    field_simp
    ring
  rw [hx, hx0r] at hconc
  -- `θ (1 + t z)/(1 + t) + (1 − θ) = 1 − (1 − z) p`
  have hval : θ * ((1 + t * z) / (1 + t)) + (1 - θ) = 1 - (1 - z) * p := by
    rw [hθ, hq]
    unfold actQ
    field_simp
    ring
  rw [hval] at hconc
  -- take logarithms
  have hpos : 0 < 1 - (1 - z) * p := by nlinarith
  have hlog := Real.log_le_log hpos hconc
  rw [Real.log_rpow (by linarith)] at hlog
  unfold Lz Lf
  linarith

/-! ### The convexity step and one toy unit -/

/-- **`(1 + u) e^{−q d} ≤ 1 + u e^{−d}` for `0 ≤ u ≤ t`, `d ≥ 0`** (convexity of `exp`:
"`f(x) = log(1 + t e^{−x})` has `f' ≥ −q`"). -/
theorem one_add_mul_exp_le {t u d : ℝ} (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hut : u ≤ t) (hd : 0 ≤ d) :
    (1 + u) * Real.exp (-(actQ t * d)) ≤ 1 + u * Real.exp (-d) := by
  have h1u : 0 < 1 + u := by linarith
  set θ := 1 / (1 + u) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : 0 ≤ 1 - θ := by
    rw [hθ, sub_nonneg, div_le_one h1u]
    linarith
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-d)) hθ0 hθ1
    (by ring : θ + (1 - θ) = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  -- `1 − θ = u/(1 + u) ≤ q`
  have hθq : 1 - θ ≤ actQ t := by
    have e : 1 - θ = u / (1 + u) := by
      rw [hθ, eq_div_iff h1u.ne', sub_mul, one_mul, one_div, inv_mul_cancel₀ h1u.ne']
      ring
    rw [e]
    unfold actQ
    rw [div_le_div_iff₀ h1u (by linarith)]
    nlinarith
  have hmono : Real.exp (-(actQ t * d)) ≤ Real.exp ((1 - θ) * -d) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hkey : (1 + u) * Real.exp ((1 - θ) * -d) ≤ 1 + u * Real.exp (-d) := by
    have h := mul_le_mul_of_nonneg_left hconv h1u.le
    have e1 : (1 + u) * θ = 1 := by
      rw [hθ]
      field_simp
    have e2 : (1 + u) * (1 - θ) = u := by
      rw [hθ]
      field_simp
      ring
    calc (1 + u) * Real.exp ((1 - θ) * -d) ≤ (1 + u) * (θ + (1 - θ) * Real.exp (-d)) := h
      _ = (1 + u) * θ + (1 + u) * (1 - θ) * Real.exp (-d) := by ring
      _ = 1 + u * Real.exp (-d) := by rw [e1, e2]
  exact (mul_le_mul_of_nonneg_left hmono h1u.le).trans hkey

/-- **One toy unit** (the per-unit step): if `P ≤ t e^{−Y}/(1 + t e^{−Y})`, `Y ≥ 0`,
`0 ≤ r ≤ 1` and `Y_z ≥ r Y`, then `P + (1 − P) e^{−Y_z} ≤ exp(−r (1 − q) Y)`. -/
theorem unit_bound {t r Y P Yz : ℝ} (ht : 0 < t) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hY : 0 ≤ Y)
    (hP : P ≤ t * Real.exp (-Y) / (1 + t * Real.exp (-Y))) (hYz : r * Y ≤ Yz) :
    P + (1 - P) * Real.exp (-Yz) ≤ Real.exp (-(r * (1 - actQ t)) * Y) := by
  obtain ⟨a, ha⟩ : ∃ a, a = Real.exp (-((1 - r) * Y)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Real.exp (-(r * Y)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Real.exp (actQ t * (r * Y)) := ⟨_, rfl⟩
  have ha0 : 0 < a := ha ▸ Real.exp_pos _
  have hb0 : 0 < b := hb ▸ Real.exp_pos _
  have hc0 : 0 < c := hc ▸ Real.exp_pos _
  have ha1 : a ≤ 1 := by
    rw [ha]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hb1 : b ≤ 1 := by
    rw [hb]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hab : Real.exp (-Y) = a * b := by
    rw [ha, hb, ← Real.exp_add]
    congr 1
    ring
  have hgoal : Real.exp (-(r * (1 - actQ t)) * Y) = b * c := by
    rw [hb, hc, ← Real.exp_add]
    congr 1
    ring
  have h1 : Real.exp (-Yz) ≤ b := by
    rw [hb]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [hab] at hP
  rw [hgoal]
  have hE : 0 < 1 + t * (a * b) := by positivity
  have hP1 : P ≤ 1 := hP.trans ((div_le_one hE).mpr (by linarith))
  -- the convexity step with `u = t a`, `d = r Y`
  have h4 := one_add_mul_exp_le ht.le (mul_nonneg ht.le ha0.le) (by nlinarith : t * a ≤ t)
    (mul_nonneg hr0 hY)
  rw [Real.exp_neg, ← hc, ← hb] at h4
  have h5 : 1 + t * a ≤ (1 + t * (a * b)) * c := by
    have := mul_le_mul_of_nonneg_right h4 hc0.le
    rw [mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one] at this
    nlinarith
  have h1P : 0 ≤ 1 - P := by linarith
  have h1' : (1 - P) * Real.exp (-Yz) ≤ (1 - P) * b := mul_le_mul_of_nonneg_left h1 h1P
  calc P + (1 - P) * Real.exp (-Yz) ≤ P + (1 - P) * b := by linarith
    _ = b + P * (1 - b) := by ring
    _ ≤ b + t * (a * b) / (1 + t * (a * b)) * (1 - b) := by
        nlinarith [mul_le_mul_of_nonneg_right hP (by linarith : (0 : ℝ) ≤ 1 - b)]
    _ = b * (1 + t * a) / (1 + t * (a * b)) := by
        field_simp
        ring
    _ ≤ b * c := by
        rw [div_le_iff₀ hE]
        nlinarith [mul_le_mul_of_nonneg_left h5 hb0.le]

/-- **An isolated B-vertex**: `(1 + t z)/(1 + t) ≤ exp(−r (1 − q) q)`. -/
theorem isolated_bound {t z : ℝ} (ht : 0 < t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (1 + t * z) / (1 + t) ≤ Real.exp (-(rFallback t z * (1 - actQ t)) * actQ t) := by
  have h1t : 0 < 1 + t := by linarith
  have h1tz : 0 < 1 + t * z := by positivity
  have hq0 := actQ_pos ht
  have hq1 := actQ_lt_one ht.le
  have hr0 := rFallback_nonneg ht hz0 hz1
  have hlog := actQ_le_log ht.le
  -- `(1 + t z)/(1 + t) = exp(−r log(1 + t))`
  have heq : (1 + t * z) / (1 + t) = Real.exp (-(rFallback t z * Real.log (1 + t))) := by
    rw [rFallback_mul_log ht, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  rw [heq]
  apply Real.exp_le_exp.mpr
  -- `r (1 − q) q ≤ r q ≤ r log(1 + t)`
  have h1 : rFallback t z * (1 - actQ t) * actQ t ≤ rFallback t z * actQ t := by
    have : (1 - actQ t) * actQ t ≤ actQ t := by nlinarith
    nlinarith
  have h2 : rFallback t z * actQ t ≤ rFallback t z * Real.log (1 + t) :=
    mul_le_mul_of_nonneg_left hlog hr0
  linarith

end Erdos993Lean.Analytic.Tail
