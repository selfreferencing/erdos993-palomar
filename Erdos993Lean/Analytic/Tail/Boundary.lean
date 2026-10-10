module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.LemmaC

/-!
# The tail input T3, part 9: the C-only boundary lemma (`Y_B = 0`)

Source:
the repaired potential proof of the tail input, section "Exact C-only boundary lemma" (the boundary
`Y_B = 0, Y_C > 0` omitted by the float certificates of T23 §3b).

With the activity-dependent potential `Ψ_λ = a L + k(λ) T`, `k(λ) = a r(λ)`,
`r(λ) = 1 − 2/(1 + √(1 + 4λ))` (the root in `(0, 1)` of `r = λ(1 − r)²`), the unit inequality at a
C-vertex with no B-child and C-child mass `Y > 0` is

  `(a − k) Y + k That_+(Y) − a log(1 + λ e^{−Y}) ≥ 0`   (`boundary_lemma`).

Proof: with `α = (1 + √(1 + 4λ))/2` (so `λ = α(α − 1)`, `r = 1 − 1/α`) and `x = e^Y`, for
`1 < x ≤ 1 + λ` the bracket divided by `a` is
`f(x) = (2 − r) log x − r log(x − 1) + r log λ − log(x + λ)` (`bdryF`), whose derivative is
`(x − α)((2 − α) x + α² − 1) / (α x (x − 1)(x + λ))` (`bdryF_deriv_mul`); the second factor is
`≥ 0` on `[1, 1 + λ]` when `α ≤ 3` (i.e. `λ ≤ 6`; it equals `α² − α + 1` at `x = 1` and
`1 + α(α − 1)(3 − α)` at `x = 1 + λ`), so `f` decreases to `x = α`, where `f(α) = 0`, and increases
after (`bdry_core`).  For `x ≥ 1 + λ`, `That_+ = 0` and the bracket increases in `Y`.

The hypothesis `λ ≤ 6` covers the activity window `[1/3, 7/3]`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Real Set

/-- `r(λ) = 1 − 2/(1 + √(1 + 4λ))`, the root in `(0, 1)` of `r = λ(1 − r)²`. -/
noncomputable def rK (lam : ℝ) : ℝ := 1 - 2 / (1 + Real.sqrt (1 + 4 * lam))

/-- `p_c = λ e^{−s}/(1 + λ e^{−s})`, the downward probability of a C-vertex with child mass `s`. -/
noncomputable def pC (lam s : ℝ) : ℝ := lam * Real.exp (-s) / (1 + lam * Real.exp (-s))

/-- The boundary function `f(x) = (2 − r) log x − r log(x − 1) + r log λ − log(x + λ)`. -/
noncomputable def bdryF (r lam x : ℝ) : ℝ :=
  (2 - r) * Real.log x - r * Real.log (x - 1) + r * Real.log lam - Real.log (x + lam)

/-! ### Facts about `r(λ)`, `α` and `p_c` -/

section Alpha

variable {lam : ℝ}

/-- `α = (1 + √(1 + 4λ))/2` satisfies `α > 1`, `α² − α = λ`, `r(λ) = 1 − 1/α`, and `α ≤ 3` if
`λ ≤ 6`. -/
theorem alpha_facts (hlam0 : 0 < lam) :
    1 < (1 + Real.sqrt (1 + 4 * lam)) / 2 ∧
      ((1 + Real.sqrt (1 + 4 * lam)) / 2) ^ 2 - (1 + Real.sqrt (1 + 4 * lam)) / 2 = lam ∧
      rK lam = 1 - 1 / ((1 + Real.sqrt (1 + 4 * lam)) / 2) ∧
      (lam ≤ 6 → (1 + Real.sqrt (1 + 4 * lam)) / 2 ≤ 3) := by
  set sq := Real.sqrt (1 + 4 * lam) with hsq
  have h0 : 0 ≤ sq := Real.sqrt_nonneg _
  have h2 : sq ^ 2 = 1 + 4 * lam := Real.sq_sqrt (by linarith)
  have h1 : 1 < sq := by nlinarith
  refine ⟨by linarith, ?_, ?_, fun h6 => by nlinarith [h2, h0]⟩
  · have e : ((1 + sq) / 2) ^ 2 - (1 + sq) / 2 = (sq ^ 2 - 1) / 4 := by ring
    rw [e, h2]
    ring
  · unfold rK
    rw [← hsq, one_div_div]

theorem rK_nonneg (hlam0 : 0 < lam) : 0 ≤ rK lam := by
  obtain ⟨hα, -, hr, -⟩ := alpha_facts hlam0
  rw [hr, sub_nonneg, div_le_one (by linarith)]
  linarith

theorem rK_le_one (hlam0 : 0 < lam) : rK lam ≤ 1 := by
  obtain ⟨hα, -, hr, -⟩ := alpha_facts hlam0
  rw [hr]
  have : 0 < 1 / ((1 + Real.sqrt (1 + 4 * lam)) / 2) := by positivity
  linarith

theorem pC_pos (hlam0 : 0 < lam) (s : ℝ) : 0 < pC lam s := by
  unfold pC
  positivity

theorem pC_lt_one (hlam0 : 0 < lam) (s : ℝ) : pC lam s < 1 := by
  unfold pC
  rw [div_lt_one (by positivity)]
  linarith

/-- `1 − p_c = 1/(1 + λ e^{−s})`. -/
theorem one_sub_pC (hlam0 : 0 < lam) (s : ℝ) : 1 - pC lam s = (1 + lam * Real.exp (-s))⁻¹ := by
  have hD : 0 < 1 + lam * Real.exp (-s) := by positivity
  unfold pC
  rw [one_sub_div hD.ne', show 1 + lam * Real.exp (-s) - lam * Real.exp (-s) = 1 by ring, one_div]

/-- The odds of `p_c` are `λ e^{−s}`. -/
theorem pC_odds (hlam0 : 0 < lam) (s : ℝ) : pC lam s / (1 - pC lam s) = lam * Real.exp (-s) := by
  have hD : 0 < 1 + lam * Real.exp (-s) := by positivity
  rw [one_sub_pC hlam0, div_inv_eq_mul]
  unfold pC
  rw [div_mul_cancel₀ _ hD.ne']

/-- `L(p_c) = log(1 + λ e^{−s})`. -/
theorem Lf_pC (hlam0 : 0 < lam) (s : ℝ) : Lf (pC lam s) = Real.log (1 + lam * Real.exp (-s)) := by
  unfold Lf
  rw [one_sub_pC hlam0, Real.log_inv, neg_neg]

/-- `T(p_c) = s`. -/
theorem Tf_pC (hlam0 : 0 < lam) (s : ℝ) : Tf lam (pC lam s) = s := by
  unfold Tf
  rw [← div_div_eq_mul_div, pC_odds hlam0, div_mul_cancel_left₀ hlam0.ne', Real.exp_neg, inv_inv,
    Real.log_exp]

/-- A `p ∈ (0, 1)` with `T(p) = s` is `p_c(s)`. -/
theorem eq_pC_of_Tf (hlam0 : 0 < lam) {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h : Tf lam p = s) :
    p = pC lam s := by
  have hu : 0 < 1 - p := by linarith
  have hpos : 0 < lam * (1 - p) / p := div_pos (mul_pos hlam0 hu) hp0
  have hexp : Real.exp s = lam * (1 - p) / p := by
    rw [← h, Tf, Real.exp_log hpos]
  have hE : lam * Real.exp (-s) = p / (1 - p) := by
    rw [Real.exp_neg, hexp, inv_div, ← mul_div_assoc, mul_div_mul_left _ _ hlam0.ne']
  unfold pC
  rw [hE, one_add_div hu.ne', show 1 - p + p = 1 by ring, div_div_div_cancel_right₀ hu.ne', div_one]

theorem pC_le_actQ (hlam0 : 0 < lam) {s : ℝ} (hs : 0 ≤ s) : pC lam s ≤ actQ lam := by
  unfold pC actQ
  have hE : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE0 : 0 < Real.exp (-s) := Real.exp_pos _
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

end Alpha

/-! ### The one-variable function `f` -/

section Core

theorem bdryF_hasDerivAt {r lam x : ℝ} (hlam : 0 < lam) (hx : 1 < x) :
    HasDerivAt (bdryF r lam) ((2 - r) / x - r / (x - 1) - 1 / (x + lam)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x - 1 ≠ 0 := by linarith
  have hxl : x + lam ≠ 0 := by linarith
  have d1 : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx0
  have d2 : HasDerivAt (fun y : ℝ => Real.log (y - 1)) (1 / (x - 1)) x :=
    ((hasDerivAt_id x).sub_const 1).log hx1
  have d3 : HasDerivAt (fun y : ℝ => Real.log (y + lam)) (1 / (x + lam)) x :=
    ((hasDerivAt_id x).add_const lam).log hxl
  have d := (((d1.const_mul (2 - r)).sub (d2.const_mul r)).add_const (r * Real.log lam)).sub d3
  convert d using 1
  · ext y
    rfl
  · simp only [div_eq_mul_inv, one_mul]

/-- The derivative identity `f'(y) · α y (y − 1)(y + λ) = (y − α)((2 − α) y + α² − 1)` for
`r = 1 − 1/α`, `λ = α² − α`. -/
theorem bdryF_deriv_mul {α y : ℝ} (hα : 1 < α) (hy : 1 < y) :
    ((2 - (1 - 1 / α)) / y - (1 - 1 / α) / (y - 1) - 1 / (y + (α ^ 2 - α))) *
        (α * y * (y - 1) * (y + (α ^ 2 - α))) =
      (y - α) * ((2 - α) * y + α ^ 2 - 1) := by
  have hα0 : α ≠ 0 := by linarith
  have hy0 : y ≠ 0 := by linarith
  have hy1 : y - 1 ≠ 0 := by linarith
  have hyl : y + (α ^ 2 - α) ≠ 0 := (by nlinarith : (0 : ℝ) < y + (α ^ 2 - α)).ne'
  have hyl' : y - α + α ^ 2 ≠ 0 := (by nlinarith : (0 : ℝ) < y - α + α ^ 2).ne'
  rw [show y + (α ^ 2 - α) = y - α + α ^ 2 by ring]
  field_simp
  ring

/-- The second factor `(2 − α) y + α² − 1` is nonnegative on `[1, 1 + λ]` for `1 < α ≤ 3`. -/
theorem second_factor_nonneg {α y : ℝ} (hα1 : 1 < α) (hα3 : α ≤ 3) (hy1 : 1 ≤ y)
    (hy2 : y ≤ 1 + (α ^ 2 - α)) : 0 ≤ (2 - α) * y + α ^ 2 - 1 := by
  by_cases h : α ≤ 2
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - α) (by linarith : (0 : ℝ) ≤ y)]
  · push_neg at h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ α - 2) (by linarith : (0 : ℝ) ≤ 1 + (α ^ 2 - α) - y),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ α) (by linarith : (0 : ℝ) ≤ α - 1))
        (by linarith : (0 : ℝ) ≤ 3 - α)]

theorem bdryF_alpha {α : ℝ} (hα : 1 < α) : bdryF (1 - 1 / α) (α ^ 2 - α) α = 0 := by
  unfold bdryF
  have h1 : α ^ 2 - α = α * (α - 1) := by ring
  have h2 : α + (α ^ 2 - α) = α ^ 2 := by ring
  rw [h1, Real.log_mul (by linarith : (0 : ℝ) < α).ne' (by linarith : (0 : ℝ) < α - 1).ne', ← h1, h2,
    Real.log_pow]
  push_cast
  ring

/-- **The core of the boundary lemma**: `f(x) ≥ 0` for `1 < x ≤ 1 + λ`, `1 < α ≤ 3`. -/
theorem bdry_core {α x : ℝ} (hα1 : 1 < α) (hα3 : α ≤ 3) (hx1 : 1 < x)
    (hx2 : x ≤ 1 + (α ^ 2 - α)) : 0 ≤ bdryF (1 - 1 / α) (α ^ 2 - α) x := by
  have hlam : 0 < α ^ 2 - α := by nlinarith
  have hder : ∀ y, 1 < y → HasDerivAt (bdryF (1 - 1 / α) (α ^ 2 - α))
      ((2 - (1 - 1 / α)) / y - (1 - 1 / α) / (y - 1) - 1 / (y + (α ^ 2 - α))) y :=
    fun y hy => bdryF_hasDerivAt hlam hy
  have hcont : ContinuousOn (bdryF (1 - 1 / α) (α ^ 2 - α)) (Ioi 1) :=
    fun y hy => (hder y hy).continuousAt.continuousWithinAt
  -- the sign of the derivative
  have hsign : ∀ y, 1 < y → y ≤ 1 + (α ^ 2 - α) →
      ((2 - (1 - 1 / α)) / y - (1 - 1 / α) / (y - 1) - 1 / (y + (α ^ 2 - α))) *
        (α * y * (y - 1) * (y + (α ^ 2 - α))) = (y - α) * ((2 - α) * y + α ^ 2 - 1) ∧
      0 < α * y * (y - 1) * (y + (α ^ 2 - α)) ∧ 0 ≤ (2 - α) * y + α ^ 2 - 1 := by
    intro y hy1 hy2
    refine ⟨bdryF_deriv_mul hα1 hy1, ?_, second_factor_nonneg hα1 hα3 hy1.le hy2⟩
    have : 0 < y - 1 := by linarith
    have : 0 < y + (α ^ 2 - α) := by linarith
    positivity
  have hαle : α ≤ 1 + (α ^ 2 - α) := by nlinarith
  rw [← bdryF_alpha hα1]
  rcases le_total x α with hxα | hαx
  · -- decreasing on `(1, α]`
    have hanti : AntitoneOn (bdryF (1 - 1 / α) (α ^ 2 - α)) (Ioc 1 α) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc 1 α) (hcont.mono Ioc_subset_Ioi_self)
      · intro y hy
        rw [interior_Ioc] at hy
        exact (hder y hy.1).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        rw [(hder y hy.1).deriv]
        obtain ⟨hid, hD, hE⟩ := hsign y hy.1 (by linarith [hy.2])
        by_contra hpos
        push_neg at hpos
        have := mul_pos hpos hD
        rw [hid] at this
        nlinarith [mul_nonneg (by linarith [hy.2] : (0 : ℝ) ≤ α - y) hE]
    exact hanti ⟨hx1, hxα⟩ ⟨hα1, le_rfl⟩ hxα
  · -- increasing on `[α, 1 + λ]`
    have hmono : MonotoneOn (bdryF (1 - 1 / α) (α ^ 2 - α)) (Icc α (1 + (α ^ 2 - α))) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (hcont.mono (fun y hy => lt_of_lt_of_le hα1 hy.1))
      · intro y hy
        rw [interior_Icc] at hy
        exact (hder y (lt_trans hα1 hy.1)).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hder y (lt_trans hα1 hy.1)).deriv]
        obtain ⟨hid, hD, hE⟩ := hsign y (lt_trans hα1 hy.1) hy.2.le
        by_contra hneg
        push_neg at hneg
        have := mul_neg_of_neg_of_pos hneg hD
        rw [hid] at this
        nlinarith [mul_nonneg (by linarith [hy.1] : (0 : ℝ) ≤ y - α) hE]
    exact hmono ⟨le_rfl, hαle⟩ ⟨hαx, hx2⟩ hαx

end Core

/-! ### The boundary lemma -/

/-- **The C-only boundary lemma**: for `0 < λ ≤ 6`, `a ≥ 0`,
`k = a r(λ)` and `Y > 0`: `(a − k) Y + k That_+(Y) − a L(p_c(Y)) ≥ 0`, where
`L(p_c(Y)) = log(1 + λ e^{−Y})` (`Lf_pC`). -/
theorem boundary_lemma {lam a Y : ℝ} (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (ha : 0 ≤ a)
    (hY : 0 < Y) :
    0 ≤ (a - a * rK lam) * Y + a * rK lam * ThatPlus lam Y - a * Lf (pC lam Y) := by
  obtain ⟨hα1, hαlam, hr, hα3'⟩ := alpha_facts hlam0
  have hα3 := hα3' hlam6
  set α := (1 + Real.sqrt (1 + 4 * lam)) / 2 with hα
  -- reduce to `a = 1`
  suffices h : 0 ≤ (1 - rK lam) * Y + rK lam * ThatPlus lam Y - Lf (pC lam Y) by
    have e : (a - a * rK lam) * Y + a * rK lam * ThatPlus lam Y - a * Lf (pC lam Y) =
        a * ((1 - rK lam) * Y + rK lam * ThatPlus lam Y - Lf (pC lam Y)) := by ring
    rw [e]
    exact mul_nonneg ha h
  set x := Real.exp Y with hx
  have hx1 : 1 < x := Real.one_lt_exp_iff.mpr hY
  have hxpos : 0 < x := by linarith
  have hLf : Lf (pC lam Y) = Real.log (x + lam) - Real.log x := by
    rw [Lf_pC hlam0, Real.exp_neg, ← hx,
      ← Real.log_div (by linarith : (0 : ℝ) < x + lam).ne' hxpos.ne', add_div, div_self hxpos.ne',
      div_eq_mul_inv]
  have hYlog : Y = Real.log x := by rw [hx, Real.log_exp]
  have hr0 : 0 ≤ rK lam := rK_nonneg hlam0
  have h1r : 0 < 1 - rK lam := by
    rw [hr]
    have : 0 < 1 / α := by positivity
    linarith
  rcases le_or_gt x (1 + lam) with hxl | hxl
  · -- `That_+ = That = log λ − log(x − 1)`
    have hThat : That lam Y = Real.log lam - Real.log (x - 1) := by
      rw [That_eq hlam0 hY, ← hx, Real.log_div hlam0.ne' (sub_pos.mpr hx1).ne']
    have hThat0 : 0 ≤ That lam Y := by
      rw [hThat, sub_nonneg]
      exact Real.log_le_log (by linarith) (by linarith)
    have hTP : ThatPlus lam Y = That lam Y := max_eq_left hThat0
    have hcore := bdry_core hα1 hα3 hx1 (by rw [hαlam]; exact hxl)
    rw [hαlam, ← hr] at hcore
    rw [hTP, hThat, hLf, hYlog]
    unfold bdryF at hcore
    linarith
  · -- `That_+ = 0` and the bracket increases in `Y`
    have hThat : That lam Y ≤ 0 := by
      rw [That_eq hlam0 hY, ← hx]
      apply Real.log_nonpos (div_nonneg hlam0.le (by linarith))
      rw [div_le_one (by linarith)]
      linarith
    have hTP : ThatPlus lam Y = 0 := max_eq_right hThat
    rw [hTP, mul_zero, add_zero]
    -- the value at `Y₀ = log(1 + λ)` is `f(1 + λ) ≥ 0`
    have hcore := bdry_core hα1 hα3 (by linarith : (1 : ℝ) < 1 + lam) (by linarith [hαlam])
    rw [hαlam, ← hr] at hcore
    unfold bdryF at hcore
    have h2l : 1 + lam + lam = 1 + 2 * lam := by ring
    rw [show 1 + lam - 1 = lam by ring, h2l] at hcore
    have hY0 : Real.log (1 + lam) ≤ Y := by
      rw [hYlog]
      exact Real.log_le_log (by linarith) hxl.le
    have hmonoL : Lf (pC lam Y) ≤ Real.log (1 + 2 * lam) - Real.log (1 + lam) := by
      rw [Lf_pC hlam0, ← Real.log_div (by linarith : (0 : ℝ) < 1 + 2 * lam).ne'
        (by linarith : (0 : ℝ) < 1 + lam).ne']
      apply Real.log_le_log (by positivity)
      have hE' : Real.exp (-Y) * (1 + lam) ≤ 1 := by
        rw [Real.exp_neg, ← hx, inv_mul_le_iff₀ hxpos, mul_one]
        linarith
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hE' hlam0.le]
    nlinarith [mul_le_mul_of_nonneg_left hY0 h1r.le]

end Erdos993Lean.Analytic.Tail
