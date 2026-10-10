module

public import Mathlib
public import Erdos993Lean.Analytic.Reserve.Step

/-!
# The step certificate on a band of `Reserve/Defs.lean`

Sources:
the two-generation reserve proof, the sharp first-four reserve proof,
the lower sharp alternate reserve proof.


The four bands of `Reserve/Defs.lean` use the reserve `α y + γ u²/y` (`β = 0`).  Here the three
numeric obligations of the interface are turned into the per-activity step certificate of
`Reserve/Step.lean`:

* `compOK_of_box_tail`: `CompOK` at every feasible point `(λ, T, Y)` of the band, from the finite
  box `BoxOK` (`T ≤ 6`, `Y ≤ 4`) and the analytic tails `TailOK` (`Y ≥ 4` or `T ≥ 6`);
* **`stepCert_of_band`**: for `λ` in the band, `StepCert` with `α = alpha c λ`, `β = 0`,
  `γ = gamma c λ`, `A = capA c λ`: at `β = 0` the comparison CC is `α E` (nonnegative by
  `EntropyOK`), CB is `compC` (nonnegative by (QC), or by `L ≥ 0` with `Z > 0`), BC is `compB`
  ((QB)), and the selected-leaf base is `LeafOK` (`A q − q(1 − q) = D q²`);
* for a signed reserve (the upper band, not in the interface yet): `compCC_nonneg_of_entropy`, CC
  from the Pinsker part of `EntropyOK` and `β² T ≤ 8 α Z`.

Scalarity: `E` (the entropy coefficient of one parent–child message pair, `EntropyOK`), `Z`, `L`,
`H`, `J` are local coefficients of one parent–child quadratic; `T` and `Y` are the grandchild and
child log-mass sums of the actual rooted tree.  They are consumed by `reserve_step_cert`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve

open Real

variable {c : Band}

/-! ### Band facts -/

theorem BandSide.lo_pos (hc : BandSide c) : (0 : ℝ) < c.lo := by
  have h : (1 / 3 : ℚ) ≤ c.lo := hc.1
  have h' : ((1 / 3 : ℚ) : ℝ) ≤ (c.lo : ℝ) := by exact_mod_cast h
  have : ((1 / 3 : ℚ) : ℝ) = 1 / 3 := by norm_num
  linarith

theorem BandSide.one_le_D (hc : BandSide c) : (1 : ℝ) ≤ c.D := by
  have h : (1 : ℚ) ≤ c.D := hc.2.2.2.1
  exact_mod_cast h

theorem BandSide.alpha_pos (hc : BandSide c) {lam : ℝ} (hlam : 0 < lam) : 0 < alpha c lam := by
  have h : (0 : ℚ) < c.aCoef := hc.2.2.2.2.1
  have h' : (0 : ℝ) < c.aCoef := by exact_mod_cast h
  unfold alpha actQ
  exact mul_pos h' (div_pos hlam (by linarith))

theorem BandSide.gamma_pos (hc : BandSide c) {lam : ℝ} (hlam : 0 < lam) : 0 < gamma c lam := by
  have h : (0 : ℚ) < c.gDen := hc.2.2.2.2.2
  have h' : (0 : ℝ) < c.gDen := by exact_mod_cast h
  unfold gamma
  exact div_pos (mul_pos hlam (by linarith)) h'

/-- `CompOK` at every feasible point of the band, from the finite box and the analytic tails. -/
theorem compOK_of_box_tail (hbox : BoxOK c) (htail : TailOK c) {lam T Y : ℝ}
    (h1 : (c.lo : ℝ) ≤ lam) (h2 : lam ≤ c.hi) (hT : 0 ≤ T) (hY : lmass lam T ≤ Y) :
    CompOK c lam T Y := by
  by_cases h : T ≤ 6 ∧ Y ≤ 4
  · exact hbox lam T Y h1 h2 hT h.1 hY h.2
  · apply htail lam T Y h1 h2 hT hY
    by_cases hT6 : T ≤ 6
    · left
      by_contra hY4
      exact h ⟨hT6, by linarith⟩
    · right
      linarith

/-! ### The step certificate on a band -/

/-- **The step certificate on a band** (`β = 0`).  For `λ` in the band `c`, the three numeric
obligations `EntropyOK`, `BoxOK c`, `TailOK c`, `LeafOK c` give the per-activity certificate of the
reserve `alpha c λ · y + gamma c λ · u²/y` with cap `capA c λ`. -/
theorem stepCert_of_band (hc : BandSide c) (hE : EntropyOK) (hbox : BoxOK c) (htail : TailOK c)
    (hleaf : LeafOK c) {lam : ℝ} (hlo : (c.lo : ℝ) ≤ lam) (hhi : lam ≤ c.hi) :
    StepCert (gamma c lam) lam (alpha c lam) 0 (capA c lam) := by
  have hlam : 0 < lam := lt_of_lt_of_le hc.lo_pos hlo
  have hα := hc.alpha_pos hlam
  have hγ := hc.gamma_pos hlam
  refine ⟨hlam, hα.le, hγ, by nlinarith [mul_pos hα hγ], ?_, ?_⟩
  · -- the selected-leaf base is `LeafOK`
    rw [msg_zero, lmass_zero]
    have hL := hleaf lam hlo hhi
    have e : capA c lam * actQ lam - actQ lam * (1 - actQ lam) = (c.D : ℝ) * actQ lam ^ 2 := by
      unfold capA
      ring
    rw [e]
    have e0 : (0 : ℝ) * actQ lam = 0 := zero_mul _
    linarith
  · intro T Y hT hY
    obtain ⟨hZ, hC, hB⟩ := compOK_of_box_tail hbox htail hlo hhi hT hY
    have hEi := (hE lam T Y hlam hT hY).1
    have eZ : cZ (gamma c lam) lam T Y = coefZ c lam T Y := rfl
    have eL : cL (gamma c lam) lam Y = coefL c lam Y := rfl
    have eH : cH (gamma c lam) lam Y = coefH c lam Y := rfl
    refine ⟨hZ, ?_, ?_, ?_⟩
    · -- CC is `α E`
      have e : compCC (gamma c lam) lam (alpha c lam) 0 T Y = alpha c lam * coefE lam T Y := by
        unfold compCC
        ring
      rw [e]
      exact mul_nonneg hα.le hEi
    · -- CB is `compC`
      have e : compCB (gamma c lam) lam (alpha c lam) 0 T Y = compC c lam T Y := by
        unfold compCB compC
        rw [eL, eZ]
        ring
      rw [e]
      rcases hC with hL | hCC
      · unfold compC
        have h1 := mul_nonneg hα.le hEi
        have h2 : 0 ≤ msg lam Y * gamma c lam * coefL c lam Y * (msg lam T / lmass lam T) ^ 2 /
            coefZ c lam T Y :=
          div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (msg_pos hlam Y).le hγ.le) hL)
            (sq_nonneg _)) hZ.le
        linarith
      · exact hCC
    · -- BC is `compB`
      have e : compBC (gamma c lam) lam (alpha c lam) 0 (capA c lam) T Y = compB c lam T Y := by
        unfold compBC compB coefJ
        rw [eH, eZ]
        ring
      rw [e]
      exact hB

/-! ### CC for a signed reserve from the entropy floor -/

/-- **CC from the entropy floor** (for a signed reserve, `β ≠ 0`; the
upper sharp signed-port proof, "For CC it suffices ... to certify `2αZ − β²T/4 ≥ 0`"): if
`2 δ² ≤ E y` and `β² T ≤ 8 α Z`, then `α E − β² δ² T/(4 y Z) ≥ 0`. -/
theorem cc_nonneg_of_floor {α β E T y Z δ : ℝ} (hα : 0 ≤ α) (hy : 0 < y) (hZ : 0 < Z)
    (hEy : 2 * δ ^ 2 ≤ E * y) (h8 : β ^ 2 * T ≤ 8 * α * Z) :
    0 ≤ α * E - β ^ 2 * δ ^ 2 * T / (4 * y * Z) := by
  have h1 : α * (2 * δ ^ 2) ≤ α * (E * y) := mul_le_mul_of_nonneg_left hEy hα
  have h2 : β ^ 2 * δ ^ 2 * T / (4 * y * Z) ≤ 8 * α * Z * δ ^ 2 / (4 * y * Z) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_right h8 (sq_nonneg δ)
    linarith
  have h3 : 8 * α * Z * δ ^ 2 / (4 * y * Z) = 2 * α * δ ^ 2 / y := by
    field_simp
    ring
  have h4 : 2 * α * δ ^ 2 / y ≤ α * E := by
    rw [div_le_iff₀ hy]
    linarith
  linarith

/-- **CC of `StepCert` from `EntropyOK`**: at a feasible point, the Pinsker part of the entropy facts
(`2 (p − s)² ≤ E y`) and `β² T ≤ 8 α Z` give `compCC ≥ 0` (this is how a signed reserve pays the
unselected–unselected pair, including the exact zero `δ = 0, Y = y` of `E`). -/
theorem compCC_nonneg_of_entropy (hE : EntropyOK) {lam T Y α β γ : ℝ} (hlam : 0 < lam)
    (hT : 0 ≤ T) (hY : lmass lam T ≤ Y) (hα : 0 ≤ α) (hZ : 0 < cZ γ lam T Y)
    (h8 : β ^ 2 * T ≤ 8 * α * cZ γ lam T Y) : 0 ≤ compCC γ lam α β T Y := by
  have hy := lmass_pos hlam T
  have hYpos : 0 < Y := lt_of_lt_of_le hy hY
  have hfloor := (hE lam T Y hlam hT hY).2
  have hrest : 0 ≤ (Y - lmass lam T) * (msg lam Y + lmass lam Y / Y) :=
    mul_nonneg (by linarith) (add_nonneg (msg_pos hlam Y).le
      (div_nonneg (lmass_pos hlam Y).le hYpos.le))
  have hEy : 2 * (msg lam T - msg lam Y) ^ 2 ≤ coefE lam T Y * lmass lam T := by
    have e : (msg lam T - msg lam Y) ^ 2 = (msg lam Y - msg lam T) ^ 2 := by ring
    rw [e]
    linarith
  exact cc_nonneg_of_floor hα hy hZ hEy h8

end Erdos993Lean.Analytic.Reserve
