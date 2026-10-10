module

public import Mathlib
public import Erdos993Lean.Analytic.Defs
public import Erdos993Lean.Analytic.NoValley.Core

/-!
# The MGF + two-sided no-valley criterion

Sources: the specification of the criterion, §1
(criterion MGF2; the O3 Laplace bounds consumed as moment rows instead of
through Markov, and the exact two-sided valley kernel), T1 §1 (the weak valley in kernel form) and
`NoValley/Core.lean` (`t1Core`, whose expectation argument is repeated here with the two changes).

The two changes to T1's explicit threshold (`ExplicitThreshold` of `Defs.lean`):
* **the two-sided kernel** `a f_L/q + b f_R/(1 − q)` with `a, b ≥ 0` (`kernel2`), in place of `κ = f_L/q + f_R/(1 − q)`
  (`a = b = 1`, `kappa_eq_kernel2`); a weak valley gives `E f_L ≤ 0` and `E f_R ≤ 0` separately (`Mixture.sum_fL_eq`,
  `Mixture.sum_fR_eq`), so `E[a f_L/q + b f_R/(1 − q)] ≤ 0` (`Mixture.sum_kernel2_nonpos`);
* **the MGF rows** `(s_k, e_k)` with the input `E[s_k^M] ≤ e_k`, priced by `z_k ≥ 0` (`pricedTail`, `pricedMargin`), in
  place of the CDF bounds `P(M ≤ M') ≤ T(M')` and their Abel-summed prices.

## Definitions

* `fL`, `fR`, `kernel2`; `pricedTail z rows M = ∑_k z_k s_k^M`, `pricedMargin z rows = ∑_k z_k e_k` (by position, the
  shorter list decides the length).
* `ExplicitThresholdMGF2 q m θ D rows` (SPEC §1): reals `ν > 0`, `c`, `α`, `β`, `γ ≥ 0`, `a, b ≥ 0`, prices `z_k ≥ 0` with
  (P) `α + β(M − m) − γ(M − m)² − ∑_k z_k s_k^M ≤ a f_L/q + b f_R/(1 − q) + cδ + νδ²` for every `M ∈ ℕ`, `j ∈ ℤ`
  (`δ = j − qM`), and (Mg) `ν θ q(1 − q) m < α − γ D m − ∑_k z_k e_k`.
* `NoValleyAtMGF2 q m θ D rows`: every probability mixture with `E M = m`, `E δ = 0`, `E δ² ≤ θ q(1 − q) m`,
  `Var M ≤ D m` and `E[s_k^M] ≤ e_k` for every row has no weak valley at `k`.
* `mgfRows tilts q m`: the rows `(1 − q + q t_k, e^{−ℓ_k m})` of a list of tilts `(t_k, ℓ_k)` (SPEC §2);
  `TailBoundMGF N tilts`: O3 in MGF form for the forests with `n ≥ N`; `ProfileMGF`, `ThresholdNoValleyMGF2`.

## Results

* **`noValleyAtMGF2_of_explicit`**: for `0 < q < 1`, `ExplicitThresholdMGF2 q m θ D rows → NoValleyAtMGF2 q m θ D rows`
  (one expectation argument: the expectation of (P) has left side `≤ 0 + 0 + ν θ q(1 − q) m` and right side
  `≥ α − γ D m − ∑ z_k e_k`, contradicting (Mg)).
* `kappa_eq_kernel2` (`κ = kernel2 q 1 1`) and `explicitThresholdMGF2_of_explicitThreshold_zero`: today's threshold
  with no tail (`M1 = 0`) is the case `a = b = 1`, no rows.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: `ν, c, α, β, γ, a, b, z_k` are the dual of one box (produced by the box constructor, consumed
only through (P) and (Mg)); `θ` summarizes the second moment of `δ` (O2), `D` the variance of the free count `M` (O1),
each row `(s_k, e_k)` the Laplace transform of `M` at `s_k` (O3, `Tail/Weight.lean` `t3_reduction_mixture`), `m` the
expected free count (O5); their consumer is `noValleyAtMGF2_of_explicit`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic

open Finset

/-! ## The two-sided kernel -/

/-- `f_L(M, j) = (1 − q) b_M(j) − q b_M(j − 1)` (T1 §1). -/
noncomputable def fL (q : ℝ) (M : ℕ) (j : ℤ) : ℝ := (1 - q) * binom M q j - q * binom M q (j - 1)

/-- `f_R(M, j) = q b_M(j) − (1 − q) b_M(j + 1)` (T1 §1). -/
noncomputable def fR (q : ℝ) (M : ℕ) (j : ℤ) : ℝ := q * binom M q j - (1 - q) * binom M q (j + 1)

/-- **The two-sided valley kernel** `a f_L(M, j)/q + b f_R(M, j)/(1 − q)` (SPEC §1; R3X §2.3). -/
noncomputable def kernel2 (q a b : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  a * fL q M j / q + b * fR q M j / (1 - q)

/-- T1's kernel is the two-sided kernel with `a = b = 1`. -/
theorem kappa_eq_kernel2 (q : ℝ) (M : ℕ) (j : ℤ) : kappa q M j = kernel2 q 1 1 M j := by
  unfold kappa kernel2 fL fR
  ring

/-! ## Priced rows -/

/-- `∑_k z_k s_k^M` over the rows `(s_k, e_k)` with the prices `z_k`, by position (the shorter list decides). -/
noncomputable def pricedTail : List ℝ → List (ℝ × ℝ) → ℕ → ℝ
  | z :: zs, r :: rs, M => z * r.1 ^ M + pricedTail zs rs M
  | _, _, _ => 0

/-- `∑_k z_k e_k` over the rows `(s_k, e_k)` with the prices `z_k`, by position. -/
noncomputable def pricedMargin : List ℝ → List (ℝ × ℝ) → ℝ
  | z :: zs, r :: rs => z * r.2 + pricedMargin zs rs
  | _, _ => 0

@[simp] theorem pricedTail_cons_cons (z : ℝ) (zs : List ℝ) (r : ℝ × ℝ) (rs : List (ℝ × ℝ)) (M : ℕ) :
    pricedTail (z :: zs) (r :: rs) M = z * r.1 ^ M + pricedTail zs rs M := rfl

@[simp] theorem pricedTail_nil_left (rows : List (ℝ × ℝ)) (M : ℕ) : pricedTail [] rows M = 0 := by
  cases rows <;> rfl

@[simp] theorem pricedTail_nil_right (z : List ℝ) (M : ℕ) : pricedTail z [] M = 0 := by
  cases z <;> rfl

@[simp] theorem pricedMargin_cons_cons (z : ℝ) (zs : List ℝ) (r : ℝ × ℝ) (rs : List (ℝ × ℝ)) :
    pricedMargin (z :: zs) (r :: rs) = z * r.2 + pricedMargin zs rs := rfl

@[simp] theorem pricedMargin_nil_left (rows : List (ℝ × ℝ)) : pricedMargin [] rows = 0 := by
  cases rows <;> rfl

@[simp] theorem pricedMargin_nil_right (z : List ℝ) : pricedMargin z [] = 0 := by
  cases z <;> rfl

/-! ## The criterion and the no-valley property -/

/-- **Criterion MGF2** (SPEC §1).  There are reals `ν > 0`, `c`, `α`, `β`, `γ ≥ 0`, two-sided kernel weights
`a, b ≥ 0` and tail prices `z_k ≥ 0` such that

(P) for all `M ∈ ℕ` and `j ∈ ℤ` (`δ = j − qM`):
    `α + β(M − m) − γ(M − m)² − ∑_k z_k s_k^M ≤ a f_L(M, j)/q + b f_R(M, j)/(1 − q) + cδ + νδ²`;

(Mg) `ν θ q(1 − q) m < α − γ D m − ∑_k z_k e_k`. -/
def ExplicitThresholdMGF2 (q m θ D : ℝ) (rows : List (ℝ × ℝ)) : Prop :=
  ∃ (ν c α β γ a b : ℝ) (z : List ℝ), 0 < ν ∧ 0 ≤ γ ∧ 0 ≤ a ∧ 0 ≤ b ∧ (∀ x ∈ z, 0 ≤ x) ∧
    (∀ (M : ℕ) (j : ℤ),
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 - pricedTail z rows M ≤
        kernel2 q a b M j + c * ((j : ℝ) - q * M) + ν * ((j : ℝ) - q * M) ^ 2) ∧
    ν * θ * (q * (1 - q)) * m < α - γ * D * m - pricedMargin z rows

/-- **The no-valley property in MGF form.**  Every probability mixture with parameter `q`, `E M = m`, `E δ = 0`
and `E δ² ≤ θ q(1 − q) m` at the rank `k`, `Var M ≤ D m` and `E[s_k^M] ≤ e_k` for every row `(s_k, e_k)` has no weak
valley at `k`. -/
def NoValleyAtMGF2 (q m θ D : ℝ) (rows : List (ℝ × ℝ)) : Prop :=
  ∀ (ι : Type) (X : Mixture ι) (k : ℤ), X.IsProb → X.meanM = m →
    X.expect (fun M Y => delta q k M Y) = 0 →
    X.expect (fun M Y => delta q k M Y ^ 2) ≤ θ * (q * (1 - q)) * m →
    X.varM ≤ D * m →
    (∀ r ∈ rows, X.expect (fun M _ => r.1 ^ M) ≤ r.2) →
    ¬ X.WeakValley q k

namespace Mixture

variable {ι : Type*} (X : Mixture ι)

/-- **The expected left kernel** (T1 §1): with `j = k − Y`, `E f_L(M, j) = (1 − q) P_k − q P_{k−1}`. -/
theorem sum_fL_eq (q : ℝ) (k : ℤ) :
    ∑ σ ∈ X.S, X.w σ * fL q (X.M σ) (k - X.Y σ) = (1 - q) * X.prob q k - q * X.prob q (k - 1) := by
  have hσ : ∀ σ ∈ X.S, X.w σ * fL q (X.M σ) (k - X.Y σ) =
      (1 - q) * (X.w σ * binom (X.M σ) q (k - X.Y σ)) -
        q * (X.w σ * binom (X.M σ) q (k - 1 - X.Y σ)) := by
    intro σ _
    have e1 : k - 1 - (X.Y σ : ℤ) = k - X.Y σ - 1 := by ring
    rw [e1, fL]
    ring
  rw [Finset.sum_congr rfl hσ, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- **The expected right kernel** (T1 §1): with `j = k − Y`, `E f_R(M, j) = q P_k − (1 − q) P_{k+1}`. -/
theorem sum_fR_eq (q : ℝ) (k : ℤ) :
    ∑ σ ∈ X.S, X.w σ * fR q (X.M σ) (k - X.Y σ) = q * X.prob q k - (1 - q) * X.prob q (k + 1) := by
  have hσ : ∀ σ ∈ X.S, X.w σ * fR q (X.M σ) (k - X.Y σ) =
      q * (X.w σ * binom (X.M σ) q (k - X.Y σ)) -
        (1 - q) * (X.w σ * binom (X.M σ) q (k + 1 - X.Y σ)) := by
    intro σ _
    have e2 : k + 1 - (X.Y σ : ℤ) = k - X.Y σ + 1 := by ring
    rw [e2, fR]
    ring
  rw [Finset.sum_congr rfl hσ, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- **Under a weak valley the expected two-sided kernel is nonpositive** for `a, b ≥ 0` (T1 §1). -/
theorem sum_kernel2_nonpos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {k : ℤ}
    (hv : X.WeakValley q k) :
    ∑ σ ∈ X.S, X.w σ * kernel2 q a b (X.M σ) (k - X.Y σ) ≤ 0 := by
  obtain ⟨hL, hR⟩ := hv
  have hσ : ∀ σ ∈ X.S, X.w σ * kernel2 q a b (X.M σ) (k - X.Y σ) =
      a / q * (X.w σ * fL q (X.M σ) (k - X.Y σ)) + b / (1 - q) * (X.w σ * fR q (X.M σ) (k - X.Y σ)) := by
    intro σ _
    unfold kernel2
    ring
  rw [Finset.sum_congr rfl hσ, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, X.sum_fL_eq,
    X.sum_fR_eq]
  have h1 : a / q * ((1 - q) * X.prob q k - q * X.prob q (k - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg ha hq0.le) (by linarith)
  have h2 : b / (1 - q) * (q * X.prob q k - (1 - q) * X.prob q (k + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hb (by linarith)) (by linarith)
  linarith

/-- **The priced rows in expectation**: `E[∑_k z_k s_k^M] ≤ ∑_k z_k e_k` when `z_k ≥ 0` and `E[s_k^M] ≤ e_k`
(by linearity; the weights' sign is not needed). -/
theorem sum_pricedTail_le :
    ∀ (z : List ℝ) (rows : List (ℝ × ℝ)), (∀ x ∈ z, 0 ≤ x) →
      (∀ r ∈ rows, X.expect (fun M _ => r.1 ^ M) ≤ r.2) →
      ∑ σ ∈ X.S, X.w σ * pricedTail z rows (X.M σ) ≤ pricedMargin z rows := by
  intro z
  induction z with
  | nil => intro rows _ _; simp
  | cons x xs ih =>
    intro rows hz hrows
    cases rows with
    | nil => simp
    | cons r rs =>
      simp only [pricedTail_cons_cons, pricedMargin_cons_cons]
      have hx : 0 ≤ x := hz x (List.mem_cons_self ..)
      have hr : X.expect (fun M _ => r.1 ^ M) ≤ r.2 := hrows r (List.mem_cons_self ..)
      have ih' := ih rs (fun y hy => hz y (List.mem_cons_of_mem _ hy))
        (fun r' hr' => hrows r' (List.mem_cons_of_mem _ hr'))
      have hsplit : ∑ σ ∈ X.S, X.w σ * (x * r.1 ^ X.M σ + pricedTail xs rs (X.M σ)) =
          x * X.expect (fun M _ => r.1 ^ M) + ∑ σ ∈ X.S, X.w σ * pricedTail xs rs (X.M σ) := by
        unfold Mixture.expect
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring
      rw [hsplit]
      have := mul_le_mul_of_nonneg_left hr hx
      linarith

end Mixture

/-- **The MGF + two-sided no-valley lemma** (SPEC §1, PROVED there in one line).  For `0 < q < 1`, the criterion
`ExplicitThresholdMGF2 q m θ D rows` implies the no-valley property `NoValleyAtMGF2 q m θ D rows`.

Proof: under a weak valley, the expectation of (P) has left side
`E[a f_L/q + b f_R/(1 − q)] + c E δ + ν E δ² ≤ 0 + 0 + ν θ q(1 − q) m` and right side
`α − γ Var M − E[∑ z_k s_k^M] ≥ α − γ D m − ∑ z_k e_k`, contradicting (Mg). -/
theorem noValleyAtMGF2_of_explicit {q m θ D : ℝ} {rows : List (ℝ × ℝ)} (hq0 : 0 < q) (hq1 : q < 1)
    (h : ExplicitThresholdMGF2 q m θ D rows) : NoValleyAtMGF2 q m θ D rows := by
  intro ι X k hX hmean hδ hδ2 hvar hrows hvalley
  obtain ⟨ν, c, α, β, γ, a, b, z, hν, hγ, ha, hb, hz, hpt, hthr⟩ := h
  have hw : ∀ σ ∈ X.S, 0 ≤ X.w σ := hX.1
  -- (1) `E kernel2 ≤ 0` under the weak valley
  have hEκ := X.sum_kernel2_nonpos hq0 hq1 ha hb hvalley
  -- (2) the pointwise bound, summed: `E[π − tail] ≤ E kernel2 + c E δ + ν E δ²`
  have hEh : ∑ σ ∈ X.S, X.w σ * (α + β * ((X.M σ : ℝ) - m) - γ * ((X.M σ : ℝ) - m) ^ 2 -
      pricedTail z rows (X.M σ)) ≤
      ∑ σ ∈ X.S, X.w σ * kernel2 q a b (X.M σ) (k - X.Y σ) +
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
    have e : X.w σ * (kernel2 q a b (X.M σ) (k - X.Y σ) + c * delta q k (X.M σ) (X.Y σ) +
        ν * delta q k (X.M σ) (X.Y σ) ^ 2) =
        X.w σ * kernel2 q a b (X.M σ) (k - X.Y σ) + c * (X.w σ * delta q k (X.M σ) (X.Y σ)) +
          ν * (X.w σ * delta q k (X.M σ) (X.Y σ) ^ 2) := by ring
    linarith
  -- (3) `E π = α − γ Var M` and `E tail ≤ ∑ z_k e_k`
  have hEπ := X.sum_quadMinorant_eq hX hmean α β γ
  have hEt := X.sum_pricedTail_le z rows hz hrows
  have hsplit : ∑ σ ∈ X.S, X.w σ * (α + β * ((X.M σ : ℝ) - m) - γ * ((X.M σ : ℝ) - m) ^ 2 -
      pricedTail z rows (X.M σ)) =
      ∑ σ ∈ X.S, X.w σ * (α + β * ((X.M σ : ℝ) - m) - γ * ((X.M σ : ℝ) - m) ^ 2) -
        ∑ σ ∈ X.S, X.w σ * pricedTail z rows (X.M σ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  -- (4) the contradiction
  have hνδ2 : ν * X.expect (fun M Y => delta q k M Y ^ 2) ≤ ν * (θ * (q * (1 - q)) * m) :=
    mul_le_mul_of_nonneg_left hδ2 hν.le
  have hγvar : γ * X.varM ≤ γ * (D * m) := mul_le_mul_of_nonneg_left hvar hγ
  rw [hδ, mul_zero, add_zero] at hEh
  rw [hsplit, hEπ] at hEh
  nlinarith

/-- **Today's criterion is the case `a = b = 1` with no rows**: T1's explicit threshold with no tail cutoff (`M1 = 0`,
so no tail prices) gives the MGF2 criterion with the empty row list. -/
theorem explicitThresholdMGF2_of_explicitThreshold_zero {q m θ D : ℝ} {T : ℕ → ℝ}
    (h : ExplicitThreshold q m θ D T 0) : ExplicitThresholdMGF2 q m θ D [] := by
  obtain ⟨ν, c, α, β, γ, hf, S, hν, hγ, hpt, hquad, -, -, -, hthr⟩ := h
  refine ⟨ν, c, α, β, γ, 1, 1, [], hν, hγ, zero_le_one, zero_le_one, by simp, ?_, ?_⟩
  · intro M j
    rw [pricedTail_nil_right, sub_zero, ← kappa_eq_kernel2]
    exact (hquad M (Nat.zero_le M)).trans (hpt M j)
  · rw [pricedMargin_nil_right, sub_zero]
    simpa using hthr

/-! ## The rows of a tilt profile, and O3 in MGF form -/

/-- **The MGF rows at `(q, m)` of a list of tilts `(t_k, ℓ_k)`** (SPEC §2): `s_k = 1 − q + q t_k`, `e_k = e^{−ℓ_k m}`. -/
noncomputable def mgfRows (tilts : List (ℝ × ℝ)) (q m : ℝ) : List (ℝ × ℝ) :=
  tilts.map fun p => (1 - q + q * p.1, Real.exp (-(p.2 * m)))

/-- The real tilts of a list of rational tilts `(t_k, ℓ_k)` (the checker's data). -/
noncomputable def castTilts (l : List (ℚ × ℚ)) : List (ℝ × ℝ) := l.map fun x => ((x.1 : ℝ), (x.2 : ℝ))

theorem mem_mgfRows_castTilts {l : List (ℚ × ℚ)} {q m : ℝ} {r : ℝ × ℝ} :
    r ∈ mgfRows (castTilts l) q m ↔
      ∃ x ∈ l, r = (1 - q + q * ((x.1 : ℚ) : ℝ), Real.exp (-(((x.2 : ℚ) : ℝ) * m))) := by
  unfold mgfRows castTilts
  simp only [List.map_map, List.mem_map, Function.comp]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- **O3 in MGF form at `n ≥ N`** for a tilt profile `tilts : ℝ → List (ℝ × ℝ)` (the certified tilts and rates at the
activity `t`): for every forest with `n ≥ N`, every activity in range at an interior rank and every maximum-weight
independent set `B`, `E[(1 − q + q t_k)^M] ≤ e^{−ℓ_k m}` for every tilt `(t_k, ℓ_k)` of `tilts t`, with `q = t/(1 + t)`
and `m = E M` of the forest mixture. -/
def TailBoundMGF (N : ℕ) (tilts : ℝ → List (ℝ × ℝ)) : Prop :=
  ∀ F : FiniteForest, N ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    ∀ r ∈ mgfRows (tilts t) (actQ t) (forestMixture F B t).meanM,
      (forestMixture F B t).expect (fun M _ => r.1 ^ M) ≤ r.2

/-- The quantitative profile of the MGF route: the caps `θ(λ)` (O2), `D(λ)` (O1), the certified tilts `(t_k, ℓ_k)`
of the activity (O3, in MGF form) and the floor of the expected free count (O5). -/
structure ProfileMGF where
  /-- variance-ratio bound `θ(λ)` (O2) -/
  θb : ℝ → ℝ
  /-- variance bound `D(λ)`: `Var M ≤ D m` (O1) -/
  Db : ℝ → ℝ
  /-- the certified tilts `(t_k, ℓ_k)` at the activity (O3): `E[(1 − q + q t_k)^M] ≤ e^{−ℓ_k m}` -/
  tilts : ℝ → List (ℝ × ℝ)
  /-- the floor of the expected free count (O5) -/
  mfloor : ℝ → ℝ

/-- **O4 in MGF form on a strip of means**: at every activity in range and every `m ∈ [mfloor(λ), mcap(λ)]`, the
no-valley property in MGF form with the profile's caps and rows. -/
def ThresholdNoValleyMGF2 (P : ProfileMGF) (mcap : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, InRange t → ∀ m : ℝ, P.mfloor t ≤ m → m ≤ mcap t →
    NoValleyAtMGF2 (actQ t) m (P.θb t) (P.Db t) (mgfRows (P.tilts t) (actQ t) m)

end Erdos993Lean.Analytic
