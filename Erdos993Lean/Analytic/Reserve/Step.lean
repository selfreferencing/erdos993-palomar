module

public import Mathlib
public import Erdos993Lean.Analytic.Reserve.Defs

/-!
# O1 by the two-generation reserve: the algebraic induction step

Sources:
the two-generation reserve proof (equations (1), (4), (5), (Q0), (QC), (QB)),
the sharp first-four reserve proof, the lower sharp alternate reserve proof,
and, for the signed linear term,
the upper sharp signed-port proof (comparisons
(Q) there: CC, CB, BC).

This file is graph-free.  It proves the reserve step for a general reserve
`Φ(y, u) = α y + β u + γ u²/y` (the four bands of `Reserve/Defs.lean` use `β = 0`) over an abstract
finite list of children.  At a parent with selection indicator `a ∈ {0, 1}` and children `i ∈ I`
(child indicator `aᵢ`, grandchild log-mass `Tᵢ`, port `uᵢ`, and the two endpoint budgets `Fᵢ`
(parent unoccupied) and `Gᵢ` (parent occupied)), put `Y = ∑ yᵢ` with `yᵢ = lmass λ Tᵢ`,
`p = msg λ Y`, `y₀ = lmass λ Y`.  Given `Fᵢ ≥ Φ(yᵢ, uᵢ)` for every child and the grandchild bound
`Gᵢ ≥ α Tᵢ + β (aᵢ − uᵢ/sᵢ) + γ (aᵢ − uᵢ/sᵢ)²/Tᵢ` (`sᵢ = msg λ Tᵢ`, for `Tᵢ > 0`; a child with
`Tᵢ = 0` is a selected leaf, `aᵢ = 1`, `Gᵢ = 0`, `uᵢ = sᵢ`), the recursion value
`A p a + (1 − p) ∑ Fᵢ + p ∑ Gᵢ − p (1 − p)(a − ∑ uᵢ)²` is at least `Φ(y₀, u)` with
`u = p (a − ∑ uᵢ)` (`reserve_step_cert`).  With no children the step is the selected-leaf base.

Main results:
* messages: `msg_pos`, `msg_lt_one`, `one_sub_msg`, `lmass_pos`, `lmass_eq_neg_log`, `msg_zero`,
  `lmass_zero`;
* `child_payment`: the child quadratic ((5) with the signed term) is at least `y` times the
  comparison of its parent/child type — CC (unselected/unselected), CB (unselected/selected), BC
  (selected/unselected) — plus a completed square in the response `u/s`, and at the physical
  selected-leaf endpoint `T = 0` it is at least `y · CB` at `T = 0`;
* `parent_step`: summing the child payments and the rank-one Cauchy bound
  `(∑ uᵢ)² ≤ Y ∑ uᵢ²/yᵢ` (allocation of the parent constant in the proportions `yᵢ/Y`);
* `grand_bound`: the grandchild Cauchy bound `G ≥ α T + β (a − u/s) + γ (a − u/s)²/T`;
* `reserve_nonneg`: `Φ ≥ 0` for every real port when `β² ≤ 4αγ`;
* `StepCert λ α β γ A`: the per-activity certificate (comparisons at every feasible `(T, Y)`, the
  selected-leaf base, PSD), and **`reserve_step_cert`**: the induction step from it.

The specialization to the bands of `Reserve/Defs.lean` (`β = 0`) is `Reserve/StepBand.lean`.

Scalarity check.  The scalars carried here summarize named objects of the rooted subtree of a
child: `yᵢ = −log(1 − sᵢ)` is the log-mass of the child's downward occupation message `sᵢ` (the
probability that the child is occupied in its own subtree's hard-core law); `Tᵢ` and `Y` are the sums
of these log-masses over the actual grandchild and child lists; `uᵢ` is the port (the mean response
of the selected count `K_B` of the child's subtree to the parent's occupancy); `Fᵢ` and `Gᵢ` are
`A U − V` of the child's subtree with the parent unoccupied / occupied.  They are produced by the
tree recursion (`Reserve/Induction.lean`) and consumed here; the output is the parent's reserve.
The coefficients `E, H, L, J, Z` are local to one parent–child pair and are not carried; `α, β, γ, A`
are the fixed design coefficients of the certified step at the activity.  Minimizing over all real
`uᵢ` forgets the actual response (the reduction records this).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve

open Real Finset

/-! ### Messages and log-masses -/

section Msg

variable {lam : ℝ}

theorem msg_pos (hlam : 0 < lam) (X : ℝ) : 0 < msg lam X := by
  unfold msg
  positivity

theorem msg_lt_one (hlam : 0 < lam) (X : ℝ) : msg lam X < 1 := by
  unfold msg
  rw [div_lt_one (by positivity)]
  linarith

/-- `1 − msg λ X = 1/(1 + λ e^{−X})`. -/
theorem one_sub_msg (hlam : 0 < lam) (X : ℝ) : 1 - msg lam X = (1 + lam * exp (-X))⁻¹ := by
  have hD : 0 < 1 + lam * exp (-X) := by positivity
  unfold msg
  field_simp
  ring

theorem lmass_pos (hlam : 0 < lam) (X : ℝ) : 0 < lmass lam X := by
  unfold lmass
  apply Real.log_pos
  have : 0 < lam * exp (-X) := by positivity
  linarith

/-- The log-mass is `−log(1 − msg)`. -/
theorem lmass_eq_neg_log (hlam : 0 < lam) (X : ℝ) : lmass lam X = -log (1 - msg lam X) := by
  unfold lmass
  rw [one_sub_msg hlam, Real.log_inv, neg_neg]

theorem msg_zero (lam : ℝ) : msg lam 0 = actQ lam := by
  simp [msg, actQ]

theorem lmass_zero (lam : ℝ) : lmass lam 0 = log (1 + lam) := by
  simp [lmass]

end Msg

/-! ### The per-child payment -/

/-- **The per-child payment (inequality (5) with the signed term, and its three minima).**  For one
child of a parent, with `E, L, J, Z` the coefficients of `Reserve/Defs.lean` written out (and `H`
arbitrary), the child's share of the parent's reserve surplus is nonnegative whenever the comparison
of its parent/child type is: CC in the unselected–unselected case, CB in the unselected–selected
case, BC in the selected–unselected case (independence excludes selected–selected), and CB at the
physical selected-leaf endpoint `T = 0`.  Each case is `y ·` comparison plus a completed square in
`x = u/s`, so every real response is paid. -/
theorem child_payment {α β γ A p y₀ Y s y T a ac u Fc Gc E H L J Z : ℝ}
    (hγ : 0 < γ) (hp0 : 0 < p) (hp1 : p < 1) (hY : 0 < Y)
    (hs : 0 < s) (hy : 0 < y) (hT : 0 ≤ T)
    (ha : a = 0 ∨ a = 1) (hac : ac = 0 ∨ ac = 1) (hind : a = 1 → ac = 0)
    (hF : α * y + β * u + γ * u ^ 2 / y ≤ Fc)
    (hG : 0 < T → α * T + β * (ac - u / s) + γ * (ac - u / s) ^ 2 / T ≤ Gc)
    (hleaf : T = 0 → ac = 1 ∧ Gc = 0 ∧ u = s)
    (hEdef : E = 1 - p + p * T / y - y₀ / Y) (hLdef : L = γ * (1 - p) - H * Y)
    (hJdef : J = s ^ 2 * T / y) (hZdef : Z = p * γ + L * J) (hZ : 0 < Z)
    (hCC : 0 ≤ α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z))
    (hCB : 0 ≤ α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) + p * γ * L * (s / y) ^ 2 / Z +
      β * p * (γ * s + L * J) / (y * Z))
    (hBC : 0 ≤ α * E + ((A - β) * p - H) / Y - T / y * (H * s + β * (s - p) / 2) ^ 2 / Z) :
    0 ≤ y / Y * ((A - β) * p * a - H * a ^ 2 - α * y₀) + 2 * H * a * u + β * p * u -
      H * Y * u ^ 2 / y + (1 - p) * Fc + p * Gc := by
  have h1p : 0 < 1 - p := by linarith
  have hy' : y ≠ 0 := hy.ne'
  have hY' : Y ≠ 0 := hY.ne'
  have hs' : s ≠ 0 := hs.ne'
  have hp' : p ≠ 0 := hp0.ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  have hZ' : Z ≠ 0 := hZ.ne'
  have hFd : 0 ≤ (1 - p) * (Fc - (α * y + β * u + γ * u ^ 2 / y)) :=
    mul_nonneg h1p.le (sub_nonneg.mpr hF)
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · -- the physical selected-leaf endpoint `T = 0`
    obtain ⟨hac1, hG0, hus⟩ := hleaf hT0.symm
    have ha0 : a = 0 := by
      rcases ha with h | h
      · exact h
      · have := hind h
        rw [hac1] at this
        norm_num at this
    have hJ0 : J = 0 := by
      rw [hJdef, ← hT0]
      ring
    have hZp : Z = p * γ := by
      rw [hZdef, hJ0]
      ring
    have hCB0 : y * (α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) + p * γ * L * (s / y) ^ 2 / Z +
        β * p * (γ * s + L * J) / (y * Z)) = α * y * E + β * s + L * s ^ 2 / y := by
      rw [hJ0, hZp, ← hT0]
      field_simp
      ring
    have hid : y / Y * ((A - β) * p * a - H * a ^ 2 - α * y₀) + 2 * H * a * u + β * p * u -
        H * Y * u ^ 2 / y + (1 - p) * Fc + p * Gc =
        (α * y * E + β * s + L * s ^ 2 / y) + (1 - p) * (Fc - (α * y + β * u + γ * u ^ 2 / y)) := by
      rw [ha0, hG0, hus, hEdef, hLdef, ← hT0]
      field_simp
      ring
    rw [hid]
    have h1 := mul_nonneg hy.le hCB
    rw [hCB0] at h1
    linarith
  · -- `T > 0`: use the grandchild bound
    have hT' : T ≠ 0 := hTpos.ne'
    have hGd : 0 ≤ p * (Gc - (α * T + β * (ac - u / s) + γ * (ac - u / s) ^ 2 / T)) :=
      mul_nonneg hp0.le (sub_nonneg.mpr (hG hTpos))
    -- the lower bound `Q₀` in normal form, with `x = u/s`
    have hid : y / Y * ((A - β) * p * a - H * a ^ 2 - α * y₀) + 2 * H * a * u + β * p * u -
        H * Y * u ^ 2 / y + (1 - p) * Fc + p * Gc =
        (α * y * E + y / Y * ((A - β) * p * a - H * a ^ 2) + 2 * H * a * s * (u / s) +
          β * (s - p) * (u / s) + p * β * ac +
          ((Z - p * γ) * (u / s) ^ 2 + p * γ * (ac - u / s) ^ 2) / T) +
        (1 - p) * (Fc - (α * y + β * u + γ * u ^ 2 / y)) +
        p * (Gc - (α * T + β * (ac - u / s) + γ * (ac - u / s) ^ 2 / T)) := by
      rw [hEdef, hZdef, hLdef, hJdef]
      field_simp
      ring
    rw [hid]
    suffices hsuff : 0 ≤ α * y * E + y / Y * ((A - β) * p * a - H * a ^ 2) +
        2 * H * a * s * (u / s) + β * (s - p) * (u / s) + p * β * ac +
        ((Z - p * γ) * (u / s) ^ 2 + p * γ * (ac - u / s) ^ 2) / T by
      linarith
    set x := u / s with hx
    rcases ha with ha0 | ha1
    · -- unselected parent
      rcases hac with hac0 | hac1
      · -- unselected child: CC
        have key : α * y * E + y / Y * ((A - β) * p * a - H * a ^ 2) + 2 * H * a * s * x +
            β * (s - p) * x + p * β * ac + ((Z - p * γ) * x ^ 2 + p * γ * (ac - x) ^ 2) / T =
            y * (α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z)) +
              Z / T * (x + β * (s - p) * T / (2 * Z)) ^ 2 := by
          rw [ha0, hac0]
          field_simp
          ring
        rw [key]
        have h1 := mul_nonneg hy.le hCC
        have h2 : 0 ≤ Z / T * (x + β * (s - p) * T / (2 * Z)) ^ 2 := by positivity
        linarith
      · -- selected child: CB
        have hLZ : L = (Z - p * γ) * y / (s ^ 2 * T) := by
          rw [eq_div_iff (by positivity), hZdef, hJdef]
          field_simp
          ring
        have key : α * y * E + y / Y * ((A - β) * p * a - H * a ^ 2) + 2 * H * a * s * x +
            β * (s - p) * x + p * β * ac + ((Z - p * γ) * x ^ 2 + p * γ * (ac - x) ^ 2) / T =
            y * (α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) + p * γ * L * (s / y) ^ 2 / Z +
              β * p * (γ * s + L * J) / (y * Z)) +
              Z / T * (x + (β * (s - p) * T - 2 * p * γ) / (2 * Z)) ^ 2 := by
          rw [ha0, hac1, hLZ, hJdef]
          field_simp
          ring
        rw [key]
        have h1 := mul_nonneg hy.le hCB
        have h2 : 0 ≤ Z / T * (x + (β * (s - p) * T - 2 * p * γ) / (2 * Z)) ^ 2 := by positivity
        linarith
    · -- selected parent: the child is unselected, BC
      have hac0 := hind ha1
      have key : α * y * E + y / Y * ((A - β) * p * a - H * a ^ 2) + 2 * H * a * s * x +
          β * (s - p) * x + p * β * ac + ((Z - p * γ) * x ^ 2 + p * γ * (ac - x) ^ 2) / T =
          y * (α * E + ((A - β) * p - H) / Y - T / y * (H * s + β * (s - p) / 2) ^ 2 / Z) +
            Z / T * (x + (H * s + β * (s - p) / 2) * T / Z) ^ 2 := by
        rw [ha1, hac0]
        field_simp
        ring
      rw [key]
      have h1 := mul_nonneg hy.le hBC
      have h2 : 0 ≤ Z / T * (x + (H * s + β * (s - p) / 2) * T / Z) ^ 2 := by positivity
      linarith

/-! ### The Cauchy steps -/

/-- **The grandchild bound (inequality (4), second line, with the signed term).**  If every grandchild
`i` of a child carries the reserve `Fᵢ ≥ α yᵢ + β vᵢ + γ vᵢ²/yᵢ`, `T = ∑ yᵢ` and the child's port is
`u = s (a − ∑ vᵢ)`, then `∑ Fᵢ ≥ α T + β (a − u/s) + γ (a − u/s)²/T` (Cauchy over the actual
grandchild list). -/
theorem grand_bound {ι : Type*} (I : Finset ι) {α β γ T a s u : ℝ} (y v Fx : ι → ℝ)
    (hy : ∀ i ∈ I, 0 < y i) (hTdef : T = ∑ i ∈ I, y i) (hγ : 0 ≤ γ) (hs : s ≠ 0)
    (hu : u = s * (a - ∑ i ∈ I, v i))
    (hF : ∀ i ∈ I, α * y i + β * v i + γ * v i ^ 2 / y i ≤ Fx i) :
    α * T + β * (a - u / s) + γ * (a - u / s) ^ 2 / T ≤ ∑ i ∈ I, Fx i := by
  have hus : u / s = a - ∑ i ∈ I, v i := by
    rw [hu]
    field_simp
  have hav : a - u / s = ∑ i ∈ I, v i := by
    rw [hus]
    ring
  have hCS : (∑ i ∈ I, v i) ^ 2 / ∑ i ∈ I, y i ≤ ∑ i ∈ I, v i ^ 2 / y i :=
    Finset.sq_sum_div_le_sum_sq_div I v hy
  have hsum : ∑ i ∈ I, (α * y i + β * v i + γ * (v i ^ 2 / y i)) ≤ ∑ i ∈ I, Fx i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have := hF i hi
    have e : γ * (v i ^ 2 / y i) = γ * v i ^ 2 / y i := by ring
    linarith
  have e : ∑ i ∈ I, (α * y i + β * v i + γ * (v i ^ 2 / y i)) =
      α * ∑ i ∈ I, y i + β * ∑ i ∈ I, v i + γ * ∑ i ∈ I, v i ^ 2 / y i := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  rw [hav, hTdef]
  have h2 : γ * ((∑ i ∈ I, v i) ^ 2 / ∑ i ∈ I, y i) ≤ γ * ∑ i ∈ I, v i ^ 2 / y i :=
    mul_le_mul_of_nonneg_left hCS hγ
  have e2 : γ * (∑ i ∈ I, v i) ^ 2 / ∑ i ∈ I, y i =
      γ * ((∑ i ∈ I, v i) ^ 2 / ∑ i ∈ I, y i) := by ring
  linarith

/-- **The parent step (inequality (5) summed).**  If every child's share of the surplus is nonnegative,
then the recursion value is at least the parent's reserve `α y₀ + β u + γ u²/y₀`,
`u = p (a − ∑ uᵢ)`.  Uses the rank-one Cauchy bound `(∑ uᵢ)² ≤ Y ∑ uᵢ²/yᵢ` and the allocation of
the parent constant `(A − β) p a − H a² − α y₀` in the proportions `yᵢ/Y`. -/
theorem parent_step {ι : Type*} (I : Finset ι) {α β γ A p y₀ Y H a : ℝ} (y u Fc Gc : ι → ℝ)
    (hy : ∀ i ∈ I, 0 < y i) (hY : 0 < Y) (hYdef : Y = ∑ i ∈ I, y i) (hy₀ : 0 < y₀)
    (hHdef : H = p * (1 - p) + γ * p ^ 2 / y₀) (hH : 0 ≤ H)
    (hQ : ∀ i ∈ I, 0 ≤ y i / Y * ((A - β) * p * a - H * a ^ 2 - α * y₀) + 2 * H * a * u i +
      β * p * u i - H * Y * u i ^ 2 / y i + (1 - p) * Fc i + p * Gc i) :
    α * y₀ + β * (p * (a - ∑ i ∈ I, u i)) + γ * (p * (a - ∑ i ∈ I, u i)) ^ 2 / y₀ ≤
      A * p * a + (1 - p) * ∑ i ∈ I, Fc i + p * ∑ i ∈ I, Gc i -
        p * (1 - p) * (a - ∑ i ∈ I, u i) ^ 2 := by
  have hY' : Y ≠ 0 := hY.ne'
  have hy₀' : y₀ ≠ 0 := hy₀.ne'
  have hsum := Finset.sum_nonneg hQ
  have e : ∀ i ∈ I, y i / Y * ((A - β) * p * a - H * a ^ 2 - α * y₀) + 2 * H * a * u i +
      β * p * u i - H * Y * u i ^ 2 / y i + (1 - p) * Fc i + p * Gc i =
      ((A - β) * p * a - H * a ^ 2 - α * y₀) / Y * y i + (2 * H * a + β * p) * u i -
        (H * Y) * (u i ^ 2 / y i) + (1 - p) * Fc i + p * Gc i := by
    intro i _
    ring
  rw [Finset.sum_congr rfl e] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [← hYdef, div_mul_cancel₀ _ hY.ne'] at hsum
  have hCS : (∑ i ∈ I, u i) ^ 2 / Y ≤ ∑ i ∈ I, u i ^ 2 / y i := by
    rw [hYdef]
    exact Finset.sq_sum_div_le_sum_sq_div I u hy
  have h1 : (∑ i ∈ I, u i) ^ 2 ≤ (∑ i ∈ I, u i ^ 2 / y i) * Y := (div_le_iff₀ hY).mp hCS
  have h2 : H * (∑ i ∈ I, u i) ^ 2 ≤ H * ((∑ i ∈ I, u i ^ 2 / y i) * Y) :=
    mul_le_mul_of_nonneg_left h1 hH
  have eH : H * (a - ∑ i ∈ I, u i) ^ 2 =
      p * (1 - p) * (a - ∑ i ∈ I, u i) ^ 2 + γ * (p * (a - ∑ i ∈ I, u i)) ^ 2 / y₀ := by
    rw [hHdef]
    field_simp
  have eexp : H * (a - ∑ i ∈ I, u i) ^ 2 =
      H * a ^ 2 - 2 * H * a * ∑ i ∈ I, u i + H * (∑ i ∈ I, u i) ^ 2 := by
    ring
  have e3 : H * ((∑ i ∈ I, u i ^ 2 / y i) * Y) = H * Y * ∑ i ∈ I, u i ^ 2 / y i := by ring
  have e4 : (2 * H * a + β * p) * ∑ i ∈ I, u i =
      2 * H * a * ∑ i ∈ I, u i + β * p * ∑ i ∈ I, u i := by ring
  have e5 : β * (p * (a - ∑ i ∈ I, u i)) = β * p * a - β * p * ∑ i ∈ I, u i := by ring
  have e6 : ((A - β) * p * a - H * a ^ 2 - α * y₀) =
      A * p * a - β * p * a - H * a ^ 2 - α * y₀ := by ring
  linarith

/-- **The reserve is nonnegative (PSD).**  If `γ > 0`, `y > 0` and `β² ≤ 4αγ`, then
`α y + β u + γ u²/y ≥ 0` for every real `u`. -/
theorem reserve_nonneg {α β γ y u : ℝ} (hγ : 0 < γ) (hy : 0 < y)
    (hpsd : β ^ 2 ≤ 4 * α * γ) : 0 ≤ α * y + β * u + γ * u ^ 2 / y := by
  have key : α * y + β * u + γ * u ^ 2 / y =
      ((2 * γ * u + β * y) ^ 2 + (4 * α * γ - β ^ 2) * y ^ 2) / (4 * γ * y) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg y))

/-! ### The per-activity step certificate -/

section Cert

variable (γ lam : ℝ)

/-- `H = p (1 − p) + γ p²/y₀` at the parent log-mass `Y` (as `coefH`, with `γ` a parameter). -/
noncomputable def cH (Y : ℝ) : ℝ := msg lam Y * (1 - msg lam Y) + γ * msg lam Y ^ 2 / lmass lam Y

/-- `L = γ (1 − p) − H Y` (as `coefL`, with `γ` a parameter). -/
noncomputable def cL (Y : ℝ) : ℝ := γ * (1 - msg lam Y) - cH γ lam Y * Y

/-- `Z = p γ + L J` (as `coefZ`, with `γ` a parameter). -/
noncomputable def cZ (T Y : ℝ) : ℝ := msg lam Y * γ + cL γ lam Y * coefJ lam T

variable (α β A : ℝ)

/-- The unselected–unselected comparison `CC = α E − β² δ² T/(4 y Z)`, `δ = s − p`. -/
noncomputable def compCC (T Y : ℝ) : ℝ :=
  α * coefE lam T Y -
    β ^ 2 * (msg lam T - msg lam Y) ^ 2 * T / (4 * lmass lam T * cZ γ lam T Y)

/-- The unselected–selected comparison `CB = CC + p γ L (s/y)²/Z + β p (γ s + L J)/(y Z)`. -/
noncomputable def compCB (T Y : ℝ) : ℝ :=
  α * coefE lam T Y -
      β ^ 2 * (msg lam T - msg lam Y) ^ 2 * T / (4 * lmass lam T * cZ γ lam T Y) +
    msg lam Y * γ * cL γ lam Y * (msg lam T / lmass lam T) ^ 2 / cZ γ lam T Y +
    β * msg lam Y * (γ * msg lam T + cL γ lam Y * coefJ lam T) / (lmass lam T * cZ γ lam T Y)

/-- The selected–unselected comparison
`BC = α E + ((A − β) p − H)/Y − (T/y)(H s + β δ/2)²/Z`. -/
noncomputable def compBC (T Y : ℝ) : ℝ :=
  α * coefE lam T Y + ((A - β) * msg lam Y - cH γ lam Y) / Y -
    T / lmass lam T * (cH γ lam Y * msg lam T + β * (msg lam T - msg lam Y) / 2) ^ 2 /
      cZ γ lam T Y

/-- **The per-activity step certificate** for the reserve `α y + β u + γ u²/y` with cap `A` at
activity `λ`: positivity, PSD (`β² ≤ 4αγ`, so the reserve is nonnegative at the root), the
selected-leaf base (`F = A q − q(1 − q)`, `u = q`, `y = log(1 + λ)` at a selected leaf), and the
comparisons `Z > 0`, CC, CB, BC at every feasible point `T ≥ 0`, `Y ≥ lmass λ T`. -/
structure StepCert : Prop where
  lam_pos : 0 < lam
  alpha_nonneg : 0 ≤ α
  gamma_pos : 0 < γ
  psd : β ^ 2 ≤ 4 * α * γ
  leaf : α * lmass lam 0 + β * msg lam 0 + γ * msg lam 0 ^ 2 / lmass lam 0 ≤
    A * msg lam 0 - msg lam 0 * (1 - msg lam 0)
  comp : ∀ T Y : ℝ, 0 ≤ T → lmass lam T ≤ Y →
    0 < cZ γ lam T Y ∧ 0 ≤ compCC γ lam α β T Y ∧ 0 ≤ compCB γ lam α β T Y ∧
      0 ≤ compBC γ lam α β A T Y

end Cert

/-- **The reserve step at one vertex, from the step certificate.**  For a vertex with selection
indicator `a` and children `i ∈ I` (possibly none, then `a = 1`: the selected-leaf base), with
`Y = ∑ lmass λ Tᵢ`, `p = msg λ Y`, `y₀ = lmass λ Y`: if every child carries the reserve and the
grandchild bound (or is a selected leaf, `Tᵢ = 0`), then the recursion value of the vertex is at
least `α y₀ + β u + γ u²/y₀`, `u = p (a − ∑ uᵢ)`. -/
theorem reserve_step_cert {lam α β γ A : ℝ} (hcert : StepCert γ lam α β A)
    {ι : Type*} (I : Finset ι) (a : ℝ) (ha : a = 0 ∨ a = 1) (hroot : I = ∅ → a = 1)
    (ac u Fc Gc T : ι → ℝ)
    (hac : ∀ i ∈ I, ac i = 0 ∨ ac i = 1) (hind : a = 1 → ∀ i ∈ I, ac i = 0)
    (hT : ∀ i ∈ I, 0 ≤ T i)
    (hF : ∀ i ∈ I, α * lmass lam (T i) + β * u i + γ * u i ^ 2 / lmass lam (T i) ≤ Fc i)
    (hG : ∀ i ∈ I, 0 < T i →
      α * T i + β * (ac i - u i / msg lam (T i)) + γ * (ac i - u i / msg lam (T i)) ^ 2 / T i ≤
        Gc i)
    (hleaf : ∀ i ∈ I, T i = 0 → ac i = 1 ∧ Gc i = 0 ∧ u i = msg lam (T i)) :
    α * lmass lam (∑ i ∈ I, lmass lam (T i)) +
        β * (msg lam (∑ i ∈ I, lmass lam (T i)) * (a - ∑ i ∈ I, u i)) +
        γ * (msg lam (∑ i ∈ I, lmass lam (T i)) * (a - ∑ i ∈ I, u i)) ^ 2 /
          lmass lam (∑ i ∈ I, lmass lam (T i)) ≤
      A * msg lam (∑ i ∈ I, lmass lam (T i)) * a +
        (1 - msg lam (∑ i ∈ I, lmass lam (T i))) * ∑ i ∈ I, Fc i +
        msg lam (∑ i ∈ I, lmass lam (T i)) * ∑ i ∈ I, Gc i -
        msg lam (∑ i ∈ I, lmass lam (T i)) * (1 - msg lam (∑ i ∈ I, lmass lam (T i))) *
          (a - ∑ i ∈ I, u i) ^ 2 := by
  have hlam := hcert.lam_pos
  have hγ := hcert.gamma_pos
  rcases I.eq_empty_or_nonempty with hI0 | hIne
  · -- no children: the selected-leaf base
    have ha1 := hroot hI0
    subst hI0
    rw [ha1]
    simp only [Finset.sum_empty]
    have hL := hcert.leaf
    refine le_of_le_of_eq (le_of_eq_of_le ?_ hL) ?_
    · ring
    · ring
  · -- children: the parent step
    set Y := ∑ i ∈ I, lmass lam (T i) with hYdef
    have hy : ∀ i ∈ I, 0 < lmass lam (T i) := fun i _ => lmass_pos hlam _
    have hY : 0 < Y := Finset.sum_pos hy hIne
    have hp0 := msg_pos hlam Y
    have hp1 := msg_lt_one hlam Y
    have hy₀ := lmass_pos hlam Y
    have hH0 : 0 ≤ cH γ lam Y := by
      unfold cH
      have : 0 < 1 - msg lam Y := by linarith
      exact add_nonneg (mul_nonneg hp0.le this.le)
        (div_nonneg (mul_nonneg hγ.le (sq_nonneg _)) hy₀.le)
    refine parent_step I (α := α) (β := β) (γ := γ) (A := A)
      (p := msg lam Y) (y₀ := lmass lam Y) (Y := Y) (H := cH γ lam Y) (a := a)
      (fun i => lmass lam (T i)) u Fc Gc hy hY hYdef hy₀ rfl hH0 fun i hi => ?_
    -- the per-child payment
    have hyY : lmass lam (T i) ≤ Y := by
      rw [hYdef]
      exact Finset.single_le_sum (f := fun j => lmass lam (T j)) (fun j hj => (hy j hj).le) hi
    obtain ⟨hZ, hCC, hCB, hBC⟩ := hcert.comp (T i) Y (hT i hi) hyY
    exact child_payment (A := A) (E := coefE lam (T i) Y) (H := cH γ lam Y)
      (L := cL γ lam Y) (J := coefJ lam (T i)) (Z := cZ γ lam (T i) Y)
      hγ hp0 hp1 hY (msg_pos hlam (T i)) (hy i hi) (hT i hi) ha
      (hac i hi) (fun h => hind h i hi) (hF i hi) (hG i hi) (hleaf i hi) rfl rfl rfl rfl
      hZ hCC hCB hBC

end Erdos993Lean.Analytic.Reserve
