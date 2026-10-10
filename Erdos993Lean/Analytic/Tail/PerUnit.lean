module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.Reduction

/-!
# The tail input T3, part 12: Theorem T3-1 (the per-unit rate, no potential)

Sources: T23 §3, Theorem T3-1
in the general-`z` form of
the per-unit proof §3 (whose rates are certified there with interval arithmetic).

For `Y > 0` put `p_max = p_c(Y) = λ e^{−Y}/(1 + λ e^{−Y})`, `d(λ, Y) = 1 − h(p_max)`
(`= (1 + λ)/(1 + λ + λ e^{−Y})`, `dmax_eq`), `G = −log(p_max + (1 − p_max) e^{−ρ Y})`,
`ρ = r(λ, z)` (`rFallback`).  **`PerUnitRate λ z ℓ`**: `ℓ d(λ, Y) Y ≤ q G` for every `Y > 0`
(i.e. `ℓ ≤ R(λ, Y, z) = q G/(d Y)`).

**Theorem (`t31_reduction`).**  For every forest, every independent set `B` (no leaf or
maximality condition), `λ > 0`, `z ∈ [0, 1]`, `ℓ ≥ 0` with `ℓ ≤ log((1 + λ)/(1 + λ z))`: if
`PerUnitRate λ z ℓ` then `E(1 − q + q z)^M ≤ exp(−ℓ m)`.

Proof: per C-unit, `−log τ_c ≥ G(p_c)` (Lemma A, `Y_z ≥ ρ Y`), and `G(p)/d(p)` decreases in
`p` (`chord_mono`: with `w = 1 − p`, `G/d = (1/w + λ) g(w)/(1 + λ)`, `g(w) = −log(1 − (1 − e^{−ρY}) w)`
convex with `g(0) = 0`, via Bernoulli's inequality), so the worst `p_c ≤ p_max` is `p_max`:
`−log τ_c ≥ (ℓ/q) d(p_c) Y_c ≥ (ℓ/q)(1 − π_c) s_c` (Lemma B, `s_c ≤ Y_c`).  Units with `Y_c = 0`
have `τ_c = 1` and no mean; isolated B-vertices use `ℓ ≤ log((1 + λ)/(1 + λ z))`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

/-! ### Scalar facts -/

/-- **The per-unit condition** `ℓ ≤ R(λ, Y, z)` for all `Y > 0`, without division:
`ℓ (1 − h(p_max)) Y ≤ q · (−log(p_max + (1 − p_max) e^{−ρ Y}))`, `p_max = p_c(Y)`. -/
def PerUnitRate (lam z ell : ℝ) : Prop :=
  ∀ Y : ℝ, 0 < Y → ell * (1 - hmin lam (pC lam Y)) * Y ≤
    actQ lam * -Real.log (pC lam Y + (1 - pC lam Y) * Real.exp (-(rFallback lam z * Y)))

/-- `1 − h(p) = (1 + λ)(1 − p)/(1 + λ(1 − p))`. -/
theorem one_sub_hmin {lam p : ℝ} (hlam0 : 0 ≤ lam) (hp1 : p ≤ 1) :
    1 - hmin lam p = (1 + lam) * (1 - p) / (1 + lam * (1 - p)) := by
  unfold hmin
  have hD : 0 < 1 + lam * (1 - p) := by nlinarith
  rw [one_sub_div hD.ne']
  congr 1
  ring

/-- `d(λ, Y) = 1 − h(p_c(Y)) = (1 + λ)/(1 + λ + λ e^{−Y})` (the function `d`). -/
theorem dmax_eq {lam : ℝ} (hlam0 : 0 < lam) (Y : ℝ) :
    1 - hmin lam (pC lam Y) = (1 + lam) / (1 + lam + lam * Real.exp (-Y)) := by
  rw [one_sub_hmin hlam0.le (pC_lt_one hlam0 Y).le, one_sub_pC hlam0]
  have hE : 0 < Real.exp (-Y) := Real.exp_pos _
  have hD : 0 < 1 + lam * Real.exp (-Y) := by positivity
  field_simp
  ring

theorem one_sub_hmin_nonneg {lam p : ℝ} (hlam0 : 0 ≤ lam) (hp1 : p ≤ 1) :
    0 ≤ 1 - hmin lam p := by
  rw [one_sub_hmin hlam0 hp1]
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- **The chord inequality**: `g(w) = −log(1 − a w)` (`0 ≤ a < 1`) has `g(w₁)/w₁ ≤ g(w₂)/w₂` for
`0 < w₁ ≤ w₂ ≤ 1` (convexity and `g(0) = 0`, via Bernoulli's inequality). -/
theorem chord_mono {a w1 w2 : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hw1 : 0 < w1) (h12 : w1 ≤ w2)
    (hw2 : w2 ≤ 1) : -Real.log (1 - a * w1) / w1 ≤ -Real.log (1 - a * w2) / w2 := by
  have hw2pos : 0 < w2 := lt_of_lt_of_le hw1 h12
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = w1 / w2 := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := hθ ▸ div_nonneg hw1.le hw2pos.le
  have hθ1 : θ ≤ 1 := hθ ▸ (div_le_one hw2pos).mpr h12
  have hpos2 : 0 < 1 - a * w2 := by nlinarith
  have hpos1 : 0 < 1 - a * w1 := by nlinarith
  -- Bernoulli: `(1 − a w₂)^θ ≤ 1 − θ a w₂ = 1 − a w₁`
  have hb := rpow_one_add_le_one_add_mul_self (s := -(a * w2)) (by nlinarith) hθ0 hθ1
  have hθw : θ * w2 = w1 := by rw [hθ]; exact div_mul_cancel₀ w1 hw2pos.ne'
  have hb' : (1 - a * w2) ^ θ ≤ 1 - a * w1 := by
    rw [show 1 + -(a * w2) = 1 - a * w2 by ring] at hb
    calc (1 - a * w2) ^ θ ≤ 1 + θ * -(a * w2) := hb
      _ = 1 - a * (θ * w2) := by ring
      _ = 1 - a * w1 := by rw [hθw]
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hpos2 θ) hb'
  rw [Real.log_rpow hpos2] at hlog
  -- `g(w₁) ≤ θ g(w₂)`, then divide by `w₁ = θ w₂`
  rw [div_le_div_iff₀ hw1 hw2pos]
  have : -Real.log (1 - a * w1) * w2 ≤ -(θ * Real.log (1 - a * w2)) * w2 :=
    mul_le_mul_of_nonneg_right (by linarith) hw2pos.le
  calc -Real.log (1 - a * w1) * w2 ≤ -(θ * Real.log (1 - a * w2)) * w2 := this
    _ = -Real.log (1 - a * w2) * (θ * w2) := by ring
    _ = -Real.log (1 - a * w2) * w1 := by rw [hθw]

/-- **The per-unit monotonicity**: `G(p)/d(p)` decreases in `p`; hence at `p ≤ p_max(Y)`,
`PerUnitRate` at `Y` gives `−log(p + (1 − p) e^{−ρ Y}) ≥ (ℓ/q)(1 − h(p)) Y`. -/
theorem perunit_scalar {lam ρ Y ell p : ℝ} (hlam0 : 0 < lam) (hρ0 : 0 ≤ ρ) (hY : 0 < Y)
    (hp0 : 0 < p) (hpmax : p ≤ pC lam Y)
    (hR : ell * (1 - hmin lam (pC lam Y)) * Y ≤
      actQ lam * -Real.log (pC lam Y + (1 - pC lam Y) * Real.exp (-(ρ * Y)))) :
    ell / actQ lam * ((1 - hmin lam p) * Y) ≤ -Real.log (p + (1 - p) * Real.exp (-(ρ * Y))) := by
  have hq0 := actQ_pos hlam0
  have hP1 := pC_lt_one hlam0 Y
  have hp1 : p < 1 := lt_of_le_of_lt hpmax hP1
  obtain ⟨x, hx⟩ : ∃ x, x = Real.exp (-(ρ * Y)) := ⟨_, rfl⟩
  have hx0 : 0 < x := hx ▸ Real.exp_pos _
  have hx1 : x ≤ 1 := hx ▸ Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← hx] at hR ⊢
  obtain ⟨P, hP⟩ : ∃ P, P = pC lam Y := ⟨_, rfl⟩
  rw [← hP] at hR hpmax hP1
  have hGp : p + (1 - p) * x = 1 - (1 - x) * (1 - p) := by ring
  have hGP : P + (1 - P) * x = 1 - (1 - x) * (1 - P) := by ring
  rw [hGp, one_sub_hmin hlam0.le hp1.le]
  rw [hGP, one_sub_hmin hlam0.le hP1.le] at hR
  obtain ⟨a, ha⟩ : ∃ a, a = 1 - x := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = 1 - p := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 1 - P := ⟨_, rfl⟩
  rw [← ha, ← hw]
  rw [← ha, ← hW] at hR
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a < 1 := by linarith
  have hw0 : 0 < w := by linarith
  have hW0 : 0 < W := by linarith
  have hWw : W ≤ w := by linarith
  have hw1 : w ≤ 1 := by linarith
  have hDW : 0 < 1 + lam * W := by positivity
  have hDw : 0 < 1 + lam * w := by positivity
  obtain ⟨gw, hgw⟩ : ∃ g, g = -Real.log (1 - a * w) := ⟨_, rfl⟩
  obtain ⟨gW, hgW⟩ : ∃ g, g = -Real.log (1 - a * W) := ⟨_, rfl⟩
  -- the chord inequality and monotonicity of `g`
  have hchord : gW * w ≤ gw * W := by
    have h := chord_mono ha0 ha1 hW0 hWw hw1
    rw [← hgW, ← hgw, div_le_div_iff₀ hW0 hw0] at h
    exact h
  have hmono : gW ≤ gw := by
    rw [hgW, hgw]
    have h1 : 0 < 1 - a * w := by nlinarith
    have := Real.log_le_log h1 (by nlinarith : 1 - a * w ≤ 1 - a * W)
    linarith
  rw [← hgW] at hR
  rw [← hgw]
  -- `A W ≤ q g(W)(1 + λ W)` with `A = ℓ (1 + λ) Y`
  have h1 : ell * (1 + lam) * Y * W ≤ actQ lam * gW * (1 + lam * W) := by
    have e : ell * ((1 + lam) * W / (1 + lam * W)) * Y =
        ell * (1 + lam) * Y * W / (1 + lam * W) := by ring
    rw [e, div_le_iff₀ hDW] at hR
    linarith
  -- `A w W ≤ q g(w)(1 + λ w) W`, then cancel `W`
  have h4 : ell * (1 + lam) * Y * w * W ≤ actQ lam * gw * (1 + lam * w) * W := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hw0.le, mul_le_mul_of_nonneg_left hchord hq0.le,
      mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ actQ lam * lam * W * w)]
  have h5 : ell * (1 + lam) * Y * w ≤ actQ lam * gw * (1 + lam * w) :=
    le_of_mul_le_mul_right h4 hW0
  have e2 : ell / actQ lam * ((1 + lam) * w / (1 + lam * w) * Y) =
      ell * (1 + lam) * Y * w / (actQ lam * (1 + lam * w)) := by
    field_simp
  rw [e2, div_le_iff₀ (by positivity)]
  linarith

/-! ### On a rooted tree -/

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

section Tree

variable {B : Finset V} {lam z ell : ℝ}

/-- One unit under `PerUnitRate`: `τ ≤ exp(−(ℓ/q)(1 − h(p_r)) Y)`. -/
theorem toyLocal_le_exp_perunit (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (hlam0 : 0 < lam)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hR : PerUnitRate lam z ell) {s : Finset V}
    (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    toyLocal G B lam z s r ≤ Real.exp (-(ell / actQ lam) *
      ((1 - hmin lam (rootProb G lam s r)) * unitY G B lam s r)) := by
  unfold toyLocal
  by_cases hrB : r ∈ B
  · rw [if_pos hrB]
    have hY : unitY G B lam s r = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      rw [if_neg]
      intro hwB
      exact hB r hrB w hwB (mem_nbrsIn.mp hw).2
    rw [hY, mul_zero, mul_zero, Real.exp_zero]
  · rw [if_neg hrB]
    have hY0 := unitY_nonneg (G := G) (B := B) hlam0.le s r
    have hp0 := rootProb_pos (G := G) hlam0 s r
    have hp1 := rootProb_lt_one (G := G) hlam0.le hr
    have hρ0 := rFallback_nonneg hlam0 hz0 hz1
    -- `τ ≤ p + (1 − p) e^{−ρ Y}`
    have hτ : tauC G B lam z s r ≤ rootProb G lam s r + (1 - rootProb G lam s r) *
        Real.exp (-(rFallback lam z * unitY G B lam s r)) := by
      rw [tauC, betaB_eq_exp hlam0.le hz0]
      have h1 := rFallback_mul_unitY_le (G := G) (B := B) hlam0 hz0 hz1 s r
      have h2 : Real.exp (-unitYz G B lam z s r) ≤
          Real.exp (-(rFallback lam z * unitY G B lam s r)) := Real.exp_le_exp.mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - rootProb G lam s r)]
    have hτ0 := toyLocal_pos (G := G) (B := B) hlam0 hz0 hz1 hr
    unfold toyLocal at hτ0
    rw [if_neg hrB] at hτ0
    rcases hY0.eq_or_lt with hY | hY
    · -- no B-children: `τ = 1`
      rw [← hY, mul_zero, mul_zero, Real.exp_zero]
      exact tauC_le_one hlam0.le hz0 hz1 hr
    · have hpmax : rootProb G lam s r ≤ pC lam (unitY G B lam s r) := by
        have := rootProb_le_unit (B := B) hG hlam0 hs hr
        unfold pC
        exact this
      have hunit := perunit_scalar hlam0 hρ0 hY hp0 hpmax (hR _ hY)
      have hpos : 0 < rootProb G lam s r + (1 - rootProb G lam s r) *
          Real.exp (-(rFallback lam z * unitY G B lam s r)) := by
        have : 0 < Real.exp (-(rFallback lam z * unitY G B lam s r)) := Real.exp_pos _
        nlinarith
      calc tauC G B lam z s r ≤ rootProb G lam s r + (1 - rootProb G lam s r) *
            Real.exp (-(rFallback lam z * unitY G B lam s r)) := hτ
        _ = Real.exp (Real.log (rootProb G lam s r + (1 - rootProb G lam s r) *
            Real.exp (-(rFallback lam z * unitY G B lam s r)))) := (Real.exp_log hpos).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          linarith

/-- **One component with a C-vertex** under `PerUnitRate`. -/
theorem toy_le_exp_perunit (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (hlam0 : 0 < lam)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hell : 0 ≤ ell) (hR : PerUnitRate lam z ell) {K : Finset V}
    (hK : ConnectedIn G K) {c : V} (hc : c ∈ K) (hcB : c ∉ B) :
    toy G B lam z K c ≤ Real.exp (-(ell / actQ lam) * ∑ b ∈ K.filter (· ∈ B), marg G lam K b) := by
  have hq0 := actQ_pos hlam0
  have hcq : 0 ≤ ell / actQ lam := div_nonneg hell hq0.le
  have h := treeProd_le_treeProd (G := G) hG (f := toyLocal G B lam z)
    (g := fun s r => Real.exp (-(ell / actQ lam) *
      ((1 - hmin lam (rootProb G lam s r)) * unitY G B lam s r)))
    (fun _ _ _ hr => toyLocal_nonneg hlam0.le hz0 hz1 hr)
    (fun _ _ hs hr => toyLocal_le_exp_perunit hG hB hlam0 hz0 hz1 hR hs hr) hK hc
  rw [treeProd_exp, treeSum_const_mul] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  -- `∑ π_b = mSum ≤ mSumMax ≤ ∑_c (1 − h(p_c)) Y_c`
  have hmean : ∑ b ∈ K.filter (· ∈ B), marg G lam K b ≤
      treeSum G (fun s r => (1 - hmin lam (rootProb G lam s r)) * unitY G B lam s r) K c := by
    rw [lemmaB_component hG hlam0.le hK hc hcB]
    refine (mSum_le_max hG hlam0 hK hc (one_div_le_one_of_rootProb hlam0.le hc) le_rfl).trans ?_
    unfold mSumMax
    apply treeSum_le_treeSum hG _ hK hc
    intro s r _ hr
    apply mul_le_mul_of_nonneg_left _ (one_sub_hmin_nonneg hlam0.le (rootProb_le_one hlam0.le hr))
    unfold sB unitY
    apply Finset.sum_le_sum
    intro w hw
    split_ifs
    · exact le_Lf (rootProb_lt_one hlam0.le (self_mem_branch hw))
    · exact le_rfl
  nlinarith [mul_le_mul_of_nonneg_left hmean hcq]

/-- **One component** under `PerUnitRate` (no leaf condition). -/
theorem t31_component (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (hlam0 : 0 < lam)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hR : PerUnitRate lam z ell)
    {K : Finset V} (hK : ConnectedIn G K) {x : V} (hx : x ∈ K) :
    phiF G B lam z K ≤
      Real.exp (-(ell / actQ lam) * ∑ b ∈ K.filter (· ∈ B), marg G lam K b) := by
  have hq0 := actQ_pos hlam0
  by_cases h : ∃ c ∈ K, c ∉ B
  · obtain ⟨c, hcK, hcB⟩ := h
    exact (phiF_le_toy hG hB hlam0.le hz0 hz1 hK hcK).trans
      (toy_le_exp_perunit hG hB hlam0 hz0 hz1 hell hR hK hcK hcB)
  · push_neg at h
    have hKB : K ⊆ B := fun c hc => h c hc
    have hKx := eq_singleton_of_subset_indep hB hK hKB hx
    subst hKx
    have hxB : x ∈ B := hKB (Finset.mem_singleton_self x)
    have hnil : nbrsIn G {x} x = ∅ := by
      ext y
      simp only [mem_nbrsIn, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      exact G.irrefl
    have hsum : ∑ b ∈ ({x} : Finset V).filter (· ∈ B), marg G lam {x} b = actQ lam := by
      rw [Finset.filter_singleton, if_pos hxB, Finset.sum_singleton,
        marg_of_mem (Finset.mem_singleton_self x),
        rootProb_eq_actQ hlam0.le (Finset.mem_singleton_self x) hnil]
    rw [hsum, neg_mul, div_mul_cancel₀ _ hq0.ne', phiF_singleton]
    unfold lapW
    rw [if_pos hxB]
    have h1 : 0 < 1 + lam * z := by positivity
    have h2 : 0 < 1 + lam := by linarith
    rw [show (1 + lam * z) / (1 + lam) = Real.exp (-Real.log ((1 + lam) / (1 + lam * z))) by
      rw [Real.exp_neg, Real.exp_log (div_pos h2 h1), inv_div]]
    exact Real.exp_le_exp.mpr (by linarith)

/-- **Theorem T3-1 on a vertex set** (any vertex set; no leaf condition). -/
theorem t31_set (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (hlam0 : 0 < lam)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hR : PerUnitRate lam z ell)
    (s : Finset V) :
    phiF G B lam z s ≤
      Real.exp (-(ell / actQ lam) * ∑ b ∈ s.filter (· ∈ B), marg G lam s b) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hne : s.Nonempty
    · obtain ⟨x, hxs⟩ := hne
      set K := compIn G s x with hK
      have hKc : ConnectedIn G K := connectedIn_compIn _ _
      have hxK : x ∈ K := self_mem_compIn hxs
      have hKs : K ⊆ s := compIn_subset _ _
      have hsub : s \ K ⊂ s := Finset.sdiff_ssubset hKs ⟨x, hxK⟩
      have hsplit : s.filter (· ∈ B) = K.filter (· ∈ B) ∪ (s \ K).filter (· ∈ B) := by
        rw [← Finset.filter_union, Finset.union_sdiff_of_subset hKs]
      have hdisj : Disjoint (K.filter (· ∈ B)) ((s \ K).filter (· ∈ B)) :=
        Finset.disjoint_filter_filter Finset.disjoint_sdiff
      have hno1 : ∀ a ∈ K, ∀ b ∈ s \ K, ¬ G.Adj a b := fun a ha b hb => not_adj_compIn_sdiff ha hb
      have hno2 : ∀ a ∈ s \ K, ∀ b ∈ s \ (s \ K), ¬ G.Adj a b := by
        intro a ha b hb hab
        rw [Finset.sdiff_sdiff_eq_self hKs] at hb
        exact hno1 b hb a ha hab.symm
      have hmass : ∑ b ∈ s.filter (· ∈ B), marg G lam s b =
          ∑ b ∈ K.filter (· ∈ B), marg G lam K b +
            ∑ b ∈ (s \ K).filter (· ∈ B), marg G lam (s \ K) b := by
        rw [hsplit, Finset.sum_union hdisj]
        congr 1
        · exact Finset.sum_congr rfl
            (fun b hb => marg_of_closed hlam0.le hKs hno1 (Finset.mem_filter.mp hb).1)
        · exact Finset.sum_congr rfl
            (fun b hb => marg_of_closed hlam0.le Finset.sdiff_subset hno2 (Finset.mem_filter.mp hb).1)
      rw [phiF_comp_split s x, hmass, mul_add, Real.exp_add]
      exact mul_le_mul (t31_component hG hB hlam0 hz0 hz1 hell hiso hR hKc hxK) (ih _ hsub)
        (phiF_nonneg hlam0.le hz0 _) (Real.exp_pos _).le
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [phiF_empty, Finset.filter_empty, Finset.sum_empty, mul_zero, Real.exp_zero]

end Tree

/-! ### The forest statements -/

/-- **Theorem T3-1 (per-unit form), hard-core form (unconditional given `PerUnitRate`).** -/
theorem t31_hardcore (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {lam z ell : ℝ} (hlam0 : 0 < lam)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hR : PerUnitRate lam z ell) :
    (∑ S ∈ indepSets F, lam ^ (S \ B).card * (lam * z) ^ (S ∩ B).card) / partitionFn F lam ≤
      Real.exp (-(ell / actQ lam) * weightW F lam B) := by
  classical
  rw [lapSum_eq_Zw, partitionFn_eq_Zw]
  have hfilt : (Finset.univ : Finset (Fin F.n)).filter (· ∈ B) = B := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hW : weightW F lam B = ∑ b ∈ (Finset.univ : Finset (Fin F.n)).filter (· ∈ B),
      marg F.graph lam Finset.univ b := by
    rw [hfilt]
    unfold weightW
    exact Finset.sum_congr rfl (fun b _ => marginal_eq_marg F lam b)
  rw [hW]
  exact t31_set F.isForest (isIndepFinset_of_isIndepSet hB) hlam0 hz0 hz1 hell hiso hR Finset.univ

/-- **Theorem T3-1 (the per-unit form).**  For every forest `F`, every independent set `B`,
`λ > 0`, `z ∈ [0, 1]`, `0 ≤ ℓ ≤ log((1 + λ)/(1 + λ z))`: if `PerUnitRate λ z ℓ` (`ℓ ≤ R(λ, Y, z)`
for all `Y > 0`), then `E(1 − q + q z)^M ≤ exp(−ℓ m)` for `forestMixture F B λ`.  The two
identities are the Laplace identity and `q m = W`. -/
theorem t31_reduction (hLap : LaplaceIdentity) (hW : WeightIdentity) (F : FiniteForest)
    (B : Finset (Fin F.n)) (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {lam z ell : ℝ}
    (hlam0 : 0 < lam) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hR : PerUnitRate lam z ell) :
    (forestMixture F B lam).expect (fun M _ => (1 - actQ lam + actQ lam * z) ^ M) ≤
      Real.exp (-ell * (forestMixture F B lam).meanM) := by
  rw [hLap F B lam z hlam0 hB]
  have hmean : (forestMixture F B lam).meanM = weightW F lam B / actQ lam := by
    rw [← hW F lam B hlam0 hB]
    field_simp [(actQ_pos hlam0).ne']
  have h := t31_hardcore F B hB hlam0 hz0 hz1 hell hiso hR
  rw [hmean, show -ell * (weightW F lam B / actQ lam) = -(ell / actQ lam) * weightW F lam B by ring]
  exact h

end Erdos993Lean.Analytic.Tail
