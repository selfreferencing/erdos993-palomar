module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.Fallback

/-!
# The tail input T3, part 8: Lemma C (child messages)

Sources: T23 §3, Lemma C, and
the repaired potential proof,
"Child-message inequality, including its empty-set cases".

With `L(p) = −log(1 − p)`, `T(p) = log(λ(1 − p)/p)` and
`That(Y) = log λ − Y − log(1 − e^{−Y}) = log(λ/(e^Y − 1))` (`That_eq`):

* `lemmaC_exact` (**exact**): `∑_{u ∈ ch(v)} L(p_u) = T(p_v)` on a rooted tree;
* `lemmaC_ineq`: for a *nonempty* finite family with `0 < p_i ≤ q`,
  `∑ T(p_i) ≥ That_+(∑ L(p_i))`, `That_+ = max(That, 0)`; for the empty family the sum is `0`
  and no `That` term is assigned.  Proof (algebraic, replacing the Jensen argument):
  `λ^{d − 1} (1 − ∏(1 − p_i)) ≥ ∏ p_i` for `p_i ≤ λ` (`prod_le_pow_mul_one_sub_prod`), which is
  `∑ T(p_i) ≥ That(∑ L(p_i))` after taking logarithms, and `T(p) ≥ 0` for `p ≤ q`;
* `lemmaC_tree`: at a vertex with at least one child, `∑_w T(p_w) ≥ That_+(T(p_v))`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

/-! ### Scalar facts -/

section Scalar

variable {t : ℝ}

/-- `That(Y) = log(λ/(e^Y − 1))` (the form used here). -/
theorem That_eq (ht : 0 < t) {Y : ℝ} (hY : 0 < Y) :
    That t Y = Real.log (t / (Real.exp Y - 1)) := by
  have h1 : 0 < Real.exp Y - 1 := by linarith [Real.add_one_lt_exp hY.ne']
  have h2 : 0 < 1 - Real.exp (-Y) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hY)
    linarith
  have h3 : Real.exp Y - 1 = Real.exp Y * (1 - Real.exp (-Y)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold That
  rw [Real.log_div ht.ne' h1.ne', h3, Real.log_mul (Real.exp_pos Y).ne' h2.ne', Real.log_exp]
  ring

/-- `T(p) ≥ 0` for `0 < p ≤ q`. -/
theorem Tf_nonneg (ht : 0 < t) {p : ℝ} (hp0 : 0 < p) (hpq : p ≤ actQ t) : 0 ≤ Tf t p := by
  unfold Tf
  apply Real.log_nonneg
  rw [le_div_iff₀ hp0, one_mul]
  unfold actQ at hpq
  rw [le_div_iff₀ (by linarith)] at hpq
  nlinarith

/-- `T(q) = 0`. -/
theorem Tf_actQ (ht : 0 < t) : Tf t (actQ t) = 0 := by
  have e : t * (1 - actQ t) / actQ t = 1 := by
    rw [one_sub_actQ ht.le, div_eq_one_iff_eq (actQ_pos ht).ne']
    unfold actQ
    ring
  unfold Tf
  rw [e, Real.log_one]

/-- `T(p) = log λ + log(1 − p) − log p`. -/
theorem Tf_eq (ht : 0 < t) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tf t p = Real.log t - Lf p - Real.log p := by
  unfold Tf Lf
  rw [Real.log_div (mul_pos ht (by linarith)).ne' hp0.ne', Real.log_mul ht.ne' (by linarith)]
  ring

/-- **The product inequality** `λ ∏ p_i ≤ λ^d (1 − ∏(1 − p_i))` for a nonempty family of size `d`
with `0 ≤ p_i ≤ 1` and `p_i ≤ λ`. -/
theorem prod_le_pow_mul_one_sub_prod {ι : Type*} {I : Finset ι} (hI : I.Nonempty) {p : ι → ℝ}
    (ht : 0 ≤ t) (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) (hpt : ∀ i ∈ I, p i ≤ t) :
    t * ∏ i ∈ I, p i ≤ t ^ I.card * (1 - ∏ i ∈ I, (1 - p i)) := by
  induction hI using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [Finset.prod_singleton, Finset.card_singleton, pow_one]
    exact le_of_eq (by ring)
  | cons a I haI hI ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Finset.card_cons]
    have hpa0 := hp0 a (Finset.mem_cons_self a I)
    have hpa1 := hp1 a (Finset.mem_cons_self a I)
    have hpat := hpt a (Finset.mem_cons_self a I)
    have ih' := ih (fun i hi => hp0 i (Finset.mem_cons_of_mem hi))
      (fun i hi => hp1 i (Finset.mem_cons_of_mem hi)) (fun i hi => hpt i (Finset.mem_cons_of_mem hi))
    have hQp : 0 ≤ ∏ i ∈ I, p i := Finset.prod_nonneg (fun i hi => hp0 i (Finset.mem_cons_of_mem hi))
    have hP : 0 ≤ ∏ i ∈ I, (1 - p i) :=
      Finset.prod_nonneg (fun i hi => by linarith [hp1 i (Finset.mem_cons_of_mem hi)])
    have htk : 0 ≤ t ^ I.card := pow_nonneg ht _
    -- `λ^{d+1}(1 − (1 − p_a)P) = λ · λ^d (1 − P) + λ^{d+1} p_a P ≥ λ (λ Qp) ≥ λ p_a Qp`
    have e : t ^ (I.card + 1) * (1 - (1 - p a) * ∏ i ∈ I, (1 - p i)) =
        t * (t ^ I.card * (1 - ∏ i ∈ I, (1 - p i))) + t ^ (I.card + 1) * p a * ∏ i ∈ I, (1 - p i) := by
      ring
    rw [e]
    have h1 : t * (t * ∏ i ∈ I, p i) ≤ t * (t ^ I.card * (1 - ∏ i ∈ I, (1 - p i))) :=
      mul_le_mul_of_nonneg_left ih' ht
    have h2 : 0 ≤ t ^ (I.card + 1) * p a * ∏ i ∈ I, (1 - p i) :=
      mul_nonneg (mul_nonneg (pow_nonneg ht _) hpa0) hP
    have h3 : t * (p a * ∏ i ∈ I, p i) ≤ t * (t * ∏ i ∈ I, p i) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpat hQp) ht
    linarith

/-- **Lemma C, the inequality** (the child-message lemma): for a nonempty finite family with
`0 < p_i ≤ q`, `That_+(∑ L(p_i)) ≤ ∑ T(p_i)`. -/
theorem lemmaC_ineq {ι : Type*} {I : Finset ι} (hI : I.Nonempty) {p : ι → ℝ} (ht : 0 < t)
    (hp0 : ∀ i ∈ I, 0 < p i) (hpq : ∀ i ∈ I, p i ≤ actQ t) :
    ThatPlus t (∑ i ∈ I, Lf (p i)) ≤ ∑ i ∈ I, Tf t (p i) := by
  classical
  have hq1 := actQ_lt_one ht.le
  have hp1 : ∀ i ∈ I, p i < 1 := fun i hi => lt_of_le_of_lt (hpq i hi) hq1
  have hqt : actQ t ≤ t := by
    unfold actQ
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold ThatPlus
  apply max_le _ (Finset.sum_nonneg fun i hi => Tf_nonneg ht (hp0 i hi) (hpq i hi))
  -- `That(Y) ≤ ∑ T(p_i)`
  set Y := ∑ i ∈ I, Lf (p i) with hY
  set P := ∏ i ∈ I, (1 - p i) with hP
  set Qp := ∏ i ∈ I, p i with hQp
  have hPpos : 0 < P := Finset.prod_pos (fun i hi => by linarith [hp1 i hi])
  have hQppos : 0 < Qp := Finset.prod_pos hp0
  have hexpY : Real.exp (-Y) = P := by
    rw [hY, ← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_congr rfl (fun i hi => exp_neg_Lf (hp1 i hi))
  have hP1 : P < 1 := by
    obtain ⟨j, hj⟩ := hI
    rw [hP, ← Finset.mul_prod_erase _ _ hj]
    have h0 : 0 ≤ ∏ i ∈ I.erase j, (1 - p i) :=
      Finset.prod_nonneg (fun i hi => by linarith [hp1 i (Finset.mem_of_mem_erase hi)])
    have h1 : ∏ i ∈ I.erase j, (1 - p i) ≤ 1 :=
      Finset.prod_le_one₀ (fun i hi => by linarith [hp1 i (Finset.mem_of_mem_erase hi)])
        (fun i hi => by linarith [hp0 i (Finset.mem_of_mem_erase hi)])
    have h2 := hp0 j hj
    have h3 := hp1 j hj
    nlinarith [mul_nonneg (sub_nonneg.mpr h3.le) (sub_nonneg.mpr h1)]
  have hkey := prod_le_pow_mul_one_sub_prod hI ht.le (fun i hi => (hp0 i hi).le)
    (fun i hi => (hp1 i hi).le) (fun i hi => (hpq i hi).trans hqt)
  rw [← hP, ← hQp] at hkey
  -- rewrite both sides with logarithms
  have hsum : ∑ i ∈ I, Tf t (p i) = I.card * Real.log t - Y - Real.log Qp := by
    rw [Finset.sum_congr rfl (fun i hi => Tf_eq ht (hp0 i hi) (hp1 i hi)),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hQp,
      Real.log_prod (fun i hi => (hp0 i hi).ne')]
  have hThat : That t Y = Real.log t - Y - Real.log (1 - P) := by
    unfold That
    rw [hexpY]
  rw [hsum, hThat]
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul ht.ne' hQppos.ne', Real.log_mul (by positivity) (sub_pos.mpr hP1).ne',
    Real.log_pow] at hlog
  linarith

end Scalar

/-! ### On a rooted tree -/

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {t : ℝ}

/-- **Lemma C (exact)**: `∑_{w ∈ ch(r)} L(p_w) = T(p_r)`. -/
theorem lemmaC_exact (hG : G.IsAcyclic) (ht : 0 < t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    ∑ w ∈ nbrsIn G s r, Lf (rootProb G t (compIn G (s.erase r) w) w) = Tf t (rootProb G t s r) := by
  have hodds := rootProb_odds hG ht hs hr
  have hp0 := rootProb_pos (G := G) ht s r
  have hp1 := rootProb_lt_one (G := G) ht.le hr
  have hpos : ∀ w ∈ nbrsIn G s r, 0 < 1 - rootProb G t (compIn G (s.erase r) w) w :=
    fun w hw => by linarith [rootProb_lt_one (G := G) ht.le (self_mem_branch hw)]
  have hprod : 0 < ∏ w ∈ nbrsIn G s r, (1 - rootProb G t (compIn G (s.erase r) w) w) :=
    Finset.prod_pos hpos
  have e : t * (1 - rootProb G t s r) / rootProb G t s r =
      (∏ w ∈ nbrsIn G s r, (1 - rootProb G t (compIn G (s.erase r) w) w))⁻¹ := by
    have h1p : (1 - rootProb G t s r) ≠ 0 := by linarith
    rw [show t * (1 - rootProb G t s r) / rootProb G t s r =
        t / (rootProb G t s r / (1 - rootProb G t s r)) by field_simp, hodds,
      div_mul_cancel_left₀ ht.ne']
  unfold Tf
  rw [e, Real.log_inv, Real.log_prod (fun w hw => (hpos w hw).ne'), ← Finset.sum_neg_distrib]
  rfl

/-- **Lemma C at a vertex with a child**: `That_+(T(p_r)) ≤ ∑_w T(p_w)`. -/
theorem lemmaC_tree (hG : G.IsAcyclic) (ht : 0 < t) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) (hne : (nbrsIn G s r).Nonempty) :
    ThatPlus t (Tf t (rootProb G t s r)) ≤
      ∑ w ∈ nbrsIn G s r, Tf t (rootProb G t (compIn G (s.erase r) w) w) := by
  rw [← lemmaC_exact hG ht hs hr]
  exact lemmaC_ineq hne ht (fun w _ => rootProb_pos ht _ _)
    (fun w hw => rootProb_le_actQ ht.le (self_mem_branch hw))

end Erdos993Lean.Analytic.Tail
