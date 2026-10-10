module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceScalarBounds
public import Erdos993Lean.Analytic.Tail.PerUnit

/-!
Exact specialization of the generic unit expression at
tilt zero to current T2a eq32. No positivity of that expression is assumed under
a different name: `UnitNonnegative` below is its literal quantified condition.
The assigned values Pi(0)=0 and H(q)=0 are handled as separate cases.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Finset

@[simp] theorem q_eq_actQ (lam : ℝ) : q lam = actQ lam := rfl
@[simp] theorem b_eq_Lf (p : ℝ) : b p = Tail.Lf p := rfl
@[simp] theorem Y_eq_Tf (lam p : ℝ) : Y lam p = Tail.Tf lam p := rfl
@[simp] theorem w_eq_rK (lam : ℝ) : w lam = Tail.rK lam := rfl

theorem fallback_zero {lam : ℝ} (hlam : 0 < lam) : Tail.rFallback lam 0 = 1 := by
  have hlog : Real.log (1+lam) ≠ 0 := (Tail.log_one_add_pos hlam).ne'
  simp [Tail.rFallback, hlog]

/-- Exactly the `b(p) ≤ x` feasibility condition, including equality. -/
theorem feasible_iff {p x : ℝ} (hp1 : p < 1) :
    b p ≤ x ↔ p ≤ 1-Real.exp (-x) := by
  have he : Real.exp (-b p) = 1-p := Tail.exp_neg_Lf hp1
  constructor
  · intro h
    have hx := Real.exp_le_exp.mpr (show -x ≤ -b p by linarith)
    rw [he] at hx
    linarith
  · intro h
    have hx : Real.exp (-x) ≤ Real.exp (-b p) := by rw [he]; linarith
    have := Real.exp_le_exp.mp hx
    linarith

/-- The exact logarithmic zero-tilt gain, not a lower enclosure. -/
theorem zero_tilt_log_gain {lam : ℝ} (hlam : 0 < lam) (x y : ℝ) :
    -Real.log (Tail.pC lam (x+y)+(1-Tail.pC lam (x+y))*Real.exp (-x)) =
      x+f lam (x+y)-f lam y := by
  have hx : 0 < Real.exp (-x) := Real.exp_pos _
  have hy : 0 < 1+lam*Real.exp (-y) := by positivity
  have hxy : 0 < 1+lam*Real.exp (-(x+y)) := by positivity
  have hexp : Real.exp (-(x+y)) = Real.exp (-x)*Real.exp (-y) := by
    rw [show -(x+y) = -x + -y by ring, Real.exp_add]
  have hid : Tail.pC lam (x+y)+(1-Tail.pC lam (x+y))*Real.exp (-x) =
      Real.exp (-x)*(1+lam*Real.exp (-y))/(1+lam*Real.exp (-(x+y))) := by
    unfold Tail.pC
    field_simp [hxy.ne']
    rw [hexp]
    ring
  rw [hid, Real.log_div (mul_pos hx hy).ne' hxy.ne',
    Real.log_mul hx.ne' hy.ne', Real.log_exp]
  unfold f
  ring

/-- The printed minimum marginal uses the same generic `hmin`. -/
theorem one_sub_minimum_marginal {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    1-Tail.hmin lam (Tail.pC lam s) = (1+q lam*Real.exp (-s))⁻¹ := by
  rw [Tail.dmax_eq hlam]
  have h1 : 1+lam ≠ 0 := by positivity
  have h2 : 1+lam+lam*Real.exp (-s) ≠ 0 := by positivity
  have h3 : 1+q lam*Real.exp (-s) ≠ 0 := by
    have := q_pos hlam
    positivity
  unfold q at *
  field_simp [h1, h2, h3] <;> ring

theorem current_E_eq_T3c {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    E lam s = Tail.T3c lam (ellH lam) s := by
  unfold E Tail.T3c
  rw [one_sub_minimum_marginal hlam]
  change ellH lam/(q lam*(1+q lam*Real.exp (-s))) =
    ellH lam/q lam*(1+q lam*Real.exp (-s))⁻¹
  have hq : q lam ≠ 0 := (q_pos hlam).ne'
  have hden : 1+q lam*Real.exp (-s) ≠ 0 := by
    have := q_pos hlam
    positivity
  field_simp [hq, hden] <;> ring

theorem current_k_eq_kK (lam : ℝ) : a lam*w lam = Tail.kK lam (a lam) := rfl

/-- This equality treats p=q as a leaf, not as a limit of the open expression. -/
theorem current_child_potential {lam p : ℝ} (hlam : 0 < lam)
    (hp : 0 < p) (hpq : p ≤ q lam) :
    a lam*H lam p = a lam*Tail.Tf lam p +
      (if p < actQ lam then Tail.kK lam (a lam)*Tail.ThatPlus lam (Tail.Tf lam p)
       else 0) := by
  by_cases hleaf : p = q lam
  · subst p
    rw [H_leaf]
    simp [q_eq_actQ, Tail.Tf_actQ hlam]
  · have hlt : p < q lam := lt_of_le_of_ne hpq hleaf
    have hY := Y_positive hlam hp hlt
    rw [H_nonleaf hlt, if_pos (show p < actQ lam from hlt)]
    change a lam*(Y lam p+w lam*Bplus lam (Y lam p)) =
      a lam*Y lam p+(a lam*w lam)*Tail.ThatPlus lam (Y lam p)
    rw [← Bplus_eq_ThatPlus hlam hY]
    ring

/-- Pi(0)=0 is exactly the generic zero-child convention. -/
theorem current_Pi_potential {lam y : ℝ} (hlam : 0 < lam) (hy : 0 ≤ y) :
    a lam*Pi lam y = (a lam-Tail.kK lam (a lam))*y +
      (if 0 < y then Tail.kK lam (a lam)*Tail.ThatPlus lam y else 0) := by
  by_cases hy0 : y = 0
  · subst y
    simp
  · have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [Pi_positive_argument hyp, if_pos hyp, ← Bplus_eq_ThatPlus hlam hyp]
    change a lam*((1-w lam)*y+w lam*Bplus lam y) =
      (a lam-a lam*w lam)*y+(a lam*w lam)*Bplus lam y
    ring

theorem unit_expression_eq_generic {lam x y p : ℝ} (hlam : 0 < lam)
    (hy : 0 ≤ y) (hp : 0 < p) (hpq : p ≤ q lam) :
    unitExpression lam x y p = Tail.T3U lam 0 (a lam) (ellH lam) x y p := by
  have hb : b p ≠ 0 := (Tail.Lf_pos hp (hpq.trans_lt (q_lt_one hlam))).ne'
  have hc := current_child_potential hlam hp hpq
  have hPi := current_Pi_potential hlam hy
  unfold Tail.T3U Tail.T3A Tail.T3phi
  rw [fallback_zero hlam, one_mul, zero_tilt_log_gain hlam,
    Tail.Lf_pC hlam, ← hc, ← current_E_eq_T3c hlam]
  have hcombine (z : ℝ) :
      z+(a lam-Tail.kK lam (a lam))*y+
        (if 0 < y then Tail.kK lam (a lam)*Tail.ThatPlus lam y else 0) =
      z+a lam*Pi lam y := by
    rw [hPi]
    ring
  rw [hcombine (x+f lam (x+y)-f lam y)]
  change unitExpression lam x y p =
    x+f lam (x+y)-f lam y+a lam*Pi lam y-a lam*f lam (x+y)+
      x*((a lam*H lam p-a lam*w lam*b p-E lam (x+y)*p)/b p)
  unfold unitExpression K
  field_simp [hb] <;> ring

def UnitNonnegative (lam : ℝ) : Prop :=
  ∀ x y p : ℝ, UnitDomain lam x y p → 0 ≤ unitExpression lam x y p

theorem unit_nonnegative_iff {lam : ℝ} (hlam : 0 < lam) :
    UnitNonnegative lam ↔ Tail.T3UNonneg lam 0 (a lam) (ellH lam) := by
  constructor
  · intro h x y p hx hy hp hpq hpx
    have hp1 := hpq.trans_lt (q_lt_one hlam)
    rw [← unit_expression_eq_generic hlam hy hp hpq]
    exact h x y p ⟨hx, hy, hp, hpq, (feasible_iff hp1).2 hpx⟩
  · intro h x y p hd
    rw [unit_expression_eq_generic hlam hd.2.1 hd.2.2.1 hd.2.2.2.1]
    exact h x y p hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1
      ((feasible_iff (hd.2.2.2.1.trans_lt (q_lt_one hlam))).1 hd.2.2.2.2)

/-- Current eq34 for a nonempty family; the zero-sum exceptional Pi is not used. -/
theorem child_Bplus_bound {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    {lam : ℝ} (hlam : 0 < lam) (p : ι → ℝ)
    (hp : ∀ i ∈ I, 0 < p i) (hpq : ∀ i ∈ I, p i ≤ q lam) :
    Bplus lam (∑ i ∈ I, b (p i)) ≤ ∑ i ∈ I, Y lam (p i) := by
  have hs : 0 < ∑ i ∈ I, b (p i) :=
    Finset.sum_pos (fun i hi => Tail.Lf_pos (hp i hi)
      ((hpq i hi).trans_lt (q_lt_one hlam))) hI
  rw [Bplus_eq_ThatPlus hlam hs]
  exact Tail.lemmaC_ineq hI hlam hp hpq

noncomputable def Psi (lam p : ℝ) : ℝ := a lam*b p+a lam*w lam*Y lam p

/-- The literal current local-potential inequality, including the no-A-child case.
The nonempty union is the retained C-vertex-with-a-child condition. -/
theorem local_potential_step {ι : Type*} {lam : ℝ} (hd : ActivityDomain lam)
    (hU : UnitNonnegative lam) (I J : Finset ι) (p : ι → ℝ)
    (hpI : ∀ i ∈ I, 0 < p i) (hpIq : ∀ i ∈ I, p i ≤ q lam)
    (hpJ : ∀ j ∈ J, 0 < p j) (hpJq : ∀ j ∈ J, p j ≤ q lam)
    (hne : I.Nonempty ∨ J.Nonempty) {pr tau : ℝ}
    (hpr : pr = Tail.pC lam (∑ i ∈ I, b (p i)+∑ j ∈ J, b (p j)))
    (htau : 0 < tau)
    (hgain : tau ≤ pr+(1-pr)*Real.exp (-(∑ i ∈ I, b (p i)))) :
    Psi lam pr ≤
      (-Real.log tau-E lam (∑ i ∈ I, b (p i)+∑ j ∈ J, b (p j))*∑ i ∈ I, p i)+
        (∑ i ∈ I, a lam*H lam (p i))+(∑ j ∈ J, Psi lam (p j)) := by
  have hlam : 0 < lam := by linarith [hd.1]
  have ha : 0 ≤ a lam := by linarith [(a_bounds hd).1]
  have hg : tau ≤ pr+(1-pr)*Real.exp (-(Tail.rFallback lam 0*∑ i ∈ I, Tail.Lf (p i))) := by
    simpa only [fallback_zero hlam, one_mul, b_eq_Lf] using hgain
  have hs := Tail.unit_step hlam (by linarith [hd.2]) ha
    ((unit_nonnegative_iff hlam).1 hU) I J p hpI hpIq hpJ hpJq hne hpr htau hg
  have hchild : (∑ i ∈ I, a lam*H lam (p i)) =
      ∑ i ∈ I, (a lam*Tail.Tf lam (p i)+
        (if p i < actQ lam then Tail.kK lam (a lam)*Tail.ThatPlus lam (Tail.Tf lam (p i))
         else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact current_child_potential hlam (hpI i hi) (hpIq i hi)
  rw [hchild, current_E_eq_T3c hlam]
  exact hs

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_eq_actQ
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_eq_actQ
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.b_eq_Lf
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.b_eq_Lf
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Y_eq_Tf
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Y_eq_Tf
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_eq_rK
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_eq_rK
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.fallback_zero
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.fallback_zero
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.feasible_iff
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.feasible_iff
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.zero_tilt_log_gain
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.zero_tilt_log_gain
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.one_sub_minimum_marginal
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.one_sub_minimum_marginal
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_E_eq_T3c
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_E_eq_T3c
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_k_eq_kK
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_k_eq_kK
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_child_potential
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_child_potential
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_Pi_potential
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_Pi_potential
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_expression_eq_generic
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_expression_eq_generic
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_nonnegative_iff
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_nonnegative_iff
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.child_Bplus_bound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.child_Bplus_bound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.local_potential_step
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.local_potential_step
