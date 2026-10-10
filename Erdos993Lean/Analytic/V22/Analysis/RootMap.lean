module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

/-!
# Version 2.2 of the manuscript: the root map and the exact minorant minimum

Source: note Lemmas 3.3--3.6 (the minorant minimum, its bonus form,
the root map and `G`). Consumer: E3 activity-one estimates and E4/E5
minorant bounds. The final minimum theorem has exactly `P,B,rho > 0`
and arbitrary real `gamma,w`; equation-conditioned intermediate lemmas
are consumed by the actual everywhere-defined root map.




-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Filter
open scoped Topology

/-- The equation whose unique root lies in `(-1,infinity)`. -/
noncomputable def rootEquation (s : ℝ) : ℝ := s + Real.log (1 + s)

theorem rootEquation_strictMonoOn : StrictMonoOn rootEquation (Ioi (-1)) := by
  intro s hs t ht hst
  simp only [mem_Ioi] at hs ht
  dsimp [rootEquation]
  exact add_lt_add hst (Real.log_lt_log (by linarith [hs]) (by linarith))

/-- Existence is proved without using the logarithm at the boundary `s=-1`:
write `s=exp(x)-1` and apply IVT to `x+exp(x)-1`. -/
theorem exists_rootEquation (lambda : ℝ) :
    ∃ s : ℝ, -1 < s ∧ rootEquation s = lambda := by
  let f : ℝ → ℝ := fun x => x + Real.exp x - 1
  let a : ℝ := min lambda 0 - 1
  let b : ℝ := max lambda 0 + 1
  have ha0 : a ≤ 0 := by dsimp [a]; linarith [min_le_right lambda 0]
  have hal : a ≤ lambda := by dsimp [a]; linarith [min_le_left lambda 0]
  have hbl : lambda ≤ b - 1 := by dsimp [b]; linarith [le_max_left lambda 0]
  have hab : a ≤ b := by linarith
  have hea : Real.exp a ≤ 1 := by
    simpa using Real.exp_le_exp.mpr ha0
  have hfa : f a ≤ lambda := by dsimp [f]; linarith
  have hfb : lambda ≤ f b := by
    dsimp [f]
    linarith [Real.exp_pos b]
  have hfc : Continuous f := (continuous_id.add Real.continuous_exp).sub continuous_const
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab hfc.continuousOn ⟨hfa, hfb⟩
  refine ⟨Real.exp x - 1, by linarith [Real.exp_pos x], ?_⟩
  dsimp [rootEquation, f] at *
  rw [show 1 + (Real.exp x - 1) = Real.exp x by ring, Real.log_exp]
  linarith

/-- The paper's root map, defined on every real lambda. -/
noncomputable def rootMap (lambda : ℝ) : ℝ :=
  Classical.choose (exists_rootEquation lambda)

theorem rootMap_gt_neg_one (lambda : ℝ) : -1 < rootMap lambda :=
  (Classical.choose_spec (exists_rootEquation lambda)).1

theorem rootMap_equation (lambda : ℝ) : rootEquation (rootMap lambda) = lambda :=
  (Classical.choose_spec (exists_rootEquation lambda)).2

theorem rootMap_eq_of_equation {lambda s : ℝ} (hs : -1 < s)
    (heq : rootEquation s = lambda) : rootMap lambda = s := by
  apply rootEquation_strictMonoOn.injOn (rootMap_gt_neg_one lambda) hs
  rw [rootMap_equation, heq]

@[simp] theorem rootMap_zero : rootMap 0 = 0 := by
  apply rootMap_eq_of_equation (by norm_num)
  simp [rootEquation]

theorem rootMap_strictMono : StrictMono rootMap := by
  intro lambda mu hlm
  by_contra! h
  have heq : rootEquation (rootMap mu) ≤ rootEquation (rootMap lambda) :=
    rootEquation_strictMonoOn.monotoneOn (rootMap_gt_neg_one mu)
      (rootMap_gt_neg_one lambda) h
  rw [rootMap_equation, rootMap_equation] at heq
  linarith

theorem rootMap_monotone : Monotone rootMap := rootMap_strictMono.monotone

theorem rootMap_pos_iff (lambda : ℝ) : 0 < rootMap lambda ↔ 0 < lambda := by
  simpa using rootMap_strictMono.lt_iff_lt (a := 0) (b := lambda)

theorem rootMap_neg_iff (lambda : ℝ) : rootMap lambda < 0 ↔ lambda < 0 := by
  simpa using rootMap_strictMono.lt_iff_lt (a := lambda) (b := 0)

theorem rootMap_sub_le_sub {lambda mu : ℝ} (hlm : lambda ≤ mu) :
    rootMap mu - rootMap lambda ≤ mu - lambda := by
  have hsm : rootMap lambda ≤ rootMap mu := rootMap_monotone hlm
  have hlog := Real.log_le_log (by linarith [rootMap_gt_neg_one lambda] :
    0 < 1 + rootMap lambda) (by linarith : 1 + rootMap lambda ≤ 1 + rootMap mu)
  have hl := rootMap_equation lambda
  have hm := rootMap_equation mu
  dsimp [rootEquation] at hl hm
  linarith

theorem rootMap_lipschitz : LipschitzWith 1 rootMap := by
  apply LipschitzWith.mk_one
  intro lambda mu
  simp only [Real.dist_eq]
  rcases le_total lambda mu with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (rootMap_monotone h)),
      abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [rootMap_sub_le_sub h]
  · rw [abs_of_nonneg (sub_nonneg.mpr (rootMap_monotone h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact rootMap_sub_le_sub h

theorem rootMap_continuous : Continuous rootMap := rootMap_lipschitz.continuous

theorem rootMap_shift_le (lambda h : ℝ) (hh : 0 ≤ h) :
    rootMap (lambda + h) ≤ rootMap lambda + h := by
  linarith [rootMap_sub_le_sub (show lambda ≤ lambda + h by linarith)]

theorem rootMap_nonneg_le {lambda : ℝ} (hl : 0 ≤ lambda) :
    0 ≤ rootMap lambda ∧ rootMap lambda ≤ lambda := by
  have hs : 0 ≤ rootMap lambda := by simpa using rootMap_monotone hl
  have hlog : 0 ≤ Real.log (1 + rootMap lambda) := Real.log_nonneg (by linarith)
  have heq := rootMap_equation lambda
  dsimp [rootEquation] at heq
  exact ⟨hs, by linarith⟩

/-- Note Lemma 3.5(a): the root derivative, from its genuine inverse. -/
theorem hasDerivAt_rootMap (lambda : ℝ) :
    HasDerivAt rootMap ((1 + rootMap lambda) / (2 + rootMap lambda)) lambda := by
  have hs : 0 < 1 + rootMap lambda := by linarith [rootMap_gt_neg_one lambda]
  have ht : 0 < 2 + rootMap lambda := by linarith
  have hd : HasDerivAt rootEquation (1 + 1 / (1 + rootMap lambda))
      (rootMap lambda) := by
    exact (hasDerivAt_id _).add (((hasDerivAt_id _).const_add 1).log hs.ne')
  have hd0 : 1 + 1 / (1 + rootMap lambda) ≠ 0 := by positivity
  have hinv := HasDerivAt.of_local_left_inverse (rootMap_continuous.continuousAt)
    hd hd0 (Filter.Eventually.of_forall rootMap_equation)
  convert hinv using 1
  field_simp [hs.ne', ht.ne', hd0]
  ring

/-- The paper's `G(lambda)`, retaining the actual certified root. -/
noncomputable def rootG (lambda : ℝ) : ℝ :=
  rootMap lambda ^ 2 / (1 + rootMap lambda)

noncomputable def rootGPrime (lambda : ℝ) : ℝ :=
  rootMap lambda / (1 + rootMap lambda)

noncomputable def rootGSecond (lambda : ℝ) : ℝ :=
  1 / ((1 + rootMap lambda) * (2 + rootMap lambda))

@[simp] theorem rootG_zero : rootG 0 = 0 := by simp [rootG]
@[simp] theorem rootGPrime_zero : rootGPrime 0 = 0 := by simp [rootGPrime]

theorem rootG_nonneg (lambda : ℝ) : 0 ≤ rootG lambda := by
  unfold rootG
  exact div_nonneg (sq_nonneg _) (by linarith [rootMap_gt_neg_one lambda])

theorem rootGPrime_lt_one (lambda : ℝ) : rootGPrime lambda < 1 := by
  unfold rootGPrime
  apply (div_lt_one (by linarith [rootMap_gt_neg_one lambda] :
    0 < 1 + rootMap lambda)).2
  linarith

theorem hasDerivAt_rootG (lambda : ℝ) : HasDerivAt rootG (rootGPrime lambda) lambda := by
  have hs : 1 + rootMap lambda ≠ 0 := ne_of_gt (by linarith [rootMap_gt_neg_one lambda])
  have ht : 2 + rootMap lambda ≠ 0 := ne_of_gt (by linarith [rootMap_gt_neg_one lambda])
  convert ((hasDerivAt_rootMap lambda).pow 2).div
    ((hasDerivAt_rootMap lambda).const_add 1) hs using 1
  · funext z
    rfl
  · simp only [rootGPrime, Pi.pow_apply]
    norm_num
    field_simp [hs, ht]
    ring

theorem hasDerivAt_rootGPrime (lambda : ℝ) :
    HasDerivAt rootGPrime (rootGSecond lambda) lambda := by
  have hs : 1 + rootMap lambda ≠ 0 := ne_of_gt (by linarith [rootMap_gt_neg_one lambda])
  have ht : 2 + rootMap lambda ≠ 0 := ne_of_gt (by linarith [rootMap_gt_neg_one lambda])
  convert (hasDerivAt_rootMap lambda).div
    ((hasDerivAt_rootMap lambda).const_add 1) hs using 1
  · funext z
    rfl
  · dsimp [rootGSecond]
    field_simp [hs, ht]
    ring

theorem rootGSecond_pos (lambda : ℝ) : 0 < rootGSecond lambda := by
  unfold rootGSecond
  have hs : 0 < 1 + rootMap lambda := by linarith [rootMap_gt_neg_one lambda]
  have ht : 0 < 2 + rootMap lambda := by linarith
  positivity

/-- Note Lemmas 3.3/3.4's minorant, with arbitrary real bonus gamma. -/
noncomputable def rootMinorant (P B rho gamma w : ℝ) : ℝ :=
  P * (gamma - w) * Real.exp (-rho * w / 2) + B * w

noncomputable def rootMinorantArgmin (rho gamma s : ℝ) : ℝ := gamma - 2 * s / rho

private theorem exp_one_add_mono {s t : ℝ} (hs : -1 < s) (hst : s ≤ t) :
    Real.exp s * (1 + s) ≤ Real.exp t * (1 + t) := by
  exact mul_le_mul (Real.exp_le_exp.mpr hst) (by linarith)
    (by linarith) (le_of_lt (Real.exp_pos t))

private theorem rootMinorant_balance {P B rho gamma s : ℝ}
    (hP : 0 < P) (hB : 0 < B) (hs : -1 < s)
    (heq : rootEquation s = Real.log (B * Real.exp (rho * gamma / 2) / P)) :
    P * Real.exp (-rho * gamma / 2) * (Real.exp s * (1 + s)) = B := by
  have hspos : 0 < 1 + s := by linarith
  have harg : 0 < B * Real.exp (rho * gamma / 2) / P := by positivity
  have hexp : Real.exp s * (1 + s) = B * Real.exp (rho * gamma / 2) / P := by
    rw [← Real.exp_log hspos, ← Real.exp_add]
    simpa [rootEquation, Real.exp_log harg] using congrArg Real.exp heq
  have hcancel : Real.exp (-rho * gamma / 2) * Real.exp (rho * gamma / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show -rho * gamma / 2 + rho * gamma / 2 = 0 by ring, Real.exp_zero]
  rw [hexp]
  calc
    P * Real.exp (-rho * gamma / 2) * (B * Real.exp (rho * gamma / 2) / P) =
        B * (Real.exp (-rho * gamma / 2) * Real.exp (rho * gamma / 2)) := by
      field_simp [hP.ne']
    _ = B := by rw [hcancel, mul_one]

theorem hasDerivAt_rootMinorant (P B rho gamma w : ℝ) :
    HasDerivAt (rootMinorant P B rho gamma)
      (B - P * Real.exp (-rho * gamma / 2) *
        (Real.exp (rho * (gamma - w) / 2) * (1 + rho * (gamma - w) / 2))) w := by
  have heq : -rho * w / 2 = -rho * gamma / 2 + rho * (gamma - w) / 2 := by ring
  convert ((((hasDerivAt_id w).const_sub gamma).const_mul P).mul
    ((((hasDerivAt_id w).const_mul (-rho)).div_const 2).exp)).add
    ((hasDerivAt_id w).const_mul B) using 1
  · funext z
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    rfl
  · simp only [id_eq]
    rw [heq, Real.exp_add]
    ring

/-- Equation-conditioned monotonicity, consumed below by the actual root map. -/
theorem rootMinorant_monotonicity_of_root {P B rho gamma s : ℝ}
    (hP : 0 < P) (hB : 0 < B) (hrho : 0 < rho) (hs : -1 < s)
    (heq : rootEquation s = Real.log (B * Real.exp (rho * gamma / 2) / P)) :
    AntitoneOn (rootMinorant P B rho gamma) (Iic (rootMinorantArgmin rho gamma s)) ∧
    MonotoneOn (rootMinorant P B rho gamma) (Ici (rootMinorantArgmin rho gamma s)) := by
  let C := P * Real.exp (-rho * gamma / 2)
  let d : ℝ → ℝ := fun w =>
    B - C * (Real.exp (rho * (gamma - w) / 2) * (1 + rho * (gamma - w) / 2))
  have hC : 0 < C := by dsimp [C]; positivity
  have hbal : C * (Real.exp s * (1 + s)) = B :=
    rootMinorant_balance hP hB hs heq
  have hd : ∀ w, HasDerivAt (rootMinorant P B rho gamma) (d w) w :=
    hasDerivAt_rootMinorant P B rho gamma
  have hcont : Continuous (rootMinorant P B rho gamma) :=
    continuous_iff_continuousAt.mpr (fun w => (hd w).continuousAt)
  have hsigma : rho * (gamma - rootMinorantArgmin rho gamma s) / 2 = s := by
    dsimp [rootMinorantArgmin]
    field_simp [hrho.ne']
    ring
  constructor
  · apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic _) hcont.continuousOn
      (fun w _ => (hd w).hasDerivWithinAt)
    intro w hw
    have hw' : w ≤ rootMinorantArgmin rho gamma s := by
      simpa only [mem_Iic] using
        (interior_subset hw : w ∈ Iic (rootMinorantArgmin rho gamma s))
    have hsig : s ≤ rho * (gamma - w) / 2 := by
      nlinarith [mul_nonneg hrho.le (sub_nonneg.mpr hw')]
    have hm := mul_le_mul_of_nonneg_left (exp_one_add_mono hs hsig) hC.le
    dsimp [d]
    linarith
  · apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) hcont.continuousOn
      (fun w _ => (hd w).hasDerivWithinAt)
    intro w hw
    have hw' : rootMinorantArgmin rho gamma s ≤ w := by
      simpa only [mem_Ici] using
        (interior_subset hw : w ∈ Ici (rootMinorantArgmin rho gamma s))
    have hsig : rho * (gamma - w) / 2 ≤ s := by
      nlinarith [mul_nonneg hrho.le (sub_nonneg.mpr hw')]
    by_cases hlo : -1 < rho * (gamma - w) / 2
    · have hm := mul_le_mul_of_nonneg_left (exp_one_add_mono hlo hsig) hC.le
      dsimp [d]
      linarith
    · have hf : Real.exp (rho * (gamma - w) / 2) *
          (1 + rho * (gamma - w) / 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
      have hm := mul_nonpos_of_nonneg_of_nonpos hC.le hf
      dsimp [d]
      linarith

theorem rootMinorant_argmin_value_of_root {P B rho gamma s : ℝ}
    (hP : 0 < P) (hB : 0 < B) (hrho : 0 < rho) (hs : -1 < s)
    (heq : rootEquation s = Real.log (B * Real.exp (rho * gamma / 2) / P)) :
    rootMinorant P B rho gamma (rootMinorantArgmin rho gamma s) =
      B * (gamma - 2 / rho * (s ^ 2 / (1 + s))) := by
  have hbal := rootMinorant_balance hP hB hs heq
  have hbal' : P * Real.exp (-(gamma * rho / 2)) * (Real.exp s * (1 + s)) = B := by
    rw [show -(gamma * rho / 2) = -rho * gamma / 2 by ring]
    exact hbal
  have hsne : 1 + s ≠ 0 := ne_of_gt (by linarith)
  have hexp : -rho * rootMinorantArgmin rho gamma s / 2 = -rho * gamma / 2 + s := by
    dsimp [rootMinorantArgmin]
    field_simp [hrho.ne']
    ring
  unfold rootMinorant
  rw [hexp, Real.exp_add]
  dsimp [rootMinorantArgmin]
  field_simp [hrho.ne', hsne]
  linear_combination 2 * s * hbal'

theorem rootMinorant_lower_bound_of_root {P B rho gamma s : ℝ}
    (hP : 0 < P) (hB : 0 < B) (hrho : 0 < rho) (hs : -1 < s)
    (heq : rootEquation s = Real.log (B * Real.exp (rho * gamma / 2) / P))
    (w : ℝ) : B * (gamma - 2 / rho * (s ^ 2 / (1 + s))) ≤
      rootMinorant P B rho gamma w := by
  rw [← rootMinorant_argmin_value_of_root hP hB hrho hs heq]
  obtain ⟨ha, hm⟩ := rootMinorant_monotonicity_of_root hP hB hrho hs heq
  rcases le_total w (rootMinorantArgmin rho gamma s) with hw | hw
  · exact ha (by simpa only [mem_Iic] using hw) (by simp) hw
  · exact hm (by simp) (by simpa only [mem_Ici] using hw) hw

/-- Source-exact closed form with no equation assumption in the final statement. -/
theorem rootMinorant_lower_bound {P B rho : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hrho : 0 < rho) (gamma w : ℝ) :
    B * (gamma - 2 / rho * rootG (Real.log (B * Real.exp (rho * gamma / 2) / P))) ≤
      rootMinorant P B rho gamma w :=
  rootMinorant_lower_bound_of_root hP hB hrho (rootMap_gt_neg_one _)
    (rootMap_equation _) w

/-- The displayed argmin actually attains the closed-form bound. -/
theorem rootMinorant_argmin_value {P B rho : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hrho : 0 < rho) (gamma : ℝ) :
    rootMinorant P B rho gamma
      (rootMinorantArgmin rho gamma (rootMap (Real.log (B * Real.exp (rho * gamma / 2) / P)))) =
      B * (gamma - 2 / rho * rootG (Real.log (B * Real.exp (rho * gamma / 2) / P))) :=
  rootMinorant_argmin_value_of_root hP hB hrho (rootMap_gt_neg_one _)
    (rootMap_equation _)

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.rootEquation
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootEquation
#check Erdos993Lean.Analytic.V22.Analysis.rootEquation_strictMonoOn
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootEquation_strictMonoOn
#check Erdos993Lean.Analytic.V22.Analysis.exists_rootEquation
#print axioms Erdos993Lean.Analytic.V22.Analysis.exists_rootEquation
#check Erdos993Lean.Analytic.V22.Analysis.rootMap
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_gt_neg_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_gt_neg_one
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_equation
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_equation
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_eq_of_equation
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_eq_of_equation
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_zero
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_strictMono
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_strictMono
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_monotone
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_monotone
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_pos_iff
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_pos_iff
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_neg_iff
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_neg_iff
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_sub_le_sub
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_sub_le_sub
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_lipschitz
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_lipschitz
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_continuous
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_continuous
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_shift_le
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_shift_le
#check Erdos993Lean.Analytic.V22.Analysis.rootMap_nonneg_le
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMap_nonneg_le
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_rootMap
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_rootMap
#check Erdos993Lean.Analytic.V22.Analysis.rootG
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime
#check Erdos993Lean.Analytic.V22.Analysis.rootGSecond
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGSecond
#check Erdos993Lean.Analytic.V22.Analysis.rootG_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_zero
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_zero
#check Erdos993Lean.Analytic.V22.Analysis.rootG_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootG_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.rootGPrime_lt_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGPrime_lt_one
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_rootG
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_rootG
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_rootGPrime
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_rootGPrime
#check Erdos993Lean.Analytic.V22.Analysis.rootGSecond_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootGSecond_pos
#check Erdos993Lean.Analytic.V22.Analysis.rootMinorant
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMinorant
#check Erdos993Lean.Analytic.V22.Analysis.rootMinorantArgmin
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMinorantArgmin
#check Erdos993Lean.Analytic.V22.Analysis.exp_one_add_mono
#print axioms Erdos993Lean.Analytic.V22.Analysis.exp_one_add_mono
#check Erdos993Lean.Analytic.V22.Analysis.rootMinorant_balance
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMinorant_balance
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_rootMinorant
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_rootMinorant
#check Erdos993Lean.Analytic.V22.Analysis.rootMinorant_monotonicity_of_root
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMinorant_monotonicity_of_root
#check Erdos993Lean.Analytic.V22.Analysis.rootMinorant_argmin_value_of_root
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMinorant_argmin_value_of_root
#check Erdos993Lean.Analytic.V22.Analysis.rootMinorant_lower_bound_of_root
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMinorant_lower_bound_of_root
#check Erdos993Lean.Analytic.V22.Analysis.rootMinorant_lower_bound
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMinorant_lower_bound
#check Erdos993Lean.Analytic.V22.Analysis.rootMinorant_argmin_value
#print axioms Erdos993Lean.Analytic.V22.Analysis.rootMinorant_argmin_value
