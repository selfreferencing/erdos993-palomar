module

public import Erdos993Lean.Analytic.V22.Functions
public import Erdos993Lean.Analytic.V22.Analysis.RootGTaylor
public import Erdos993Lean.Analytic.V22.Analysis.Kernel

/-!
# Exact bridge from the shared note definitions to the certified root map

The shared definition totalizes the root by zero when its equation has no
solution. Existence on every real argument and uniqueness on `(-1,infinity)`
show that this fallback is never used. All bridges below preserve the shared
definitions verbatim, including every real argument and integer fiber index.

Source: note Lemma 3.5 and Section 2.2. Consumer: the shared analytic
statements and their fiber bounds. This is an exact analytic adapter, with no
claim about a historical forest process.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

/-- The shared fallback branch is unreachable, for every real argument. -/
theorem shared_rootMap_eq (lambda : ℝ) :
    Erdos993Lean.Analytic.V22.rootMap lambda = rootMap lambda := by
  classical
  have hex : ∃ s : ℝ, -1 < s ∧ s + Real.log (1 + s) = lambda := by
    simpa only [rootEquation] using exists_rootEquation lambda
  unfold Erdos993Lean.Analytic.V22.rootMap
  rw [dif_pos hex]
  exact (rootMap_eq_of_equation (Classical.choose_spec hex).1
    (Classical.choose_spec hex).2).symm

theorem shared_rootMap_function_eq :
    Erdos993Lean.Analytic.V22.rootMap = rootMap := by
  funext lambda
  exact shared_rootMap_eq lambda

theorem shared_G_eq (lambda : ℝ) : Erdos993Lean.Analytic.V22.G lambda = rootG lambda := by
  simp only [Erdos993Lean.Analytic.V22.G, rootG, shared_rootMap_eq]

theorem shared_G1_eq (lambda : ℝ) :
    Erdos993Lean.Analytic.V22.G1 lambda = rootGPrime lambda := by
  simp only [Erdos993Lean.Analytic.V22.G1, rootGPrime, shared_rootMap_eq]

theorem shared_G2_eq (lambda : ℝ) :
    Erdos993Lean.Analytic.V22.G2 lambda = rootGSecond lambda := by
  simp only [Erdos993Lean.Analytic.V22.G2, rootGSecond, shared_rootMap_eq]

theorem shared_G_function_eq : Erdos993Lean.Analytic.V22.G = rootG := by
  funext lambda
  exact shared_G_eq lambda

theorem shared_G1_function_eq : Erdos993Lean.Analytic.V22.G1 = rootGPrime := by
  funext lambda
  exact shared_G1_eq lambda

theorem shared_G2_function_eq : Erdos993Lean.Analytic.V22.G2 = rootGSecond := by
  funext lambda
  exact shared_G2_eq lambda

theorem shared_rootMap_gt_neg_one (lambda : ℝ) :
    -1 < Erdos993Lean.Analytic.V22.rootMap lambda := by
  rw [shared_rootMap_eq]
  exact rootMap_gt_neg_one lambda

theorem shared_rootMap_equation (lambda : ℝ) :
    Erdos993Lean.Analytic.V22.rootMap lambda +
      Real.log (1 + Erdos993Lean.Analytic.V22.rootMap lambda) = lambda := by
  simpa only [shared_rootMap_eq, rootEquation] using rootMap_equation lambda

@[simp] theorem shared_rootMap_zero : Erdos993Lean.Analytic.V22.rootMap 0 = 0 := by
  rw [shared_rootMap_eq, rootMap_zero]

theorem shared_rootMap_strictMono : StrictMono Erdos993Lean.Analytic.V22.rootMap := by
  rw [shared_rootMap_function_eq]
  exact rootMap_strictMono

theorem shared_rootMap_monotone : Monotone Erdos993Lean.Analytic.V22.rootMap :=
  shared_rootMap_strictMono.monotone

theorem shared_rootMap_lipschitz : LipschitzWith 1 Erdos993Lean.Analytic.V22.rootMap := by
  rw [shared_rootMap_function_eq]
  exact rootMap_lipschitz

theorem shared_rootMap_continuous : Continuous Erdos993Lean.Analytic.V22.rootMap :=
  shared_rootMap_lipschitz.continuous

theorem shared_hasDerivAt_rootMap (lambda : ℝ) :
    HasDerivAt Erdos993Lean.Analytic.V22.rootMap
      ((1 + Erdos993Lean.Analytic.V22.rootMap lambda) /
        (2 + Erdos993Lean.Analytic.V22.rootMap lambda)) lambda := by
  simpa only [shared_rootMap_function_eq] using hasDerivAt_rootMap lambda

theorem shared_hasDerivAt_G (lambda : ℝ) :
    HasDerivAt Erdos993Lean.Analytic.V22.G (Erdos993Lean.Analytic.V22.G1 lambda) lambda := by
  simpa only [shared_G_function_eq, shared_G1_function_eq] using hasDerivAt_rootG lambda

theorem shared_hasDerivAt_G1 (lambda : ℝ) :
    HasDerivAt Erdos993Lean.Analytic.V22.G1 (Erdos993Lean.Analytic.V22.G2 lambda) lambda := by
  simpa only [shared_G1_function_eq, shared_G2_function_eq] using hasDerivAt_rootGPrime lambda

theorem shared_G_deriv_eq : deriv Erdos993Lean.Analytic.V22.G = Erdos993Lean.Analytic.V22.G1 := by
  rw [shared_G_function_eq, shared_G1_function_eq]
  exact rootG_deriv_eq

theorem shared_G1_deriv_eq : deriv Erdos993Lean.Analytic.V22.G1 = Erdos993Lean.Analytic.V22.G2 := by
  rw [shared_G1_function_eq, shared_G2_function_eq]
  exact rootGPrime_deriv_eq

theorem shared_G_contDiff_two : ContDiff ℝ 2 Erdos993Lean.Analytic.V22.G := by
  rw [shared_G_function_eq]
  exact rootG_contDiff_two

theorem shared_G1_contDiff_one : ContDiff ℝ 1 Erdos993Lean.Analytic.V22.G1 := by
  rw [shared_G1_function_eq]
  exact rootGPrime_contDiff_one

theorem shared_G2_continuous : Continuous Erdos993Lean.Analytic.V22.G2 := by
  rw [shared_G2_function_eq]
  exact rootGSecond_continuous

@[simp] theorem shared_G_zero : Erdos993Lean.Analytic.V22.G 0 = 0 := by
  rw [shared_G_eq, rootG_zero]

@[simp] theorem shared_G1_zero : Erdos993Lean.Analytic.V22.G1 0 = 0 := by
  rw [shared_G1_eq, rootGPrime_zero]

@[simp] theorem shared_G2_zero : Erdos993Lean.Analytic.V22.G2 0 = (1 / 2 : ℝ) := by
  rw [shared_G2_eq, rootGSecond_zero]

theorem shared_G_nonneg (lambda : ℝ) : 0 ≤ Erdos993Lean.Analytic.V22.G lambda := by
  rw [shared_G_eq]
  exact rootG_nonneg lambda

theorem shared_G1_lt_one (lambda : ℝ) : Erdos993Lean.Analytic.V22.G1 lambda < 1 := by
  rw [shared_G1_eq]
  exact rootGPrime_lt_one lambda

theorem shared_G2_pos (lambda : ℝ) : 0 < Erdos993Lean.Analytic.V22.G2 lambda := by
  rw [shared_G2_eq]
  exact rootGSecond_pos lambda

theorem shared_G1_strictMono : StrictMono Erdos993Lean.Analytic.V22.G1 := by
  rw [shared_G1_function_eq]
  exact rootGPrime_strictMono

theorem shared_G1_monotone : Monotone Erdos993Lean.Analytic.V22.G1 :=
  shared_G1_strictMono.monotone

theorem shared_G2_strictAnti : StrictAnti Erdos993Lean.Analytic.V22.G2 := by
  rw [shared_G2_function_eq]
  exact rootGSecond_strictAnti

theorem shared_G2_antitone : Antitone Erdos993Lean.Analytic.V22.G2 :=
  shared_G2_strictAnti.antitone

theorem shared_G_convex : ConvexOn ℝ univ Erdos993Lean.Analytic.V22.G := by
  rw [shared_G_function_eq]
  exact rootG_convex

theorem shared_G_strictConvex : StrictConvexOn ℝ univ Erdos993Lean.Analytic.V22.G := by
  rw [shared_G_function_eq]
  exact rootG_strictConvex

theorem shared_G_antitoneOn_nonpos : AntitoneOn Erdos993Lean.Analytic.V22.G (Iic 0) := by
  rw [shared_G_function_eq]
  exact rootG_antitoneOn_nonpos

theorem shared_G_monotoneOn_nonneg : MonotoneOn Erdos993Lean.Analytic.V22.G (Ici 0) := by
  rw [shared_G_function_eq]
  exact rootG_monotoneOn_nonneg

/-- Note Lemma 3.5(c), in precisely the shared functions used by the finite checks. -/
theorem shared_G_taylor_shift_upper (lambda h : ℝ) (hh : 0 ≤ h) :
    Erdos993Lean.Analytic.V22.G (lambda + h) ≤ Erdos993Lean.Analytic.V22.G lambda +
      h * Erdos993Lean.Analytic.V22.G1 lambda + h ^ 2 / 2 * Erdos993Lean.Analytic.V22.G2 lambda := by
  simpa only [shared_G_eq, shared_G1_eq, shared_G2_eq] using rootG_taylor_shift_upper lambda h hh

theorem shared_G1_shift_upper (lambda h : ℝ) (hh : 0 ≤ h) :
    Erdos993Lean.Analytic.V22.G1 (lambda + h) ≤ Erdos993Lean.Analytic.V22.G1 lambda +
      h * Erdos993Lean.Analytic.V22.G2 lambda := by
  simpa only [shared_G1_eq, shared_G2_eq] using rootGPrime_shift_upper lambda h hh

theorem shared_gaussianAmplitude_eq : Erdos993Lean.Analytic.V22.gaussianAmplitude = gaussianA := rfl

theorem shared_weightL_eq (q : ℝ) : Erdos993Lean.Analytic.V22.weightL q = weightL q := rfl

theorem shared_weightR_eq (q : ℝ) : Erdos993Lean.Analytic.V22.weightR q = weightR q := rfl

/-- Exact normalization and index bridge; no positivity or support premise is needed. -/
theorem shared_fiberFunction_eq (q mu : ℝ) (M : ℕ) (j : ℤ) :
    Erdos993Lean.Analytic.V22.fiberFunction q mu M j = fiber q mu M j := rfl

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_function_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_function_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_G2_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G2_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_function_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_function_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_function_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_function_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_G2_function_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G2_function_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_gt_neg_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_gt_neg_one
#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_equation
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_equation
#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_zero
#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_strictMono
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_strictMono
#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_monotone
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_monotone
#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_lipschitz
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_lipschitz
#check Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_continuous
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_rootMap_continuous
#check Erdos993Lean.Analytic.V22.Analysis.shared_hasDerivAt_rootMap
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_hasDerivAt_rootMap
#check Erdos993Lean.Analytic.V22.Analysis.shared_hasDerivAt_G
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_hasDerivAt_G
#check Erdos993Lean.Analytic.V22.Analysis.shared_hasDerivAt_G1
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_hasDerivAt_G1
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_deriv_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_deriv_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_deriv_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_deriv_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_contDiff_two
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_contDiff_two
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_contDiff_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_contDiff_one
#check Erdos993Lean.Analytic.V22.Analysis.shared_G2_continuous
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G2_continuous
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_zero
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_zero
#check Erdos993Lean.Analytic.V22.Analysis.shared_G2_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G2_zero
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_lt_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_lt_one
#check Erdos993Lean.Analytic.V22.Analysis.shared_G2_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G2_pos
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_strictMono
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_strictMono
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_monotone
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_monotone
#check Erdos993Lean.Analytic.V22.Analysis.shared_G2_strictAnti
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G2_strictAnti
#check Erdos993Lean.Analytic.V22.Analysis.shared_G2_antitone
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G2_antitone
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_convex
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_convex
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_strictConvex
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_strictConvex
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_antitoneOn_nonpos
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_antitoneOn_nonpos
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_monotoneOn_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_monotoneOn_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.shared_G_taylor_shift_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G_taylor_shift_upper
#check Erdos993Lean.Analytic.V22.Analysis.shared_G1_shift_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_G1_shift_upper
#check Erdos993Lean.Analytic.V22.Analysis.shared_gaussianAmplitude_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_gaussianAmplitude_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_weightL_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_weightL_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_weightR_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_weightR_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_fiberFunction_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_fiberFunction_eq
