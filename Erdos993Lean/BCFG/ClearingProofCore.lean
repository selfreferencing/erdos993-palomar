module

public import Erdos993Lean.BCFG.IntegerEvaluation
public import Erdos993Lean.BCFG.ClearingDenominators
public import Erdos993Lean.BCFG.ChartGeometry
public import Erdos993Lean.BCFG.ClearingBernsteinForms
public import Erdos993Lean.BCFG.ClearingEnvelopeForms
public import Erdos993Lean.BCFG.ClearingLightForms
public import Erdos993Lean.BCFG.ClearingMonomialCancellation
public meta import Erdos993Lean.BCFG.ClearingRingNormalizer

/-! Generic proof infrastructure for Eq.(15), with no finite identity hypothesis
in the per-row results. The syntax below unfolds the literal analytic formulas
and original integer lists, then asks ordinary Lean tactics for a proof. It
performs no external polynomial arithmetic and grants no elaboration claim. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem heavy_clearing_facts {r : AnalyticRow} {lam v : ℝ}
    (h : HeavyDomain r lam v) :
    0 < lam ∧ 0 < v ∧ 0 < 1+lam ∧ 0 < 1+v ∧
      0 < 1+lam+lam*v^(heavyExponent r) ∧
      0 < (1+lam)^2+lam*v^(heavyExponent r) ∧
      0 < 1-((1-v)/(1+v))^2 := by
  have hl := activity_pos h.1
  have hv : 0 < v := lt_of_lt_of_le (by norm_num) h.2.1
  have hV : 0 < 1+v := by linarith
  have hz : 1-((1-v)/(1+v))^2 = 4*v/(1+v)^2 := by
    field_simp [hV.ne'] <;> ring
  refine ⟨hl, hv, by linarith, hV, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · rw [hz]
    positivity

theorem light_clearing_facts {r : AnalyticRow} {lam x : ℝ}
    (h : LightDomain r lam x) :
    0 < lam ∧ 0 < 1+lam ∧
      0 < 1+lam-lam*x ∧ 0 < 2+2*lam-lam*x ∧
      0 < (1+lam)^2-lam^2*x ∧
      0 < (1+lam)*(1+2*lam)-lam^2*x ∧
      0 < lightOmega lam x ∧ 0 < 1-(lightZ lam x)^2 := by
  have hl := activity_pos h.1
  obtain ⟨hB,hC,hA,hE⟩ := light_factors_pos hl h.2.2
  have hw := lightOmega_pos hl h.2.1 h.2.2
  have hz := lightZ_bounds hl h.2.1 h.2.2
  refine ⟨hl, by linarith, hB, hC, hA, hE, hw, ?_⟩
  nlinarith [mul_pos (sub_pos.mpr hz.2) (show 0 < 1+lightZ lam x by linarith [hz.1])]

theorem clearing_eq_of_cross {r : AnalyticRow} {f : DeterminantFunction}
    {lam y s P : ℝ} (h : FunctionDomain r f lam y)
    (hc : analyticFunction r f lam y * clearingDenominator r f lam y =
      s * clearingFactor f lam * P) :
    analyticFunction r f lam y =
      s * clearingFactor f lam * P / clearingDenominator r f lam y :=
  (eq_div_iff (clearingDenominator_pos h).ne').2 hc

/-- Canonical heavy factors remove nested occupation denominators before expansion. -/
theorem occupation_heavyOmega {r : AnalyticRow} {lam v : ℝ}
    (hL : 1+lam ≠ 0) :
    occupation lam (heavyOmega r lam v) = lam*v^(heavyExponent r)/heavyA r lam v := by
  unfold occupation heavyOmega heavyA
  field_simp [hL]

theorem rhoZero_heavyOmega {r : AnalyticRow} {lam v : ℝ}
    (hL : 1+lam ≠ 0) :
    rhoZero lam (heavyOmega r lam v) = heavyA r lam v/heavyE r lam v := by
  unfold rhoZero heavyOmega heavyA heavyE
  field_simp [hL]
  <;> ring

theorem dCoeff_heavyOmega {r : AnalyticRow} {lam v : ℝ}
    (hL : 1+lam ≠ 0) (hA : heavyA r lam v ≠ 0) :
    dCoeff lam (heavyOmega r lam v) = (1+lam)/heavyA r lam v := by
  rw [dCoeff, occupation_heavyOmega hL]
  unfold heavyA at *
  field_simp [hA]
  <;> ring

theorem rCoeff_heavyOmega {r : AnalyticRow} {lam v : ℝ}
    (hl : lam ≠ 0) (hv : v ≠ 0) (hL : 1+lam ≠ 0) :
    rCoeff r lam (heavyOmega r lam v) = kappa r*heavyA r lam v/v^(heavyExponent r) := by
  rw [rCoeff, occupation_heavyOmega hL, gamma]
  field_simp [hl, hv]

/-- Canonical light factors keep the closed leaf endpoint in the same formulas. -/
theorem occupation_lightOmega {lam x : ℝ} (hL : 1+lam ≠ 0) :
    occupation lam (lightOmega lam x) = lam*lightB lam x/lightA lam x := by
  unfold occupation lightOmega q lightB lightA
  field_simp [hL]
  <;> ring

theorem rhoZero_lightOmega {lam x : ℝ} (hL : 1+lam ≠ 0) :
    rhoZero lam (lightOmega lam x) = lightA lam x/lightE lam x := by
  unfold rhoZero lightOmega q lightA lightE
  field_simp [hL]
  <;> ring

theorem dCoeff_lightOmega {lam x : ℝ}
    (hL : 1+lam ≠ 0) (hA : lightA lam x ≠ 0) :
    dCoeff lam (lightOmega lam x) = (1+lam)/lightA lam x := by
  rw [dCoeff, occupation_lightOmega hL]
  unfold lightA lightB at *
  field_simp [hA]
  <;> ring

theorem rCoeff_lightOmega {r : AnalyticRow} {lam x : ℝ}
    (hl : lam ≠ 0) (hL : 1+lam ≠ 0) :
    rCoeff r lam (lightOmega lam x) = kappa r*lightA lam x/lightB lam x := by
  rw [rCoeff, occupation_lightOmega hL, gamma]
  field_simp [hl]

theorem one_sub_rhoZero_heavyOmega {r : AnalyticRow} {lam v : ℝ}
    (hL : 1+lam ≠ 0) (hE : heavyE r lam v ≠ 0) :
    1-rhoZero lam (heavyOmega r lam v) = lam*(1+lam)/heavyE r lam v := by
  rw [rhoZero_heavyOmega hL]
  calc
    1-heavyA r lam v/heavyE r lam v =
        (heavyE r lam v-heavyA r lam v)/heavyE r lam v := by
      rw [sub_div, div_self hE]
    _ = lam*(1+lam)/heavyE r lam v := by
      congr 1
      unfold heavyE heavyA
      ring

theorem one_sub_rhoZero_lightOmega {lam x : ℝ}
    (hL : 1+lam ≠ 0) (hE : lightE lam x ≠ 0) :
    1-rhoZero lam (lightOmega lam x) = lam*(1+lam)/lightE lam x := by
  rw [rhoZero_lightOmega hL]
  calc
    1-lightA lam x/lightE lam x = (lightE lam x-lightA lam x)/lightE lam x := by
      rw [sub_div, div_self hE]
    _ = lam*(1+lam)/lightE lam x := by
      congr 1
      unfold lightE lightA
      ring

/- A syntax abbreviation only. All array literals come from the supplied
   immutable pInt constant; s is its original clearingScale constant.
   `ring` must close the full resulting identity, rather than a sampled or
   truncated coefficient test. Every final theorem still has its own proof. -/
macro "bcfg_exact_clear " p:ident " scale " s:ident " order " l:ident y:ident cancel:("cancel")? : tactic => do
  let cancellation ← if cancel.isSome then
    `(tactic|
      (conv_lhs =>
        simp (disch := first | (apply ne_of_gt; assumption) | norm_num | positivity) only
          [Mathlib.Tactic.RingNF.nat_rawCast_0, Mathlib.Tactic.RingNF.nat_rawCast_1,
           Mathlib.Tactic.RingNF.nat_rawCast_2, Mathlib.Tactic.RingNF.int_rawCast_neg,
           Mathlib.Tactic.RingNF.nnrat_rawCast, Mathlib.Tactic.RingNF.rat_rawCast_neg,
           clearing_pow_inv_sq, clearing_pow_mul_inv_sq]
        bcfg_ring_nf [$l:ident, $y:ident]))
    else `(tactic|skip)
  `(tactic|
    (simp only [analyticFunction, heavyBernstein, heavyCoefficient, lightCoefficient]
     first
     | rw [bernstein_vacancy_H1]
     | rw [bernstein_vacancy_H2]
     | rw [bernstein_vacancy_H0]
     | rw [bernstein_vacancy_H3]
     | rw [lightJ_vacancy]
     | rw [lightC0_vacancy]
     | rw [lightC1_vacancy]
     try simp (disch :=
       (try dsimp only [heavyE, lightE, heavyExponent])
       first | assumption | (apply ne_of_gt; assumption) | positivity) only
       [one_sub_rhoZero_heavyOmega, one_sub_rhoZero_lightOmega]
     simp (disch :=
       (try dsimp only [heavyA, lightA, lightB, lightC, heavyExponent])
       first | assumption | (apply ne_of_gt; assumption) | positivity) only [heavyRawCoefficient, lightRawCoefficient,
       heavyK1, heavyK2, lightK1, lightK2, eCoeff,
       occupation_heavyOmega, rhoZero_heavyOmega, dCoeff_heavyOmega, rCoeff_heavyOmega,
       occupation_lightOmega, rhoZero_lightOmega, dCoeff_lightOmega, rCoeff_lightOmega,
       heavyUpper_closed_form, lightUpper_canonical,
       lightSourceA_canonical, lightSourceB_canonical]
     norm_num only [$s:ident,
      analyticFunction, heavyBernstein, bernsteinCoefficient, heavyCoefficient,
      heavyRawCoefficient, vacancyCoefficient, rawCoefficient,
      lightJ, lightC0, lightC1, lightCoefficient, lightRawCoefficient,
      heavyZ, heavyLower,
      heavyK1, heavyK2, lightOmega, lightZ, lightK1, lightK2,
      lightSourceA, lightSourceB, lightCenter, sourceA,
      clearingDenominator, clearingFactor, heavyA, heavyE, heavyB,
      lightA, lightB, lightC, lightE,
      cubicEnvelope, price, gamma, centerResponse,
      massLine, ellLower, ellUpper, activityCenter, q,
      rowLow, rowHigh, theta, alpha, beta, kappa, heavyExponent,
      massIntercept, massSlope, logCenterLower, logCenterUpper, epsilon,
      Finset.sum_range_succ] <;>
    (trace "clearing: analytic expansion complete"
     conv_lhs =>
       field_simp (disch := first | positivity |
         (apply ne_of_gt; nlinarith) | (apply ne_of_lt; nlinarith))
     trace "clearing: left denominators collected"
     conv_lhs =>
       bcfg_ring_nf [$l:ident, $y:ident]
     trace "clearing: left denominators normalized"
     $cancellation:tactic
     trace "clearing: monomial inverse squares cancelled"
     conv_rhs => norm_num only [integerBiValue, integerUniValue, $p:ident]
     trace "clearing: integer Horner normalized"
     conv_rhs =>
       bcfg_ring_nf [$l:ident, $y:ident]
     trace "clearing: right polynomial normalized"
     all_goals rfl)))

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavy_clearing_facts
#print axioms Erdos993Lean.BCFG.Analytic.heavy_clearing_facts
#check Erdos993Lean.BCFG.Analytic.light_clearing_facts
#print axioms Erdos993Lean.BCFG.Analytic.light_clearing_facts
#check Erdos993Lean.BCFG.Analytic.clearing_eq_of_cross
#print axioms Erdos993Lean.BCFG.Analytic.clearing_eq_of_cross
