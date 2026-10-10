module

public import F4Heavy.Contract
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Exact integral representation of the frozen `childH`, including u=0.
The integrand is the literal real power (1-u)^t from the manuscript. -/

@[expose] public section

namespace F4Unified.LightConstruction

 theorem childH_eq_integral {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    F4Unified.childH u = ∫ t : ℝ in (0 : ℝ)..1, (1-u)^t := by
  by_cases hu : u = 0
  · subst u
    simp [F4Unified.childH]
  · have hbase : 0 < 1-u := by linarith
    have hbase_ne : 1-u ≠ 1 := by
      intro hz
      apply hu
      linarith
    have hlog : Real.log (1-u) ≠ 0 := by
      intro hz
      have hexp := congrArg Real.exp hz
      rw [Real.exp_log hbase, Real.exp_zero] at hexp
      exact hbase_ne hexp
    have hint : (∫ t : ℝ in (0 : ℝ)..1, (1-u)^t) =
        (Real.log (1-u))⁻¹ * ((1-u)-1) := by
      simp_rw [Real.rpow_def_of_pos hbase]
      rw [intervalIntegral.integral_comp_mul_left Real.exp hlog]
      simp [Real.exp_log hbase, integral_exp]
    rw [hint]
    simp only [F4Unified.childH, F4Unified.phi, if_neg hu]
    field_simp
    <;> ring

#print axioms childH_eq_integral

end F4Unified.LightConstruction
