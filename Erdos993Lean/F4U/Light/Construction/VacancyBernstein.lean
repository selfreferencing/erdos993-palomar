module

public import Erdos993Lean.F4U.Light.Construction.CubicW
public import Erdos993Lean.F4U.Light.Soundness.BernsteinBasis
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section
open scoped BigOperators

def cubicValue (w : ℕ → ℝ) (rho : ℝ) : ℝ :=
  w 0 + w 1 * rho + w 2 * rho^2 + w 3 * rho^3

/-- Exact degree-three and degree-four Bernstein representations of the
retained cubic on its original vacancy interval. -/
theorem vacancy_bernstein_identity (w : ℕ → ℝ) (r0 r1 t : ℝ) {n : ℕ}
    (hn : n = 3 ∨ n = 4) :
    cubicValue w (r0 + (r1-r0)*t) =
      F4U.Light.scaledBernsteinSum n
        (fun s => (Nat.choose n s : ℝ) * vacancyControl w r0 r1 n s) t := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have hc42 : Nat.choose 4 2 = 6 := by decide
  rcases hn with rfl | rfl <;>
    norm_num [cubicValue, F4U.Light.scaledBernsteinSum, vacancyControl,
      vacancyChartCoefficient, Finset.sum_range_succ, h03, h13, h23, h33, hc42] <;> ring

theorem vacancy_cubic_pos (w : ℕ → ℝ) {r0 r1 rho : ℝ} {n : ℕ}
    (hn : n = 3 ∨ n = 4) (hlo : r0 ≤ rho) (hhi : rho ≤ r1)
    (hcontrols : ∀ s ≤ n, 0 < vacancyControl w r0 r1 n s) :
    0 < cubicValue w rho := by
  have hcoeff : ∀ s ≤ n,
      0 < (Nat.choose n s : ℝ) * vacancyControl w r0 r1 n s := by
    intro s hs
    exact mul_pos (by exact_mod_cast Nat.choose_pos hs) (hcontrols s hs)
  by_cases hwidth : r0 = r1
  · have hrho : rho = r0 := by linarith
    rw [hrho]
    have heq := vacancy_bernstein_identity w r0 r1 0 hn
    simp only [mul_zero, add_zero] at heq
    rw [heq]
    exact F4U.Light.scaledBernsteinSum_pos n _ hcoeff ⟨le_refl 0, by norm_num⟩
  · have hw : 0 < r1-r0 := sub_pos.mpr (lt_of_le_of_ne (hlo.trans hhi) hwidth)
    have ht0 : 0 ≤ (rho-r0)/(r1-r0) := div_nonneg (by linarith) hw.le
    have ht1 : (rho-r0)/(r1-r0) ≤ 1 := (div_le_one hw).mpr (by linarith)
    have heq := vacancy_bernstein_identity w r0 r1 ((rho-r0)/(r1-r0)) hn
    have harg : r0+(r1-r0)*((rho-r0)/(r1-r0)) = rho := by field_simp; ring
    rw [harg] at heq
    rw [heq]
    exact F4U.Light.scaledBernsteinSum_pos n _ hcoeff ⟨ht0, ht1⟩

theorem actual_child_control_pos (r : Row) (reg : Regime) (phase : SourcePhase)
    (endpoint : LogEndpoint) (control : ChildControl) {lam H rho : ℝ}
    (hphase : PhaseDomain phase lam H rho)
    (hcontrols : ∀ s ≤ vacancyControlDegree reg phase,
      0 < actualVacancyControl r reg phase endpoint control s lam H) :
    0 < childControlValue r reg phase control lam H rho (logEndpoint endpoint H) := by
  rw [child_control_cubic_representation]
  change 0 < cubicValue (childCubicCoefficient r reg phase control lam H (logEndpoint endpoint H)) rho
  apply vacancy_cubic_pos _ (n := vacancyControlDegree reg phase)
    (r0 := phaseLo phase lam H) (r1 := phaseHi phase lam H)
    (by cases reg <;> cases phase <;> simp [vacancyControlDegree])
  · cases phase <;> exact hphase.1
  · cases phase <;> exact hphase.2
  · exact hcontrols

#print axioms cubicValue
#print axioms vacancy_bernstein_identity
#print axioms vacancy_cubic_pos
#print axioms actual_child_control_pos

end
end F4Unified.LightConstruction
