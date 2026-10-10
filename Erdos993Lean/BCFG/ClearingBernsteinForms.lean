module

public import Erdos993Lean.BCFG.DeterminantAlgebra

/-! Generic cubic formulas used before expanding the row-specific rational
functions. Keeping the coefficients arbitrary avoids repeating the finite
vacancy and Bernstein sums in every clearing identity. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem vacancyCoefficient_zero (c : ℕ → ℝ) (r : ℝ) :
    vacancyCoefficient c r 0 = c 0+r*c 1+r^2*c 2+r^3*c 3 := by
  norm_num [vacancyCoefficient, Finset.sum_range_succ] <;> ring

theorem vacancyCoefficient_one (c : ℕ → ℝ) (r : ℝ) :
    vacancyCoefficient c r 1 = (1-r)*(c 1+2*r*c 2+3*r^2*c 3) := by
  simp only [vacancyCoefficient, pow_one]
  congr 1
  norm_num [Finset.sum_range_succ] <;> ring

theorem vacancyCoefficient_two (c : ℕ → ℝ) (r : ℝ) :
    vacancyCoefficient c r 2 = (1-r)^2*(c 2+3*r*c 3) := by
  unfold vacancyCoefficient
  congr 1
  norm_num [Finset.sum_range_succ] <;> ring

theorem vacancyCoefficient_three (c : ℕ → ℝ) (r : ℝ) :
    vacancyCoefficient c r 3 = (1-r)^3*c 3 := by
  norm_num [vacancyCoefficient, Finset.sum_range_succ]

theorem bernstein_vacancy_H0 (c : ℕ → ℝ) (r : ℝ) :
    bernsteinCoefficient (vacancyCoefficient c r) 0 =
      c 0+r*c 1+r^2*c 2+r^3*c 3 := by
  norm_num [bernsteinCoefficient, Finset.sum_range_succ,
    vacancyCoefficient_zero]

theorem bernstein_vacancy_H3 (c : ℕ → ℝ) (r : ℝ) :
    bernsteinCoefficient (vacancyCoefficient c r) 3 =
      c 0+c 1+c 2+c 3 := by
  norm_num [bernsteinCoefficient, Finset.sum_range_succ,
    vacancyCoefficient_zero, vacancyCoefficient_one,
    vacancyCoefficient_two, vacancyCoefficient_three] <;> ring

theorem bernstein_vacancy_H1 (c : ℕ → ℝ) (r : ℝ) :
    bernsteinCoefficient (vacancyCoefficient c r) 1+
      2/3*bernsteinCoefficient (vacancyCoefficient c r) 0 =
      (5*c 0+(1+4*r)*c 1+(2*r+3*r^2)*c 2+(3*r^2+2*r^3)*c 3)/3 := by
  norm_num [bernsteinCoefficient, Finset.sum_range_succ,
    vacancyCoefficient_zero, vacancyCoefficient_one] <;> ring

theorem bernstein_vacancy_H2 (c : ℕ → ℝ) (r : ℝ) :
    bernsteinCoefficient (vacancyCoefficient c r) 2-
      1/3*bernsteinCoefficient (vacancyCoefficient c r) 0 =
      (2*c 0+2*c 1+(1+2*r-r^2)*c 2+(3*r-r^3)*c 3)/3 := by
  norm_num [bernsteinCoefficient, Finset.sum_range_succ,
    vacancyCoefficient_zero, vacancyCoefficient_one,
    vacancyCoefficient_two] <;> ring

theorem lightJ_vacancy (c : ℕ → ℝ) (r u : ℝ) :
    lightJ (vacancyCoefficient c r) u =
      (1-r)^2*(c 2+3*r*c 3)+(2*u+1)*(1-r)^3*c 3 := by
  rw [lightJ, vacancyCoefficient_two, vacancyCoefficient_three]
  ring

theorem lightC0_vacancy (c : ℕ → ℝ) (r u : ℝ) :
    lightC0 (vacancyCoefficient c r) u =
      c 0+r*c 1+r^2*c 2+r^3*c 3-
        u^2*((1-r)^2*(c 2+3*r*c 3)+2*u*(1-r)^3*c 3) := by
  rw [lightC0, vacancyCoefficient_zero, vacancyCoefficient_two,
    vacancyCoefficient_three]
  ring

theorem lightC1_vacancy (c : ℕ → ℝ) (r u : ℝ) :
    lightC1 (vacancyCoefficient c r) u =
      c 0+c 1+c 2+c 3-
        (1-u)^2*((1-r)^2*(c 2+3*r*c 3)+(2*u+1)*(1-r)^3*c 3) := by
  rw [lightC1, vacancyCoefficient_zero, vacancyCoefficient_one,
    vacancyCoefficient_two, vacancyCoefficient_three, lightJ_vacancy]
  ring

end Erdos993Lean.BCFG.Analytic
