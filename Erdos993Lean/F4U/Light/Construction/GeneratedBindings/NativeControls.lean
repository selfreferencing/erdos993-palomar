module
public import Erdos993Lean.F4U.Light.Construction.CubicW
@[expose] public section
set_option linter.unusedSimpArgs false
namespace F4Unified.LightConstruction.GeneratedBindings.NativeControls
noncomputable section
def power0 (w : ℕ → ℝ) (a : ℝ) : ℝ := w 0 + w 1*a + w 2*a^2 + w 3*a^3
def power1 (w : ℕ → ℝ) (a : ℝ) : ℝ := w 1 + 2*w 2*a + 3*w 3*a^2
def power2 (w : ℕ → ℝ) (a : ℝ) : ℝ := w 2 + 3*w 3*a
theorem vacancyControl_3_0 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 3 0 = power0 w a := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_3_0
theorem vacancyControl_3_1 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 3 1 = power0 w a + (b-a)/3*power1 w a := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_3_1
theorem vacancyControl_3_2 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 3 2 = power0 w a + 2*(b-a)/3*power1 w a + (b-a)^2/3*power2 w a := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_3_2
theorem vacancyControl_3_3 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 3 3 = power0 w a + (b-a)*power1 w a + (b-a)^2*power2 w a + (b-a)^3*w 3 := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_3_3
theorem vacancyControl_4_0 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 4 0 = power0 w a := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_4_0
theorem vacancyControl_4_1 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 4 1 = power0 w a + (b-a)/4*power1 w a := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_4_1
theorem vacancyControl_4_2 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 4 2 = power0 w a + (b-a)/2*power1 w a + (b-a)^2/6*power2 w a := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_4_2
theorem vacancyControl_4_3 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 4 3 = power0 w a + 3*(b-a)/4*power1 w a + (b-a)^2/2*power2 w a + (b-a)^3/4*w 3 := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_4_3
theorem vacancyControl_4_4 (w : ℕ → ℝ) (a b : ℝ) :
    vacancyControl w a b 4 4 = power0 w a + (b-a)*power1 w a + (b-a)^2*power2 w a + (b-a)^3*w 3 := by
  have h03 : Finset.Icc (0 : ℕ) 3 = {0,1,2,3} := by decide
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h23 : Finset.Icc (2 : ℕ) 3 = {2,3} := by decide
  have h33 : Finset.Icc (3 : ℕ) 3 = {3} := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [vacancyControl,vacancyChartCoefficient,power0,power1,power2,
    Finset.sum_range_succ,h03,h13,h23,h33,h42] <;> ring
#print axioms vacancyControl_4_4
end
end F4Unified.LightConstruction.GeneratedBindings.NativeControls
