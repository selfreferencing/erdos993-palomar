module

public import Erdos993Lean.Analytic.V213.SmallForestPatternData
public import Erdos993Lean.Analytic.V213.SmallForestPatternTransport

/-!
These are Real extensions of the exact nine
reviewed Rat quotient operands, with explicit cast bridges. The original
PatternData source is not edited. Universal signs, not finite sampling.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestPatterns

noncomputable def prod2R (j : ℝ) : ℝ := (j+1)*(j+2)
noncomputable def prod3R (j : ℝ) : ℝ := prod2R j*(j+3)
noncomputable def prod4R (j : ℝ) : ℝ := prod3R j*(j+4)
noncomputable def P4R (x : ℝ) : ℝ := 19*x^4+272*x^3+1307*x^2+2202*x+448
noncomputable def P3R (x : ℝ) : ℝ := 11*x^3+105*x^2+268*x+84

noncomputable def ratio1 (j : ℝ) : ℝ := 3*(j^2*(19*j-21)+24*j+4)/((j-6)*prod2R j)
noncomputable def ratio2 (j : ℝ) : ℝ := 3*j*(j^2*(19*j-36)+19*j+54)/((j-3)*prod3R j)
noncomputable def ratio3 (j : ℝ) : ℝ := 2*j*(j-2)*(13*j+11)/prod3R j
noncomputable def ratio4 (j : ℝ) : ℝ := 3*P4R (j-4)/prod4R j
noncomputable def ratio5 (j : ℝ) : ℝ := (4*(j-3)^2+15*(j-3)+5)/prod2R j
noncomputable def ratio6 (j : ℝ) : ℝ := P3R (j-4)/prod3R j
noncomputable def ratio7 (j : ℝ) : ℝ := (j-4)/(j+2)
noncomputable def ratio8 (j : ℝ) : ℝ := 2*(j-2)*(88*j^3+243*j^2+209*j+60)/(3*prod4R j)
noncomputable def ratio9 (j : ℝ) : ℝ := (13*(j-3)^2+65*(j-3)+42)/(2*(j+2)*(j+3))

theorem quotient1_cast (j : ℚ) : (quotient1 j : ℝ) = ratio1 (j : ℝ) := by
  simp [quotient1, ratio1, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem quotient2_cast (j : ℚ) : (quotient2 j : ℝ) = ratio2 (j : ℝ) := by
  simp [quotient2, ratio2, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem quotient3_cast (j : ℚ) : (quotient3 j : ℝ) = ratio3 (j : ℝ) := by
  simp [quotient3, ratio3, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem quotient4_cast (j : ℚ) : (quotient4 j : ℝ) = ratio4 (j : ℝ) := by
  simp [quotient4, ratio4, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem quotient5_cast (j : ℚ) : (quotient5 j : ℝ) = ratio5 (j : ℝ) := by
  simp [quotient5, ratio5, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem quotient6_cast (j : ℚ) : (quotient6 j : ℝ) = ratio6 (j : ℝ) := by
  simp [quotient6, ratio6, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem quotient7_cast (j : ℚ) : (quotient7 j : ℝ) = ratio7 (j : ℝ) := by
  simp [quotient7, ratio7, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem quotient8_cast (j : ℚ) : (quotient8 j : ℝ) = ratio8 (j : ℝ) := by
  simp [quotient8, ratio8, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem quotient9_cast (j : ℚ) : (quotient9 j : ℝ) = ratio9 (j : ℝ) := by
  simp [quotient9, ratio9, prod2, prod3, prod4, P3, P4,
    prod2R, prod3R, prod4R, P3R, P4R]

theorem ratio1_nonneg (j : ℝ) (hj : 7 ≤ j) : 0 ≤ ratio1 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  have hc : 0 ≤ 19*j-21 := by linarith
  have hd : 0 < j-6 := by linarith
  dsimp only [ratio1, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

theorem ratio2_nonneg (j : ℝ) (hj : 4 ≤ j) : 0 ≤ ratio2 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  have hc : 0 ≤ 19*j-36 := by linarith
  have hd : 0 < j-3 := by linarith
  dsimp only [ratio2, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

theorem ratio3_nonneg (j : ℝ) (hj : 2 ≤ j) : 0 ≤ ratio3 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  dsimp only [ratio3, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

theorem ratio4_nonneg (j : ℝ) (hj : 4 ≤ j) : 0 ≤ ratio4 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  have h4 : 0 ≤ j-4 := by linarith
  dsimp only [ratio4, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

theorem ratio5_nonneg (j : ℝ) (hj : 3 ≤ j) : 0 ≤ ratio5 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  have h3 : 0 ≤ j-3 := by linarith
  dsimp only [ratio5, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

theorem ratio6_nonneg (j : ℝ) (hj : 4 ≤ j) : 0 ≤ ratio6 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  have h4 : 0 ≤ j-4 := by linarith
  dsimp only [ratio6, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

theorem ratio7_nonneg (j : ℝ) (hj : 4 ≤ j) : 0 ≤ ratio7 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  have h4 : 0 ≤ j-4 := by linarith
  dsimp only [ratio7, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

theorem ratio8_nonneg (j : ℝ) (hj : 2 ≤ j) : 0 ≤ ratio8 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  dsimp only [ratio8, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

theorem ratio9_nonneg (j : ℝ) (hj : 3 ≤ j) : 0 ≤ ratio9 j := by
  have hj0 : 0 ≤ j := by linarith
  have h2 : 0 ≤ j-2 := by linarith
  have h3 : 0 ≤ j-3 := by linarith
  dsimp only [ratio9, prod2R, prod3R, prod4R, P3R, P4R]
  positivity

end Erdos993Lean.Analytic.V213.SmallForestPatterns

#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient1_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient1_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient2_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient2_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient3_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient3_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient4_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient4_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient5_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient5_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient6_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient6_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient7_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient7_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient8_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient8_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient9_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient9_cast
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio1_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio1_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio2_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio2_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio3_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio3_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio4_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio4_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio5_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio5_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio6_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio6_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio7_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio7_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio8_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio8_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio9_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.ratio9_nonneg
