module

public import Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.Integer

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

theorem lower_row_00 :
    (decide (0 < lower.getD 0 0) &&
      (List.range (m+1)).all (fun B => decide (lower.getD 0 0 ≤ 100*coeff 0 B))) = true := by
  exact integer_original_row 0 (by decide +kernel)

theorem lower_row_01 :
    (decide (0 < lower.getD 1 0) &&
      (List.range (m+1)).all (fun B => decide (lower.getD 1 0 ≤ 100*coeff 1 B))) = true := by
  exact integer_original_row 1 (by decide +kernel)

theorem lower_row_02 :
    (decide (0 < lower.getD 2 0) &&
      (List.range (m+1)).all (fun B => decide (lower.getD 2 0 ≤ 100*coeff 2 B))) = true := by
  exact integer_original_row 2 (by decide +kernel)

theorem lower_row_03 :
    (decide (0 < lower.getD 3 0) &&
      (List.range (m+1)).all (fun B => decide (lower.getD 3 0 ≤ 100*coeff 3 B))) = true := by
  exact integer_original_row 3 (by decide +kernel)

theorem lower_row_04 :
    (decide (0 < lower.getD 4 0) &&
      (List.range (m+1)).all (fun B => decide (lower.getD 4 0 ≤ 100*coeff 4 B))) = true := by
  exact integer_original_row 4 (by decide +kernel)

theorem lower_row_05 :
    (decide (0 < lower.getD 5 0) &&
      (List.range (m+1)).all (fun B => decide (lower.getD 5 0 ≤ 100*coeff 5 B))) = true := by
  exact integer_original_row 5 (by decide +kernel)

theorem lower_row_06 :
    (decide (0 < lower.getD 6 0) &&
      (List.range (m+1)).all (fun B => decide (lower.getD 6 0 ≤ 100*coeff 6 B))) = true := by
  exact integer_original_row 6 (by decide +kernel)

theorem lower_checked : lowerCheck n m coeff lower = true := by
  apply List.all_eq_true.mpr
  intro A hA
  have hAn : A ≤ 6 := by simpa [n] using Nat.le_of_lt_succ (List.mem_range.mp hA)
  interval_cases A
  · exact lower_row_00
  · exact lower_row_01
  · exact lower_row_02
  · exact lower_row_03
  · exact lower_row_04
  · exact lower_row_05
  · exact lower_row_06

end Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope

#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_00
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_00
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_01
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_01
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_02
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_02
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_03
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_03
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_04
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_04
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_05
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_05
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_06
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_row_06
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_checked
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower_checked
