module

public import Erdos993Lean.Analytic.V213.SmallForestPatternIdentities
public import Erdos993Lean.Analytic.V213.SmallForestSupporting

/-! Apply the actual supporting-line theorem to all
nine symbolic patterns. No finite-index catalogue, forest premise or numerical
replay is used. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestPatterns
open Erdos993Lean.Analytic.V213.SmallForest

theorem pattern1_supporting_line (n m : ℕ) (hm : m ≤ 2*n+15) :
    G (1/2) ((n+7 : ℕ) : ℤ) (2*n+10) +
      G (1/2) (((n+7 : ℕ) : ℤ)-1) (2*n+9) *
        ((m : ℝ) - ((2*n+10 : ℕ) : ℝ)) ≤
      G (1/2) ((n+7 : ℕ) : ℤ) m := by
  have hsign := pattern1_signs n
  have hend := (pattern1_quotient_and_endpoint n).2
  have hdiff : ((2*n+15 : ℕ) : ℝ) - ((2*n+10 : ℕ) : ℝ) = 5 := by
    push_cast
    ring
  have ht : 2*n+10-1 = 2*n+9 := by omega
  have hp : 2*n+10-2 = 2*n+8 := by omega
  have h := supporting_line (1/2) (by norm_num) (by norm_num)
    (n+7) (2*n+10) (2*n+15) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

theorem pattern2_supporting_line (n m : ℕ) (hm : m ≤ 2*n+10) :
    G (1/2) ((n+4 : ℕ) : ℤ) (2*n+5) +
      G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+4) *
        ((m : ℝ) - ((2*n+5 : ℕ) : ℝ)) ≤
      G (1/2) ((n+4 : ℕ) : ℤ) m := by
  have hsign := pattern2_signs n
  have hend := (pattern2_quotient_and_endpoint n).2
  have hdiff : ((2*n+10 : ℕ) : ℝ) - ((2*n+5 : ℕ) : ℝ) = 5 := by
    push_cast
    ring
  have ht : 2*n+5-1 = 2*n+4 := by omega
  have hp : 2*n+5-2 = 2*n+3 := by omega
  have h := supporting_line (1/2) (by norm_num) (by norm_num)
    (n+4) (2*n+5) (2*n+10) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

theorem pattern3_supporting_line (n m : ℕ) (hm : m ≤ 2*n+6) :
    G (1/2) ((n+2 : ℕ) : ℤ) (2*n+2) +
      G (1/2) (((n+2 : ℕ) : ℤ)-1) (2*n+1) *
        ((m : ℝ) - ((2*n+2 : ℕ) : ℝ)) ≤
      G (1/2) ((n+2 : ℕ) : ℤ) m := by
  have hsign := pattern3_signs n
  have hend := (pattern3_quotient_and_endpoint n).2
  have hdiff : ((2*n+6 : ℕ) : ℝ) - ((2*n+2 : ℕ) : ℝ) = 4 := by
    push_cast
    ring
  have ht : 2*n+2-1 = 2*n+1 := by omega
  have hp : 2*n+2-2 = 2*n+0 := by omega
  have h := supporting_line (1/2) (by norm_num) (by norm_num)
    (n+2) (2*n+2) (2*n+6) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

theorem pattern4_supporting_line (n m : ℕ) (hm : m ≤ 2*n+11) :
    G (1/2) ((n+4 : ℕ) : ℤ) (2*n+6) +
      G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+5) *
        ((m : ℝ) - ((2*n+6 : ℕ) : ℝ)) ≤
      G (1/2) ((n+4 : ℕ) : ℤ) m := by
  have hsign := pattern4_signs n
  have hend := (pattern4_quotient_and_endpoint n).2
  have hdiff : ((2*n+11 : ℕ) : ℝ) - ((2*n+6 : ℕ) : ℝ) = 5 := by
    push_cast
    ring
  have ht : 2*n+6-1 = 2*n+5 := by omega
  have hp : 2*n+6-2 = 2*n+4 := by omega
  have h := supporting_line (1/2) (by norm_num) (by norm_num)
    (n+4) (2*n+6) (2*n+11) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

theorem pattern5_supporting_line (n m : ℕ) (hm : m ≤ 2*n+7) :
    G (1/2) ((n+3 : ℕ) : ℤ) (2*n+5) +
      G (1/2) (((n+3 : ℕ) : ℤ)-1) (2*n+4) *
        ((m : ℝ) - ((2*n+5 : ℕ) : ℝ)) ≤
      G (1/2) ((n+3 : ℕ) : ℤ) m := by
  have hsign := pattern5_signs n
  have hend := (pattern5_quotient_and_endpoint n).2
  have hdiff : ((2*n+7 : ℕ) : ℝ) - ((2*n+5 : ℕ) : ℝ) = 2 := by
    push_cast
    ring
  have ht : 2*n+5-1 = 2*n+4 := by omega
  have hp : 2*n+5-2 = 2*n+3 := by omega
  have h := supporting_line (1/2) (by norm_num) (by norm_num)
    (n+3) (2*n+5) (2*n+7) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

theorem pattern6_supporting_line (n m : ℕ) (hm : m ≤ 2*n+10) :
    G (1/2) ((n+4 : ℕ) : ℤ) (2*n+7) +
      G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+6) *
        ((m : ℝ) - ((2*n+7 : ℕ) : ℝ)) ≤
      G (1/2) ((n+4 : ℕ) : ℤ) m := by
  have hsign := pattern6_signs n
  have hend := (pattern6_quotient_and_endpoint n).2
  have hdiff : ((2*n+10 : ℕ) : ℝ) - ((2*n+7 : ℕ) : ℝ) = 3 := by
    push_cast
    ring
  have ht : 2*n+7-1 = 2*n+6 := by omega
  have hp : 2*n+7-2 = 2*n+5 := by omega
  have h := supporting_line (1/2) (by norm_num) (by norm_num)
    (n+4) (2*n+7) (2*n+10) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

theorem pattern7_supporting_line (n m : ℕ) (hm : m ≤ 2*n+9) :
    G (1/2) ((n+4 : ℕ) : ℤ) (2*n+8) +
      G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+7) *
        ((m : ℝ) - ((2*n+8 : ℕ) : ℝ)) ≤
      G (1/2) ((n+4 : ℕ) : ℤ) m := by
  have hsign := pattern7_signs n
  have hend := (pattern7_quotient_and_endpoint n).2
  have hdiff : ((2*n+9 : ℕ) : ℝ) - ((2*n+8 : ℕ) : ℝ) = 1 := by
    push_cast
    ring
  have ht : 2*n+8-1 = 2*n+7 := by omega
  have hp : 2*n+8-2 = 2*n+6 := by omega
  have h := supporting_line (1/2) (by norm_num) (by norm_num)
    (n+4) (2*n+8) (2*n+9) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

theorem pattern8_supporting_line (n m : ℕ) (hm : m ≤ 2*n+7) :
    G (2/3) ((n+2 : ℕ) : ℤ) (2*n+3) +
      G (2/3) (((n+2 : ℕ) : ℤ)-1) (2*n+2) *
        ((m : ℝ) - ((2*n+3 : ℕ) : ℝ)) ≤
      G (2/3) ((n+2 : ℕ) : ℤ) m := by
  have hsign := pattern8_signs n
  have hend := (pattern8_quotient_and_endpoint n).2
  have hdiff : ((2*n+7 : ℕ) : ℝ) - ((2*n+3 : ℕ) : ℝ) = 4 := by
    push_cast
    ring
  have ht : 2*n+3-1 = 2*n+2 := by omega
  have hp : 2*n+3-2 = 2*n+1 := by omega
  have h := supporting_line (2/3) (by norm_num) (by norm_num)
    (n+2) (2*n+3) (2*n+7) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

theorem pattern9_supporting_line (n m : ℕ) (hm : m ≤ 2*n+8) :
    G (2/3) ((n+3 : ℕ) : ℤ) (2*n+6) +
      G (2/3) (((n+3 : ℕ) : ℤ)-1) (2*n+5) *
        ((m : ℝ) - ((2*n+6 : ℕ) : ℝ)) ≤
      G (2/3) ((n+3 : ℕ) : ℤ) m := by
  have hsign := pattern9_signs n
  have hend := (pattern9_quotient_and_endpoint n).2
  have hdiff : ((2*n+8 : ℕ) : ℝ) - ((2*n+6 : ℕ) : ℝ) = 2 := by
    push_cast
    ring
  have ht : 2*n+6-1 = 2*n+5 := by omega
  have hp : 2*n+6-2 = 2*n+4 := by omega
  have h := supporting_line (2/3) (by norm_num) (by norm_num)
    (n+3) (2*n+6) (2*n+8) (by omega) (by omega) (by omega)
    (by simpa only [ht] using hsign.1)
    (by simpa only [hp] using hsign.2) (by
      rw [ht, hdiff]
      linarith only [hend]) m hm
  simpa only [ht] using h

end Erdos993Lean.Analytic.V213.SmallForestPatterns

#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_supporting_line
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_supporting_line
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_supporting_line
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_supporting_line
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_supporting_line
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_supporting_line
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_supporting_line
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_supporting_line
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_supporting_line
