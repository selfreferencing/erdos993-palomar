module

public import Erdos993Lean.Analytic.V213.SmallForestAffineIdentity

/-! Proposed exact quotient operands, not proofs of identities or signs. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestPatterns

def prod2 (j : ℚ) : ℚ := (j+1)*(j+2)
def prod3 (j : ℚ) : ℚ := prod2 j*(j+3)
def prod4 (j : ℚ) : ℚ := prod3 j*(j+4)

-- display.pattern_polynomials; nine-pattern P4/P3 definitions
-- P_4(x)=19x^4+272x^3+1307x^2+2202x+448,\qquad P_3(x)=11x^3+105x^2+268x+84.
def P4 (x : ℚ) : ℚ := 19*x^4+272*x^3+1307*x^2+2202*x+448
def P3 (x : ℚ) : ℚ := 11*x^3+105*x^2+268*x+84
structure PatternInput where
  w : ℚ
  u : ℤ
  nu : ℤ
  firstIndex : ℕ
  deriving Repr, DecidableEq
-- symbolic_patterns.01; r12:lem28 / nine symbolic patterns
-- $1/2$ & $-4$ & $1$ & $7$ & $3[j^2(19j-21)+24j+4]/[(j-6)(j+1)_2]$\\
def pattern1 : PatternInput := ⟨((1 : ℚ) / 2), -4, 1, 7⟩
def quotient1 (j : ℚ) : ℚ := 3*(j^2*(19*j-21)+24*j+4)/((j-6)*prod2 j)
-- symbolic_patterns.02; r12:lem28 / nine symbolic patterns
-- $1/2$ & $-3$ & $2$ & $4$ & $3j[j^2(19j-36)+19j+54]/[(j-3)(j+1)_3]$\\
def pattern2 : PatternInput := ⟨((1 : ℚ) / 2), -3, 2, 4⟩
def quotient2 (j : ℚ) : ℚ := 3*j*(j^2*(19*j-36)+19*j+54)/((j-3)*prod3 j)
-- symbolic_patterns.03; r12:lem28 / nine symbolic patterns
-- $1/2$ & $-2$ & $2$ & $2$ & $2j(j-2)(13j+11)/(j+1)_3$\\
def pattern3 : PatternInput := ⟨((1 : ℚ) / 2), -2, 2, 2⟩
def quotient3 (j : ℚ) : ℚ := 2*j*(j-2)*(13*j+11)/prod3 j
-- symbolic_patterns.04; r12:lem28 / nine symbolic patterns
-- $1/2$ & $-2$ & $3$ & $4$ & $3P_4(j-4)/(j+1)_4$\\
def pattern4 : PatternInput := ⟨((1 : ℚ) / 2), -2, 3, 4⟩
def quotient4 (j : ℚ) : ℚ := 3*P4 (j-4)/prod4 j
-- symbolic_patterns.05; r12:lem28 / nine symbolic patterns
-- $1/2$ & $-1$ & $1$ & $3$ & $[4(j-3)^2+15(j-3)+5]/(j+1)_2$\\
def pattern5 : PatternInput := ⟨((1 : ℚ) / 2), -1, 1, 3⟩
def quotient5 (j : ℚ) : ℚ := (4*(j-3)^2+15*(j-3)+5)/prod2 j
-- symbolic_patterns.06; r12:lem28 / nine symbolic patterns
-- $1/2$ & $-1$ & $2$ & $4$ & $P_3(j-4)/(j+1)_3$\\
def pattern6 : PatternInput := ⟨((1 : ℚ) / 2), -1, 2, 4⟩
def quotient6 (j : ℚ) : ℚ := P3 (j-4)/prod3 j
-- symbolic_patterns.07; r12:lem28 / nine symbolic patterns
-- $1/2$ & $0$ & $1$ & $4$ & $(j-4)/(j+2)$\\
def pattern7 : PatternInput := ⟨((1 : ℚ) / 2), 0, 1, 4⟩
def quotient7 (j : ℚ) : ℚ := (j-4)/(j+2)
-- symbolic_patterns.08; r12:lem28 / nine symbolic patterns
-- $2/3$ & $-1$ & $3$ & $2$ & $2(j-2)(88j^3+243j^2+209j+60)/[3(j+1)_4]$\\
def pattern8 : PatternInput := ⟨((2 : ℚ) / 3), -1, 3, 2⟩
def quotient8 (j : ℚ) : ℚ := 2*(j-2)*(88*j^3+243*j^2+209*j+60)/(3*prod4 j)
-- symbolic_patterns.09; r12:lem28 / nine symbolic patterns
-- $2/3$ & $0$ & $2$ & $3$ & $[13(j-3)^2+65(j-3)+42]/[2(j+2)(j+3)]$\\
def pattern9 : PatternInput := ⟨((2 : ℚ) / 3), 0, 2, 3⟩
def quotient9 (j : ℚ) : ℚ := (13*(j-3)^2+65*(j-3)+42)/(2*(j+2)*(j+3))
end Erdos993Lean.Analytic.V213.SmallForestPatterns

#check Erdos993Lean.Analytic.V213.SmallForestPatterns.prod2
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.prod2
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.prod3
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.prod3
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.prod4
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.prod4
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.P4
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.P4
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.P3
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.P3
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.PatternInput
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.PatternInput
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient1
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient1
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient2
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient2
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient3
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient3
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient4
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient4
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient5
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient5
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient6
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient6
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient7
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient7
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient8
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient8
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient9
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.quotient9
