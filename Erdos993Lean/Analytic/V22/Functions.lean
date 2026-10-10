module

public import Mathlib
public import Erdos993Lean.Analytic.MGF.Criterion

/-!
# Explicit functions of the repaired fiber-theorem note, version 2.2

Source: the note (version of 2 October 2026), SHA-256
`c08dbf5837e1fce232f4871dffbade9fa8197bd01e9d8c77fbd8c921e35e4415`.
The real-arithmetic functions below are definitions only. They make no claim
that the finite checks, analytic inequalities, or forest theorem are proved.



Root-map existence and uniqueness are proved separately, in the analysis modules.
The definition uses choice only when the defining equation has a solution and
is totalized by zero otherwise; it introduces no axiom.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Positive part, used throughout the note. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- Section 3, the root map of `s + log(1+s) = λ`, with `s > -1`. -/
def rootMap (l : ℝ) : ℝ :=
  if h : ∃ s : ℝ, -1 < s ∧ s + Real.log (1 + s) = l then Classical.choose h else 0

/-- Lemma 3.5: `G(λ)`. -/
def G (l : ℝ) : ℝ := (rootMap l) ^ 2 / (1 + rootMap l)

/-- Lemma 3.5: the formula for `G'(λ)`. -/
def G1 (l : ℝ) : ℝ := rootMap l / (1 + rootMap l)

/-- Lemma 3.5: the formula for `G''(λ)`. -/
def G2 (l : ℝ) : ℝ := 1 / ((1 + rootMap l) * (2 + rootMap l))

/-- Definition 3.10: the positive `t` coordinate of `s > -1`. -/
def tOfS (s : ℝ) : ℝ := Real.rpow (Real.exp s * (1 + s)) (2 / 5)

/-- Section 3: `λ_t`. -/
def lambdaT (t : ℝ) : ℝ := (5 / 2) * Real.log t

/-- Definition 3.10: Gaussian slack. -/
def gaussianSlack (t : ℝ) : ℝ := (9 / 2) * (t - 1) ^ 2 / t - 2 * G (lambdaT t)

/-- Lemma 3.12 and Lemma 7.1: `φ(s)`. -/
def phi (s : ℝ) : ℝ := (18 / 25) * (2 - s / 2) ^ 2 - 2 / (1 + s)

/-- Lemma 3.12: `Λ(a)`. -/
def Lambda (a : ℝ) : ℝ := 2 * a + a ^ 2 / 2 + a ^ 3 / 3 + a ^ 4 / 4 + a ^ 5 / 5 + a ^ 6 / 6

/-- The repaired Lemmas 3.12 and 7.2 define the quotient by this polynomial,
including its value at `a=0`. -/
def polynomialLambdaQuotient (a : ℝ) : ℝ := 2 + a / 2 + a ^ 2 / 3 + a ^ 3 / 4 + a ^ 4 / 5 + a ^ 5 / 6

/-- Lemmas 3.12 and 7.2, with the polynomial quotient at zero. -/
def Q (a : ℝ) : ℝ :=
  (18 / 25) * (polynomialLambdaQuotient a) ^ 2 * (1 + (Lambda a) ^ 2 / 75) * (1 - a) - 2

/-- The right endpoint of the template's `k` interval. -/
def kbar (M : ℝ) : ℝ := 77 / 20 + 10 / M

/-- The template log-ratio shift bound. -/
def hbar (M : ℝ) : ℝ := kbar M / (M + 3)

/-- One endpoint term in Definition 3.10. -/
def templateTerm (t M k : ℝ) : ℝ :=
  M * gaussianSlack t + 2 - 6 * G (lambdaT t) - 2 * k * G1 (lambdaT t) - k ^ 2 * G2 (lambdaT t) / (M + 3)

/-- Definition 3.10: minimum at the two exact rational `k` endpoints. -/
def templateT (t M : ℝ) : ℝ := min (templateTerm t M (71 / 20)) (templateTerm t M (kbar M))

/-- Section 2: the target parabola. -/
def psi (t : ℝ) : ℝ := t - (9 / 2) * (t - 1) ^ 2

/-- Section 2: binomial variance at activity `r=2q-1`. -/
def varianceR (r : ℝ) : ℝ := (1 - r ^ 2) / 4

/-- Section 2: `ρ`. -/
def rho (N : ℝ) : ℝ := N / (N + 1)

/-- Section 2: the bonus `Δ(r,N)`. -/
def Delta (r N : ℝ) : ℝ := r ^ 2 * (N ^ 2 - N + 1) / ((1 - r ^ 2) * N)

/-- Section 2: `γ=1+Δ`. -/
def gamma (r N : ℝ) : ℝ := 1 + Delta r N

/-- Section 4: logarithmic formula for `artanh`, used only in its stated domain. -/
def artanh (r : ℝ) : ℝ := Real.log ((1 + r) / (1 - r)) / 2

/-- Section 4: `artanh r-r`. -/
def aHat (r : ℝ) : ℝ := artanh r - r

/-- Section 4: `s_N`. -/
def sN (r N : ℝ) : ℝ := Real.sqrt (varianceR r * N)

/-- Section 4: `ε`. -/
def epsilon (r N : ℝ) : ℝ := r * Real.sqrt N / (Real.sqrt (varianceR r) * (N + 1))

/-- Section 4: `c₀`. -/
def c0 (r N : ℝ) : ℝ := r ^ 2 / (2 * varianceR r * (N + 1))

/-- Section 4: `Z_L`, with a general window `W` (`W=1` for the original bound). -/
def ZL (r N W : ℝ) : ℝ := 2 * (Real.sqrt W * sN r N + r) / (N + 1)

/-- Section 4: `Z_R`, with a general window `W`. -/
def ZR (r N W : ℝ) : ℝ := 2 * Real.sqrt W * sN r N / (N + 1)

/-- Section 4 and Section 5: the quartic error on a window of width `W`. -/
def quarticError (r N W : ℝ) : ℝ :=
  max ((N + 1) * (ZL r N W) ^ 4 / (12 * (1 - (ZL r N W) ^ 2) * (1 - r ^ 2)))
    ((N + 1) * (ZR r N W) ^ 4 / (12 * (1 - (r + ZR r N W) ^ 2) * (1 - r ^ 2)))

/-- Section 4: the quartic error at `r=0`. -/
def quarticErrorZero (N : ℝ) : ℝ := N ^ 2 / (12 * (N + 1) * (N ^ 2 + N + 1))

/-- Section 4: `ỹ`. -/
def yTilde (r N : ℝ) : ℝ := r + aHat r * (N + 1) / 2

/-- Section 4: `ε'`. -/
def epsilonPrime (r N : ℝ) : ℝ := 4 * yTilde r N * sN r N / (N + 1)

/-- Section 4: `c₀'`. -/
def c0Prime (r N : ℝ) : ℝ := 2 * (yTilde r N) ^ 2 / (N + 1)

/-- Section 4: `c_r`. -/
def cr (r : ℝ) : ℝ := ((artanh r) ^ 2 + Real.log (1 - r ^ 2)) / 2

/-- Proposition 4.5: the original lower-range error. -/
def eL (r N : ℝ) : ℝ := c0 r N + positivePart (quarticError r N 1 - quarticErrorZero N) + epsilon r N

/-- Proposition 4.5: `ρ_U`. -/
def rhoU (r N : ℝ) : ℝ := (1 - r ^ 2) * rho N - epsilonPrime r N / Real.sqrt (gamma r N)

/-- Proposition 4.5: `e_U`, retaining the `-c₀'` term. -/
def eU (r N : ℝ) : ℝ :=
  r ^ 2 * rho N / 2 + epsilonPrime r N / 2 * (Real.sqrt (gamma r N) + 1 / Real.sqrt (gamma r N))
    + (N + 1) * cr r - c0Prime r N

/-- Lemma 4.10: `c=1-1/N`. -/
def cCoef (N : ℝ) : ℝ := 1 - 1 / N

/-- Lemma 4.10: `Z₀`. -/
def Z0 (N : ℝ) : ℝ := Real.sqrt N / (N + 1)

/-- Lemma 4.10: `φ_m`. -/
def phiM (N rm : ℝ) : ℝ := 1 + 2 * rm / Real.sqrt N

/-- Lemma 4.10: `K_L`. -/
def KL (N rm : ℝ) : ℝ := 1 + (phiM N rm) ^ 2 / (1 - (Z0 N) ^ 2 * (phiM N rm) ^ 2)

/-- Lemma 4.10: `K_R`. -/
def KR (N rm : ℝ) : ℝ := 1 / (1 - (rm + Z0 N) ^ 2)

def cL1 (N rm : ℝ) : ℝ := 4 * KL N rm / (N * (1 - rm ^ 2))
def cL2 (N rm : ℝ) : ℝ := (4 * KL N rm / N ^ 2 + 1 / N) / (1 - rm ^ 2)
def cR1 (N rm : ℝ) : ℝ := 2 * KR N rm / ((N + 1) * (1 - rm ^ 2))
def cR2 (N rm : ℝ) : ℝ := (KR N rm + 1) / (N * (1 - rm ^ 2))

/-- Lemma 4.10(a): first linearised coefficient. -/
def alpha1 (N rm : ℝ) : ℝ := 2 / Real.sqrt (1 - rm ^ 2) + max (cL1 N rm) (cR1 N rm) / 12

/-- Lemma 4.10(a): second linearised coefficient. -/
def alpha2 (N rm : ℝ) : ℝ := 2 / (N * (1 - rm ^ 2)) + max (cL2 N rm) (cR2 N rm) / 12

/-- Lemma 4.10(b): the all-`ν` lower bound on `ρ_U`. -/
def rhoStar (N rm : ℝ) : ℝ :=
  (1 - rm ^ 2) * rho N - 2 / ((N + 1) * Real.sqrt (cCoef N)) - rm ^ 2 / (3 * (1 - rm ^ 2) * Real.sqrt (cCoef N))

/-- Lemma 4.10(c). -/
def kappaA (N rm : ℝ) : ℝ := 2 + 2 * (N + 1) / (3 * N * (1 - rm ^ 2) * Real.sqrt (cCoef N))

def e2 : ℝ := 1 / 2
def e3 (rm : ℝ) : ℝ := 5 / (6 * (1 - rm ^ 2))
def e4 (N rm : ℝ) : ℝ := (N + 1) / (12 * N * (1 - rm ^ 2) ^ 2)
def e5 (rm : ℝ) : ℝ := 1 / (12 * (1 - rm ^ 2) ^ 2)

/-- Lemma 4.10(d): `E(ν)`. -/
def E (N rm nu : ℝ) : ℝ := 2 * nu + e2 * nu ^ 2 + e3 rm * nu ^ 3 + e4 N rm * nu ^ 4 + e5 rm * nu ^ 5

/-- Lemmas 4.11 and 4.13: the coefficient after bounding higher powers of `ν`. -/
def E2 (N rm nm : ℝ) : ℝ := e2 + e3 rm * nm + e4 N rm * nm ^ 2 + e5 rm * nm ^ 3

def sigma0 (t M0 : ℝ) : ℝ := positivePart (rootMap (lambdaT t + hbar M0))
def ebar (N rm nm : ℝ) : ℝ := (alpha1 N rm * nm + alpha2 N rm * nm ^ 2) / (N + 1)

/-- Lemma 4.11(L): the exact lower-range denominator. -/
def betaL (t N M0 rm nm : ℝ) : ℝ :=
  (N - 1) * (1 - ebar N rm nm) - 2 * sigma0 t M0 * alpha2 N rm
    - (2 * (alpha1 N rm) ^ 2 + 4 * alpha1 N rm * alpha2 N rm * nm + 2 * (alpha2 N rm) ^ 2 * nm ^ 2) / (N + 1)

/-- Lemma 4.11(L): `D̄_L`; positivity is a separate hypothesis. -/
def dLbar (t N M0 rm nm : ℝ) : ℝ := (sigma0 t M0 * alpha1 N rm) ^ 2 / betaL t N M0 rm nm

/-- Lemma 4.11(U): `β_e`. -/
def betaE (N rm nm : ℝ) : ℝ := N - 1 - 2 / rhoStar N rm * E2 N rm nm

def Ghat (t M0 : ℝ) : ℝ := max (G (lambdaT t)) (G (lambdaT t + hbar M0))

/-- Lemma 4.11(U): all-`ν` `D̄_U`; denominator positivity is separate. -/
def dUbar (t N M0 rm nm : ℝ) : ℝ :=
  4 * (Ghat t M0) ^ 2 / ((rhoStar N rm) ^ 2 * (N - 1 - kappaA N rm * Ghat t M0 / rhoStar N rm))
    + |G1 (lambdaT t)| * 4 / ((rhoStar N rm) ^ 2 * betaE N rm nm)

/-- Lemma 5.4: the bounded-block lower bound on `ρ_U`. -/
def rhoStarBlock (N nm rm : ℝ) : ℝ :=
  (1 - rm ^ 2) * rho N - (2 * nm / (N + 1) + nm ^ 3 / (3 * N * (1 - rm ^ 2))) / Real.sqrt (1 + cCoef N * nm ^ 2)

/-- Lemma 5.4: the bounded-block coefficient. -/
def kappaABlock (N nm rm : ℝ) : ℝ :=
  2 + 2 * (N + 1) / (3 * N * (1 - rm ^ 2)) * nm / Real.sqrt (1 + cCoef N * nm ^ 2)

/-- Lemma 4.11: upper bound of the quadratic supremum on `[0,nm]`. -/
def quadraticSupBound (a b nm : ℝ) : ℝ :=
  if 0 < b then min (a ^ 2 / (4 * b)) (a * nm) else a * nm - b * nm ^ 2

/-- Lemma 5.4: bounded-range upper remainder with explicit coefficients. -/
def dUbarBlock (Gh g1 N nm rm : ℝ) : ℝ :=
  let rs := rhoStarBlock N nm rm
  let ka := kappaABlock N nm rm
  positivePart (quadraticSupBound (4 * Gh / rs) (N - 1 - ka * Gh / rs) nm)
    + g1 * positivePart (quadraticSupBound (4 / rs) (N - 1 - 2 / rs * E2 N rm nm) nm)

/-- Lemma 4.13: the function `f(N)` used by checks 7.6 and 7.7. -/
def lambdaBonusF (N rm : ℝ) : ℝ :=
  (N - 1) * rhoStar N rm / 2 - E2 N rm (min 6 (rm * Real.sqrt N)) - (N + 1) / ((71 / 20) * N)

/-- Section 4.8: the explicit large-`t` majorant `X̄(ν,N)`. -/
def Xbar (nu N rm : ℝ) : ℝ :=
  (N + 1) * nu ^ 4 / (12 * N ^ 2 * (1 - rm ^ 2) ^ 2)
    + nu * Real.sqrt (1 + nu ^ 2) / (N + 1) * (1 + nu ^ 2 * (N + 1) / (6 * N * (1 - rm ^ 2)))
    - rhoStar N rm / 2 * (1 + nu ^ 2 * cCoef N)

/-- Section 5.3: the common ray-majorant formula with a retained upper
remainder. The coefficient choices producing `D` are explicit in the finite
and infinite block functions below, as required by Lemmas 5.4 and 7.14. -/
def phiWithRemainder (t M D : ℝ) : ℝ :=
  t * positivePart (-gaussianSlack t) + t / M * positivePart
    (6 * G (lambdaT t) - 2 + D + max
      (2 * (71 / 20) * G1 (lambdaT t) + (71 / 20) ^ 2 * G2 (lambdaT t) / (M + 3))
      (2 * kbar M * G1 (lambdaT t) + (kbar M) ^ 2 * G2 (lambdaT t) / (M + 3)))

/-- Coarse specialization of the ray majorant: all-`ν` coefficient bounds
with bounded quadratic suprema at the actual `M`. This is preserved for
diagnostics; it is NOT the refined Table 4 finite-block target. -/
def phiAllNuSpecialization (t M rm : ℝ) : ℝ :=
  let N := M + 2
  let nm := min 6 (rm * Real.sqrt N)
  let Gh := Ghat t M
  let rs := rhoStar N rm
  let ka := kappaA N rm
  let d := positivePart (quadraticSupBound (4 * Gh / rs) (N - 1 - ka * Gh / rs) nm)
    + |G1 (lambdaT t)| * positivePart (quadraticSupBound (4 / rs) (N - 1 - 2 / rs * E2 N rm nm) nm)
  phiWithRemainder t M d

/-- Compatibility name for the coarse specialization. Table 4 statements
must use `phiBlock` or `phiInfiniteBlock`, retaining the block parameters. -/
def Phi (t M rm : ℝ) : ℝ := phiAllNuSpecialization t M rm

/-- Lemma 5.4: `ν_m` on a finite block with upper endpoint `M₂`. -/
def phiBlockNuMax (M2 rm : ℝ) : ℝ := min 6 (rm * Real.sqrt (M2 + 2))

/-- Lemma 5.4: the shifted convex upper bound for `G(λ^T_U)` on the block. -/
def phiBlockGhat (t M1 M2 : ℝ) : ℝ :=
  max (G (lambdaT t + (71 / 20) / (M2 + 3))) (G (lambdaT t + hbar M1))

/-- Lemma 5.4: the lower quadratic coefficient `q₂`, with the retained block
`ρ_*` and `ν_m` and the lower endpoint `N₁=M₁+2`. -/
def phiBlockQ2 (M1 M2 rm : ℝ) : ℝ :=
  let N1 := M1 + 2
  let nm := phiBlockNuMax M2 rm
  rhoStarBlock N1 nm rm * cCoef N1 / 2 - E2 N1 rm nm / N1

/-- Lemma 5.4: the shifted negative-derivative bound when
`q₂>0`, with its original fallback otherwise. On the source spike ranges
the arguments are negative, so this agrees with the stated absolute value.
The positive part also records the zero-deficit case if a lower bound is
nonnegative rather than introducing an absolute-value loss. -/
def phiBlockG1Bound (t M1 M2 rm : ℝ) : ℝ :=
  let q2 := phiBlockQ2 M1 M2 rm
  if 0 < q2 then
    positivePart (-G1 (lambdaT t + (71 / 20) / (M2 + 3) - 1 / ((M1 + 2) ^ 2 * q2)))
  else positivePart (-G1 (lambdaT t))

/-- Lemma 5.4: bounded-range upper remainder for a finite block. Division
by `ρ_*` requires `phiBlockCoefficientsValid`; the quadratic supremum keeps
both its positive- and nonpositive-denominator branches. -/
def phiBlockRemainder (t M1 M2 rm : ℝ) : ℝ :=
  dUbarBlock (phiBlockGhat t M1 M2) (phiBlockG1Bound t M1 M2 rm)
    (M1 + 2) (phiBlockNuMax M2 rm) rm

/-- Coefficient positivity guard for the finite block formula. Source-range,
ordering, and consumer hypotheses are retained by the statement using it. -/
def phiBlockCoefficientsValid (M1 M2 rm : ℝ) : Prop :=
  0 < rhoStarBlock (M1 + 2) (phiBlockNuMax M2 rm) rm

/-- Lemmas 5.4 and 7.14: finite-block ray majorant. `M` is the actual fiber
parameter; `M₁,M₂` remain visible in the frozen coefficient choices. -/
def phiBlock (t M M1 M2 rm : ℝ) : ℝ :=
  phiWithRemainder t M (phiBlockRemainder t M1 M2 rm)

/-- Lemma 5.4: final infinite-block upper remainder, evaluated at `M₁`.
This uses the unbounded AM-GM suprema of Lemma 4.11, not a bounded quadratic
minimum at a frozen `ν_m`. Both denominators must be positive. -/
def phiInfiniteBlockRemainder (t M1 rm : ℝ) : ℝ :=
  dUbar t (M1 + 2) M1 rm (min 6 (rm * Real.sqrt (M1 + 2)))

/-- The retained positivity guards for the final infinite block. The note's
monotonicity of `β_e` above the starting `N` is a separate consumer premise. -/
def phiInfiniteBlockCoefficientsValid (t M1 rm : ℝ) : Prop :=
  let N1 := M1 + 2
  let nm := min 6 (rm * Real.sqrt N1)
  0 < rhoStar N1 rm ∧
    0 < N1 - 1 - kappaA N1 rm * Ghat t M1 / rhoStar N1 rm ∧
    0 < betaE N1 rm nm

/-- Lemmas 5.4 and 7.14: final infinite-block ray majorant. `M` is the actual
fiber parameter, while its all-`ν` remainder is frozen at the lower `M₁`. -/
def phiInfiniteBlock (t M M1 rm : ℝ) : ℝ :=
  phiWithRemainder t M (phiInfiniteBlockRemainder t M1 rm)

/-- Section 5.6: the derivative lower bound from Lemma 5.12 (argument is `N`). -/
def uMonoDerivative (r N : ℝ) : ℝ :=
  let m := N + 1
  r ^ 2 / 2 - aHat r * r - cr r - 2 * r ^ 2 / m - 4 * r ^ 2 / m ^ 2
    - 1 / (m * (m - 2)) - aHat r / (2 * r * (m - 2)) - (71 / 20) / m ^ 2

/-- Lemma 5.12: `Φ_r(N)`, preserving the negative `c₀'` term in `e_U`. -/
def phiR (r N : ℝ) : ℝ := (71 / 20) / (N + 1) + rhoU r N / 2 * Delta r N - eU r N

/-- Corollary 5.15: derivative numerator for `ỹ R/(N+1)`. -/
def windowH (r N : ℝ) : ℝ :=
  aHat r * (1 + 2 * r ^ 2 * (N - 1)) - 2 * r * (1 - 4 * r ^ 2) * (N - 1) / (N + 1) ^ 2

/-- Corollary 5.15: termwise lower bound of `Φ_r` on an `(r,N)` block. -/
def phiRBlockLower (ra rb Na Nb : ℝ) : ℝ :=
  let third := 1 / ((Na + 1) * Real.sqrt (cCoef Na)) + rb ^ 2 / (6 * (1 - rb ^ 2) * Real.sqrt (cCoef Na))
  (71 / 20) / (Nb + 1) + rhoStar Na rb * Delta ra Na / 2
    - (rb ^ 2 * rho Nb / 2 + yTilde rb Nb * Real.sqrt (Nb + rb ^ 2 * (Nb - 1) ^ 2) / (Nb + 1) + third + (Nb + 1) * cr rb)

/-- Section 5.6: the window conditions `(c1),(c2),(c3)`. -/
def windowConditions (r N : ℝ) : Prop :=
  ZL r N 3 < 1 ∧ r + ZR r N 3 < 1 ∧ 3 ≤ 12 * (1 - (r + ZR r N 3) ^ 2) / ((1 - r ^ 2) * rho N)

/-- Section 5.6: persistent window conditions `(c1),(c2),(c3')`. -/
def persistentWindowConditions (r N : ℝ) : Prop :=
  ZL r N 3 < 1 ∧ r + ZR r N 3 < 1 ∧ 3 ≤ 12 * (1 - (r + ZR r N 3) ^ 2) / (1 - r ^ 2)

/-- Lemma 5.11: window error `e_L` (distinct from the original range error). -/
def windowEL (r N : ℝ) : ℝ := c0 r N + quarticError r N 3 + epsilon r N * (Real.sqrt 3 / 2 + 1 / (2 * Real.sqrt 3))

def windowRhoL (r N : ℝ) : ℝ := rho N + epsilon r N / Real.sqrt 3
def windowRhoLbar (r N : ℝ) : ℝ := 1 + epsilon r N / Real.sqrt 3

/-- Section 3: Wallis coefficient at an integer index. -/
def wallisW (m : ℕ) : ℝ := ((2 * m).choose m : ℝ) / (4 : ℝ) ^ m

/-- Section 4.1: exact binomial central amplitude, preserving parity. -/
def centralAmplitude (N : ℕ) : ℝ :=
  if N % 2 = 0 then wallisW (N / 2)
  else wallisW ((N + 1) / 2) * Real.exp
    (((N : ℝ) + 1) * ((1 / ((N : ℝ) + 1)) * artanh (1 / ((N : ℝ) + 1))
      + Real.log (1 - (1 / ((N : ℝ) + 1)) ^ 2) / 2))

/-- Section 2: Gaussian amplitude `a_G`. -/
def gaussianAmplitude : ℝ := Real.exp (-(1 / 2 : ℝ)) / Real.sqrt (2 * Real.pi)

/-- Section 5.6: exact `λ^T_c` at integer `N`. -/
def lambdaTc (mu : ℝ) (N : ℕ) : ℝ :=
  Real.log (((N : ℝ) / mu * Real.exp (rho N / 2)) /
    (Real.rpow mu (3 / 2) * centralAmplitude N / (2 * gaussianAmplitude * ((N : ℝ) - 1))))

/-- Lemma 5.11: exact `λ_L` at integer `N`. -/
def windowLambdaL (r mu : ℝ) (N : ℕ) : ℝ := lambdaTc mu N + windowRhoL r N / 2 * Delta r N + windowEL r N

/-- Lemma 5.11: exact window turning-point condition. -/
def windowCondition (r mu : ℝ) (N : ℕ) : Prop :=
  let y := windowRhoL r N / 2 * (gamma r N - min 3 (gamma r N))
  windowLambdaL r mu N ≤ y + Real.log (1 + y)

/-- Lemma 5.11: exact split bound. -/
def xSplit (r mu : ℝ) (N : ℕ) : ℝ :=
  1 - 2 / rho N * G (lambdaTc mu N) + Delta r N / (1 + positivePart (rootMap (windowLambdaL r mu N))) - 2 * windowEL r N / rho N

/-- Lemma 5.11: exact logarithmic bound. -/
def xLog (r mu : ℝ) (N : ℕ) : ℝ := 1 - 2 / windowRhoL r N * (lambdaTc mu N + windowEL r N)

/-- Lemma 5.11: exact lower piece, with its stated window branch. -/
def xL (r mu : ℝ) (N : ℕ) : ℝ :=
  if windowCondition r mu N then min 3 (gamma r N) else max (xSplit r mu N) (xLog r mu N)

/-- Theorem 5.14: the explicit convex upper bound for `G(λ^T_c)` at a real
starting `N` (the finite checks do not interpolate the parity amplitude). -/
def windowGhat (t N : ℝ) : ℝ := Ghat t (N - 2)

/-- Theorem 5.14: upper bound on `s(λ_L)_+` before adding the bonus shift. -/
def windowSbar (t r N : ℝ) : ℝ :=
  positivePart (rootMap (lambdaT t + hbar (N - 2) + windowEL r N))

/-- Theorem 5.14: the requirement on the three-piece bound, with its exact
pointwise sign branch. A cell crossing zero needs the stronger cell requirement. -/
def windowRequired (t N b beta : ℝ) : ℝ :=
  let target := psi t + b + beta * (t - 1)
  if 0 < target then target / t else target * (N - 2) / (t * N)

/-- Theorem 5.14: pointwise split recipe at the actual `r`, without replacing
its window error by a claimed endpoint extremum. -/
def windowSplitAt (t r N : ℝ) : ℝ :=
  1 - 2 / rho N * windowGhat t N
    + Delta r N / (1 + windowSbar t r N + windowRhoLbar r N * Delta r N / 2)
    - 2 * windowEL r N / rho N

/-- Theorem 5.14: pointwise logarithmic recipe at the actual `r`. -/
def windowLogAt (t r N : ℝ) : ℝ :=
  let q := lambdaT t + hbar (N - 2) + windowEL r N
  if 0 ≤ q then 1 - 2 * q / rho N else 1 - 2 * q / windowRhoLbar r N

/-- Theorem 5.14: the pointwise sufficient persistent condition at actual `r`. -/
def windowConditionAt (t r N : ℝ) : Prop :=
  let lhs := lambdaT t + hbar (N - 2) + windowEL r N + windowRhoLbar r N
  if 2 ≤ Delta r N then lhs ≤ Real.log (1 + rho N * (Delta r N - 2) / 2) else lhs ≤ 0

/-- Theorem 5.14: the explicit pointwise lower-range recipe at actual `r`. -/
def windowLowerAt (t r N : ℝ) : ℝ :=
  let wlo := min 3 (1 + Delta r N)
  if windowConditionAt t r N then wlo else min wlo (max (windowSplitAt t r N) (windowLogAt t r N))

/-- Lemma 5.13 and Theorem 5.14: the upper-range recipe at actual `r`, using
the exact `Φ_r` formula and the explicit all-`ν` `ρ_*` bound for `r≤rm`. -/
def windowUpperAt (t r N rm : ℝ) : ℝ :=
  1 + Delta r N - 2 / rhoStar N rm * G (min 0 (lambdaT t + phiR r N))

/-- Theorem 5.14: explicit pointwise recipe for the three ranges. -/
def windowAt (t r N rm : ℝ) : ℝ := min (windowLowerAt t r N) (min 3 (windowUpperAt t r N rm))

/-- Theorem 5.14's pointwise split recipe; soundness is a separate obligation. -/
def windowXsplitLower (t r N : ℝ) : ℝ := windowSplitAt t r N

/-- Theorem 5.14's pointwise log recipe; soundness is a separate obligation. -/
def windowXlogLower (t r N : ℝ) : ℝ := windowLogAt t r N

/-- Theorem 5.14's pointwise persistent condition at actual `r`. -/
def persistentWindowCondition (t r N : ℝ) : Prop := windowConditionAt t r N

/-- Theorem 5.14's pointwise lower-range recipe at actual `r`. -/
def windowXlLower (t r N : ℝ) : ℝ := windowLowerAt t r N

/-- Lemma 5.13's pointwise upper-range recipe, preserving `r` and the cap `rm`. -/
def windowXuLower (t r N rm : ℝ) : ℝ := windowUpperAt t r N rm

/-- Theorem 5.14's pointwise three-range recipe, preserving `r` and the cap `rm`. -/
def windowXLower (t r N rm : ℝ) : ℝ := windowAt t r N rm

/-- Corollary 5.15: explicit `(ra,rb,N)` block upper-range recipe. Every term
of `phiRBlockLower` is retained. Soundness requires the block monotonicity
and positivity obligations of Lemma 5.13 and Corollary 5.15. -/
def windowXuBlockLower (t ra rb N : ℝ) : ℝ :=
  1 + Delta ra N - 2 / rhoStar N rb * G (min 0 (lambdaT t + phiRBlockLower ra rb N N))

/-- Section 2: valley-kernel weights. -/
def weightL (q : ℝ) : ℝ := q ^ 2 * (3 - 4 * q)
def weightR (q : ℝ) : ℝ := (1 - q) ^ 2 * (4 * q - 1)

/-- Section 2: exact fiber function, at every integer offset. -/
def fiberFunction (q mu : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  let v := q * (1 - q)
  let sig := Real.sqrt (v * mu)
  let u := (j : ℝ) - q * M - (2 * q - 1) / 2
  sig ^ 3 * Erdos993Lean.Analytic.kernel2 q (weightL q) (weightR q) M j / (4 * v ^ 2 * gaussianAmplitude) + u ^ 2 / sig ^ 2

/-- Section 5.1: the infimum over *all* integer offsets. No support restriction
is silently substituted for the paper's `min_j`. -/
def fiberInfimum (q mu : ℝ) (M : ℕ) : ℝ := sInf (Set.range (fun j : ℤ => fiberFunction q mu M j))

/-- Section 5.1: target line. -/
def targetLine (b beta t : ℝ) : ℝ := b + beta * (t - 1)

/-- Section 5.1: spike deficit with the exact target line. The analysis modules
must prove attainment/boundedness when identifying the infimum with `min_j`. -/
def deficitG (q mu b beta : ℝ) (M : ℕ) : ℝ :=
  positivePart (psi ((M : ℝ) / mu) + targetLine b beta ((M : ℝ) / mu) - fiberInfimum q mu M)

end

end Erdos993Lean.Analytic.V22

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.positivePart
#print axioms Erdos993Lean.Analytic.V22.positivePart
#check Erdos993Lean.Analytic.V22.rootMap
#print axioms Erdos993Lean.Analytic.V22.rootMap
#check Erdos993Lean.Analytic.V22.G
#print axioms Erdos993Lean.Analytic.V22.G
#check Erdos993Lean.Analytic.V22.G1
#print axioms Erdos993Lean.Analytic.V22.G1
#check Erdos993Lean.Analytic.V22.G2
#print axioms Erdos993Lean.Analytic.V22.G2
#check Erdos993Lean.Analytic.V22.tOfS
#print axioms Erdos993Lean.Analytic.V22.tOfS
#check Erdos993Lean.Analytic.V22.lambdaT
#print axioms Erdos993Lean.Analytic.V22.lambdaT
#check Erdos993Lean.Analytic.V22.gaussianSlack
#print axioms Erdos993Lean.Analytic.V22.gaussianSlack
#check Erdos993Lean.Analytic.V22.phi
#print axioms Erdos993Lean.Analytic.V22.phi
#check Erdos993Lean.Analytic.V22.Lambda
#print axioms Erdos993Lean.Analytic.V22.Lambda
#check Erdos993Lean.Analytic.V22.polynomialLambdaQuotient
#print axioms Erdos993Lean.Analytic.V22.polynomialLambdaQuotient
#check Erdos993Lean.Analytic.V22.Q
#print axioms Erdos993Lean.Analytic.V22.Q
#check Erdos993Lean.Analytic.V22.kbar
#print axioms Erdos993Lean.Analytic.V22.kbar
#check Erdos993Lean.Analytic.V22.hbar
#print axioms Erdos993Lean.Analytic.V22.hbar
#check Erdos993Lean.Analytic.V22.templateTerm
#print axioms Erdos993Lean.Analytic.V22.templateTerm
#check Erdos993Lean.Analytic.V22.templateT
#print axioms Erdos993Lean.Analytic.V22.templateT
#check Erdos993Lean.Analytic.V22.psi
#print axioms Erdos993Lean.Analytic.V22.psi
#check Erdos993Lean.Analytic.V22.varianceR
#print axioms Erdos993Lean.Analytic.V22.varianceR
#check Erdos993Lean.Analytic.V22.rho
#print axioms Erdos993Lean.Analytic.V22.rho
#check Erdos993Lean.Analytic.V22.Delta
#print axioms Erdos993Lean.Analytic.V22.Delta
#check Erdos993Lean.Analytic.V22.gamma
#print axioms Erdos993Lean.Analytic.V22.gamma
#check Erdos993Lean.Analytic.V22.artanh
#print axioms Erdos993Lean.Analytic.V22.artanh
#check Erdos993Lean.Analytic.V22.aHat
#print axioms Erdos993Lean.Analytic.V22.aHat
#check Erdos993Lean.Analytic.V22.sN
#print axioms Erdos993Lean.Analytic.V22.sN
#check Erdos993Lean.Analytic.V22.epsilon
#print axioms Erdos993Lean.Analytic.V22.epsilon
#check Erdos993Lean.Analytic.V22.c0
#print axioms Erdos993Lean.Analytic.V22.c0
#check Erdos993Lean.Analytic.V22.ZL
#print axioms Erdos993Lean.Analytic.V22.ZL
#check Erdos993Lean.Analytic.V22.ZR
#print axioms Erdos993Lean.Analytic.V22.ZR
#check Erdos993Lean.Analytic.V22.quarticError
#print axioms Erdos993Lean.Analytic.V22.quarticError
#check Erdos993Lean.Analytic.V22.quarticErrorZero
#print axioms Erdos993Lean.Analytic.V22.quarticErrorZero
#check Erdos993Lean.Analytic.V22.yTilde
#print axioms Erdos993Lean.Analytic.V22.yTilde
#check Erdos993Lean.Analytic.V22.epsilonPrime
#print axioms Erdos993Lean.Analytic.V22.epsilonPrime
#check Erdos993Lean.Analytic.V22.c0Prime
#print axioms Erdos993Lean.Analytic.V22.c0Prime
#check Erdos993Lean.Analytic.V22.cr
#print axioms Erdos993Lean.Analytic.V22.cr
#check Erdos993Lean.Analytic.V22.eL
#print axioms Erdos993Lean.Analytic.V22.eL
#check Erdos993Lean.Analytic.V22.rhoU
#print axioms Erdos993Lean.Analytic.V22.rhoU
#check Erdos993Lean.Analytic.V22.eU
#print axioms Erdos993Lean.Analytic.V22.eU
#check Erdos993Lean.Analytic.V22.cCoef
#print axioms Erdos993Lean.Analytic.V22.cCoef
#check Erdos993Lean.Analytic.V22.Z0
#print axioms Erdos993Lean.Analytic.V22.Z0
#check Erdos993Lean.Analytic.V22.phiM
#print axioms Erdos993Lean.Analytic.V22.phiM
#check Erdos993Lean.Analytic.V22.KL
#print axioms Erdos993Lean.Analytic.V22.KL
#check Erdos993Lean.Analytic.V22.KR
#print axioms Erdos993Lean.Analytic.V22.KR
#check Erdos993Lean.Analytic.V22.cL1
#print axioms Erdos993Lean.Analytic.V22.cL1
#check Erdos993Lean.Analytic.V22.cL2
#print axioms Erdos993Lean.Analytic.V22.cL2
#check Erdos993Lean.Analytic.V22.cR1
#print axioms Erdos993Lean.Analytic.V22.cR1
#check Erdos993Lean.Analytic.V22.cR2
#print axioms Erdos993Lean.Analytic.V22.cR2
#check Erdos993Lean.Analytic.V22.alpha1
#print axioms Erdos993Lean.Analytic.V22.alpha1
#check Erdos993Lean.Analytic.V22.alpha2
#print axioms Erdos993Lean.Analytic.V22.alpha2
#check Erdos993Lean.Analytic.V22.rhoStar
#print axioms Erdos993Lean.Analytic.V22.rhoStar
#check Erdos993Lean.Analytic.V22.kappaA
#print axioms Erdos993Lean.Analytic.V22.kappaA
#check Erdos993Lean.Analytic.V22.e2
#print axioms Erdos993Lean.Analytic.V22.e2
#check Erdos993Lean.Analytic.V22.e3
#print axioms Erdos993Lean.Analytic.V22.e3
#check Erdos993Lean.Analytic.V22.e4
#print axioms Erdos993Lean.Analytic.V22.e4
#check Erdos993Lean.Analytic.V22.e5
#print axioms Erdos993Lean.Analytic.V22.e5
#check Erdos993Lean.Analytic.V22.E
#print axioms Erdos993Lean.Analytic.V22.E
#check Erdos993Lean.Analytic.V22.E2
#print axioms Erdos993Lean.Analytic.V22.E2
#check Erdos993Lean.Analytic.V22.sigma0
#print axioms Erdos993Lean.Analytic.V22.sigma0
#check Erdos993Lean.Analytic.V22.ebar
#print axioms Erdos993Lean.Analytic.V22.ebar
#check Erdos993Lean.Analytic.V22.betaL
#print axioms Erdos993Lean.Analytic.V22.betaL
#check Erdos993Lean.Analytic.V22.dLbar
#print axioms Erdos993Lean.Analytic.V22.dLbar
#check Erdos993Lean.Analytic.V22.betaE
#print axioms Erdos993Lean.Analytic.V22.betaE
#check Erdos993Lean.Analytic.V22.Ghat
#print axioms Erdos993Lean.Analytic.V22.Ghat
#check Erdos993Lean.Analytic.V22.dUbar
#print axioms Erdos993Lean.Analytic.V22.dUbar
#check Erdos993Lean.Analytic.V22.rhoStarBlock
#print axioms Erdos993Lean.Analytic.V22.rhoStarBlock
#check Erdos993Lean.Analytic.V22.kappaABlock
#print axioms Erdos993Lean.Analytic.V22.kappaABlock
#check Erdos993Lean.Analytic.V22.quadraticSupBound
#print axioms Erdos993Lean.Analytic.V22.quadraticSupBound
#check Erdos993Lean.Analytic.V22.dUbarBlock
#print axioms Erdos993Lean.Analytic.V22.dUbarBlock
#check Erdos993Lean.Analytic.V22.lambdaBonusF
#print axioms Erdos993Lean.Analytic.V22.lambdaBonusF
#check Erdos993Lean.Analytic.V22.Xbar
#print axioms Erdos993Lean.Analytic.V22.Xbar
#check Erdos993Lean.Analytic.V22.phiWithRemainder
#print axioms Erdos993Lean.Analytic.V22.phiWithRemainder
#check Erdos993Lean.Analytic.V22.phiAllNuSpecialization
#print axioms Erdos993Lean.Analytic.V22.phiAllNuSpecialization
#check Erdos993Lean.Analytic.V22.Phi
#print axioms Erdos993Lean.Analytic.V22.Phi
#check Erdos993Lean.Analytic.V22.phiBlockNuMax
#print axioms Erdos993Lean.Analytic.V22.phiBlockNuMax
#check Erdos993Lean.Analytic.V22.phiBlockGhat
#print axioms Erdos993Lean.Analytic.V22.phiBlockGhat
#check Erdos993Lean.Analytic.V22.phiBlockQ2
#print axioms Erdos993Lean.Analytic.V22.phiBlockQ2
#check Erdos993Lean.Analytic.V22.phiBlockG1Bound
#print axioms Erdos993Lean.Analytic.V22.phiBlockG1Bound
#check Erdos993Lean.Analytic.V22.phiBlockRemainder
#print axioms Erdos993Lean.Analytic.V22.phiBlockRemainder
#check Erdos993Lean.Analytic.V22.phiBlockCoefficientsValid
#print axioms Erdos993Lean.Analytic.V22.phiBlockCoefficientsValid
#check Erdos993Lean.Analytic.V22.phiBlock
#print axioms Erdos993Lean.Analytic.V22.phiBlock
#check Erdos993Lean.Analytic.V22.phiInfiniteBlockRemainder
#print axioms Erdos993Lean.Analytic.V22.phiInfiniteBlockRemainder
#check Erdos993Lean.Analytic.V22.phiInfiniteBlockCoefficientsValid
#print axioms Erdos993Lean.Analytic.V22.phiInfiniteBlockCoefficientsValid
#check Erdos993Lean.Analytic.V22.phiInfiniteBlock
#print axioms Erdos993Lean.Analytic.V22.phiInfiniteBlock
#check Erdos993Lean.Analytic.V22.uMonoDerivative
#print axioms Erdos993Lean.Analytic.V22.uMonoDerivative
#check Erdos993Lean.Analytic.V22.phiR
#print axioms Erdos993Lean.Analytic.V22.phiR
#check Erdos993Lean.Analytic.V22.windowH
#print axioms Erdos993Lean.Analytic.V22.windowH
#check Erdos993Lean.Analytic.V22.phiRBlockLower
#print axioms Erdos993Lean.Analytic.V22.phiRBlockLower
#check Erdos993Lean.Analytic.V22.windowConditions
#print axioms Erdos993Lean.Analytic.V22.windowConditions
#check Erdos993Lean.Analytic.V22.persistentWindowConditions
#print axioms Erdos993Lean.Analytic.V22.persistentWindowConditions
#check Erdos993Lean.Analytic.V22.windowEL
#print axioms Erdos993Lean.Analytic.V22.windowEL
#check Erdos993Lean.Analytic.V22.windowRhoL
#print axioms Erdos993Lean.Analytic.V22.windowRhoL
#check Erdos993Lean.Analytic.V22.windowRhoLbar
#print axioms Erdos993Lean.Analytic.V22.windowRhoLbar
#check Erdos993Lean.Analytic.V22.wallisW
#print axioms Erdos993Lean.Analytic.V22.wallisW
#check Erdos993Lean.Analytic.V22.centralAmplitude
#print axioms Erdos993Lean.Analytic.V22.centralAmplitude
#check Erdos993Lean.Analytic.V22.gaussianAmplitude
#print axioms Erdos993Lean.Analytic.V22.gaussianAmplitude
#check Erdos993Lean.Analytic.V22.lambdaTc
#print axioms Erdos993Lean.Analytic.V22.lambdaTc
#check Erdos993Lean.Analytic.V22.windowLambdaL
#print axioms Erdos993Lean.Analytic.V22.windowLambdaL
#check Erdos993Lean.Analytic.V22.windowCondition
#print axioms Erdos993Lean.Analytic.V22.windowCondition
#check Erdos993Lean.Analytic.V22.xSplit
#print axioms Erdos993Lean.Analytic.V22.xSplit
#check Erdos993Lean.Analytic.V22.xLog
#print axioms Erdos993Lean.Analytic.V22.xLog
#check Erdos993Lean.Analytic.V22.xL
#print axioms Erdos993Lean.Analytic.V22.xL
#check Erdos993Lean.Analytic.V22.windowGhat
#print axioms Erdos993Lean.Analytic.V22.windowGhat
#check Erdos993Lean.Analytic.V22.windowSbar
#print axioms Erdos993Lean.Analytic.V22.windowSbar
#check Erdos993Lean.Analytic.V22.windowRequired
#print axioms Erdos993Lean.Analytic.V22.windowRequired
#check Erdos993Lean.Analytic.V22.windowSplitAt
#print axioms Erdos993Lean.Analytic.V22.windowSplitAt
#check Erdos993Lean.Analytic.V22.windowLogAt
#print axioms Erdos993Lean.Analytic.V22.windowLogAt
#check Erdos993Lean.Analytic.V22.windowConditionAt
#print axioms Erdos993Lean.Analytic.V22.windowConditionAt
#check Erdos993Lean.Analytic.V22.windowLowerAt
#print axioms Erdos993Lean.Analytic.V22.windowLowerAt
#check Erdos993Lean.Analytic.V22.windowUpperAt
#print axioms Erdos993Lean.Analytic.V22.windowUpperAt
#check Erdos993Lean.Analytic.V22.windowAt
#print axioms Erdos993Lean.Analytic.V22.windowAt
#check Erdos993Lean.Analytic.V22.windowXsplitLower
#print axioms Erdos993Lean.Analytic.V22.windowXsplitLower
#check Erdos993Lean.Analytic.V22.windowXlogLower
#print axioms Erdos993Lean.Analytic.V22.windowXlogLower
#check Erdos993Lean.Analytic.V22.persistentWindowCondition
#print axioms Erdos993Lean.Analytic.V22.persistentWindowCondition
#check Erdos993Lean.Analytic.V22.windowXlLower
#print axioms Erdos993Lean.Analytic.V22.windowXlLower
#check Erdos993Lean.Analytic.V22.windowXuLower
#print axioms Erdos993Lean.Analytic.V22.windowXuLower
#check Erdos993Lean.Analytic.V22.windowXLower
#print axioms Erdos993Lean.Analytic.V22.windowXLower
#check Erdos993Lean.Analytic.V22.windowXuBlockLower
#print axioms Erdos993Lean.Analytic.V22.windowXuBlockLower
#check Erdos993Lean.Analytic.V22.weightL
#print axioms Erdos993Lean.Analytic.V22.weightL
#check Erdos993Lean.Analytic.V22.weightR
#print axioms Erdos993Lean.Analytic.V22.weightR
#check Erdos993Lean.Analytic.V22.fiberFunction
#print axioms Erdos993Lean.Analytic.V22.fiberFunction
#check Erdos993Lean.Analytic.V22.fiberInfimum
#print axioms Erdos993Lean.Analytic.V22.fiberInfimum
#check Erdos993Lean.Analytic.V22.targetLine
#print axioms Erdos993Lean.Analytic.V22.targetLine
#check Erdos993Lean.Analytic.V22.deficitG
#print axioms Erdos993Lean.Analytic.V22.deficitG
