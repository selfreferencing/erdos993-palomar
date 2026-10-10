module

public import Mathlib
public import Erdos993Lean.Ceiling.Tail

/-!
# The hard-core mean, the occupation bound B5, and the activity-indexed form R221A

Definitions only; the theorems that use them are in `Ceiling/Join.lean`.

For a finite forest `F` on `n` vertices with independence counts `i_k`:

* `partitionFn F λ = Z_F(λ) = ∑_k i_k λ^k` (the independence polynomial at the activity `λ`);
* `hardCoreMean F λ = μ_F(λ) = λ Z_F'(λ) / Z_F(λ) = ∑_k k i_k λ^k / ∑_k i_k λ^k`, the mean size of
  an independent set drawn from the hard-core model at activity `λ`;
* `matchingEnvelopeMean F = W(F) = n/2 − ν(F)/3`, with `ν` the matching number
  (`matchingNumber`, `Ceiling/Statement.lean`); `W(F)` is the mean of `B_F(x) = (1+2x)^ν(1+x)^(n−2ν)`
  normalized at activity 1;
* `numComponents F = cc(F)`, the number of connected components, isolated vertices included.

**B5, occupation at activity 7/3** (`OccupationAt73`; the ceiling proof,
Appendix R3):
`μ_F(7/3) ≥ W(F) + cc(F)/7` for every forest.  A paper proof with a finite check of 428
exact integer cases; stated here as a proposition.

**R221A, the activity-indexed form of the ceiling's analytic input**
(`R221A`): for
every forest with `n ≥ 8,400,000`, every activity `λ ∈ [1/3, 7/3]` and every integer `k` with
`|k − μ_F(λ)| < 1`: `i_{k−1}, i_k, i_{k+1} > 0` and `i_k² > exp(1/(1650 n)) i_{k−1} i_{k+1}`.  This is
the output of a computer-assisted analytic proof (Fourier inversion with an exact
rational error ledger at `n = 8.4·10^6`); **it is not proved in Lean**.
It is stated here for integers `k ≥ 1` (for `n ≥ 8.4·10^6` every `k` within distance 1 of
`μ_F(λ) ≥ λn/(1+3λ) ≥ n/6` is at least 1, so nothing is lost).
-/

@[expose] public section

namespace Erdos993Lean

open Finset

/-- The independence polynomial of a forest evaluated at an activity `t`:
`Z_F(t) = ∑_{k ≤ n} i_k t^k`. -/
noncomputable def partitionFn (F : FiniteForest) (t : ℝ) : ℝ :=
  ∑ k ∈ range (F.n + 1), (independenceCount F k : ℝ) * t ^ k

/-- The hard-core mean `μ_F(t) = ∑_k k i_k t^k / ∑_k i_k t^k`. -/
noncomputable def hardCoreMean (F : FiniteForest) (t : ℝ) : ℝ :=
  (∑ k ∈ range (F.n + 1), (k : ℝ) * (independenceCount F k : ℝ) * t ^ k) / partitionFn F t

/-- `W(F) = n/2 − ν(F)/3`, the mean of `B_F` normalized at activity 1. -/
noncomputable def matchingEnvelopeMean (F : FiniteForest) : ℝ :=
  (F.n : ℝ) / 2 - (matchingNumber F.graph : ℝ) / 3

/-- `cc(F)`: the number of connected components, isolated vertices included. -/
noncomputable def numComponents (F : FiniteForest) : ℕ :=
  Nat.card F.graph.ConnectedComponent

/-- **B5 (occupation at activity 7/3)**: `μ_F(7/3) ≥ W(F) + cc(F)/7` for every forest
(the ceiling proof, Appendix R3; a paper proof with 428 exact finite cases). -/
def OccupationAt73 : Prop :=
  ∀ F : FiniteForest,
    matchingEnvelopeMean F + (numComponents F : ℝ) / 7 ≤ hardCoreMean F (7 / 3)

/-- **R221A (the activity-indexed analytic input of the ceiling; not proved in Lean).**  For
every forest with `n ≥ 8,400,000`, every activity `t ∈ [1/3, 7/3]` and every integer `k ≥ 1`
within distance `1` of the hard-core mean `μ_F(t)`: `i_{k−1}, i_k, i_{k+1} > 0` and
`i_k² > exp(1/(1650 n)) · i_{k−1} i_{k+1}`. -/
def R221A : Prop :=
  ∀ F : FiniteForest, 8400000 ≤ F.n → ∀ t : ℝ, 1 / 3 ≤ t → t ≤ 7 / 3 →
    ∀ k : ℕ, 1 ≤ k → |(k : ℝ) - hardCoreMean F t| < 1 →
      0 < independenceCount F (k - 1) ∧ 0 < independenceCount F k ∧
        0 < independenceCount F (k + 1) ∧
        Real.exp (1 / (1650 * (F.n : ℝ))) *
            ((independenceCount F (k - 1) : ℝ) * (independenceCount F (k + 1) : ℝ)) <
          (independenceCount F k : ℝ) ^ 2

end Erdos993Lean
