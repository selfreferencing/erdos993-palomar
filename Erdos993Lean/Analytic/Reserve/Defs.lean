module

public import Mathlib
public import Erdos993Lean.Analytic.Defs

/-!
# O1 by the two-generation reserve: shared definitions

Source: the proof of O1 by the two-generation reserve.




For every forest, every activity `λ` of a band and every independent `B` containing every leaf whose
neighbour has degree `≥ 2` (every maximum-weight `B`, `IsMaxWeight.leaf_mem`), with `q = λ/(1+λ)`:
`Var K_B ≤ A W`, `A = 1 + (D − 1) q`, hence `Var M ≤ D E M`.  The proof roots each component, keeps for each
rooted subtree the mean and variance `U^s, V^s` of the selected count with the parent unoccupied (`s = 0`)
or occupied (`s = 1`), and proves by postorder induction the reserve `F ≥ α y + γ u²/y` for
`F = A U⁰ − V⁰`, `u = U⁰ − U¹`, `y = −log(1 − p)` (`p` the downward message), with `G = A U¹ − V¹ = ∑ F_child`.
The step reduces, after Cauchy–Schwarz over children and grandchildren and completing the square, to the
three comparisons `CompOK` at `(λ, T, Y)`: `T` = the child's grandchild log-mass, `Y` = the parent's
child log-mass (`Y ≥ lmass λ T`).  They are certified on the finite box (`BoxOK`: `T ≤ 6`, `Y ≤ 4`, the
cell certificates) and proved analytically beyond it (`TailOK`).  The selected-leaf base is `LeafOK`.

Division of labour: the tree induction and the assembly prove `bandVar_of_ok : BandSide c → EntropyOK → BoxOK c → TailOK c → LeafOK c →
BandVar c`; a verified interval checker proves `BoxOK` and `LeafOK` for `band0 … band3`
(it may assume `EntropyOK`); the analytic part proves `EntropyOK` and `TailOK` for
`band0 … band3`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve

open Real

/-- One activity band of the reserve: `λ ∈ [lo, hi]`, cap `D`, `α = aCoef · q`, `γ = λ(3+λ)/gDen`. -/
structure Band where
  lo : ℚ
  hi : ℚ
  D : ℚ
  aCoef : ℚ
  gDen : ℚ

/-- `λ ∈ [1/3, 3/5]`, `D = 8/5`, `α = q/2`, `γ = λ(3+λ)/11` (the lower sharp alternate reserve). -/
def band0 : Band := ⟨1/3, 3/5, 8/5, 1/2, 11⟩
/-- `λ ∈ [3/5, 4/5]`, `D = 7/5`, `α = 23q/50`, `γ = λ(3+λ)/13` (the sharp first-four reserve). -/
def band1 : Band := ⟨3/5, 4/5, 7/5, 23/50, 13⟩
/-- `λ ∈ [4/5, 13/10]`, `D = 6/5`, `α = 23q/50`, `γ = λ(3+λ)/13`. -/
def band2 : Band := ⟨4/5, 13/10, 6/5, 23/50, 13⟩
/-- `λ ∈ [13/10, 8/5]`, `D = 7/5`, `α = 23q/50`, `γ = λ(3+λ)/13`. -/
def band3 : Band := ⟨13/10, 8/5, 7/5, 23/50, 13⟩

variable (c : Band)

/-- `A = 1 + (D − 1) q`. -/
noncomputable def capA (lam : ℝ) : ℝ := 1 + ((c.D : ℝ) - 1) * actQ lam
/-- `α = aCoef · q`. -/
noncomputable def alpha (lam : ℝ) : ℝ := (c.aCoef : ℝ) * actQ lam
/-- `γ = λ (3 + λ) / gDen`. -/
noncomputable def gamma (lam : ℝ) : ℝ := lam * (3 + lam) / (c.gDen : ℝ)

/-- The downward occupation message of a vertex whose children carry total log-mass `X`:
`λ e^{−X} / (1 + λ e^{−X})`. -/
noncomputable def msg (lam X : ℝ) : ℝ := lam * exp (-X) / (1 + lam * exp (-X))

/-- Its log-mass `−log(1 − msg λ X) = log(1 + λ e^{−X})`. -/
noncomputable def lmass (lam X : ℝ) : ℝ := log (1 + lam * exp (-X))

section Coefficients

variable (lam T Y : ℝ)

/-- `E = 1 − p + p T / y − y₀ / Y` with child `s = msg λ T`, `y = lmass λ T` and parent `p = msg λ Y`,
`y₀ = lmass λ Y`. -/
noncomputable def coefE : ℝ :=
  1 - msg lam Y + msg lam Y * T / lmass lam T - lmass lam Y / Y

/-- `H = p (1 − p) + γ p² / y₀`. -/
noncomputable def coefH : ℝ :=
  msg lam Y * (1 - msg lam Y) + gamma c lam * msg lam Y ^ 2 / lmass lam Y

/-- `L = γ (1 − p) − H Y`. -/
noncomputable def coefL : ℝ := gamma c lam * (1 - msg lam Y) - coefH c lam Y * Y

/-- `J = s² T / y`. -/
noncomputable def coefJ : ℝ := msg lam T ^ 2 * T / lmass lam T

/-- `Z = p γ + L J`. -/
noncomputable def coefZ : ℝ := msg lam Y * gamma c lam + coefL c lam Y * coefJ lam T

/-- The normalized (QC) comparison (unselected parent, selected child): `α E + p γ L (s/y)² / Z`. -/
noncomputable def compC : ℝ :=
  alpha c lam * coefE lam T Y +
    msg lam Y * gamma c lam * coefL c lam Y * (msg lam T / lmass lam T) ^ 2 / coefZ c lam T Y

/-- The normalized (QB) comparison (selected parent, unselected child):
`α E + (A p − H) / Y − H² J / Z`. -/
noncomputable def compB : ℝ :=
  alpha c lam * coefE lam T Y + (capA c lam * msg lam Y - coefH c lam Y) / Y -
    coefH c lam Y ^ 2 * coefJ lam T / coefZ c lam T Y

end Coefficients

/-- The three sufficient comparisons at one point: (Q0) `Z > 0`, (QC) `L ≥ 0` or `compC ≥ 0`,
(QB) `compB ≥ 0`. -/
def CompOK (lam T Y : ℝ) : Prop :=
  0 < coefZ c lam T Y ∧ (0 ≤ coefL c lam Y ∨ 0 ≤ compC c lam T Y) ∧ 0 ≤ compB c lam T Y

/-- **The finite box** (the cell certificates): the comparisons for `λ ∈ [lo, hi]`, `0 ≤ T ≤ 6`,
`lmass λ T ≤ Y ≤ 4`. -/
def BoxOK : Prop :=
  ∀ lam T Y : ℝ, (c.lo : ℝ) ≤ lam → lam ≤ c.hi → 0 ≤ T → T ≤ 6 → lmass lam T ≤ Y → Y ≤ 4 →
    CompOK c lam T Y

/-- **The analytic tails**: the comparisons for `λ ∈ [lo, hi]`, `T ≥ 0`, `Y ≥ lmass λ T`, and
`Y ≥ 4` or `T ≥ 6`. -/
def TailOK : Prop :=
  ∀ lam T Y : ℝ, (c.lo : ℝ) ≤ lam → lam ≤ c.hi → 0 ≤ T → lmass lam T ≤ Y → (4 ≤ Y ∨ 6 ≤ T) →
    CompOK c lam T Y

/-- **The selected-leaf base**: `α log(1+λ) + γ q² / log(1+λ) ≤ D q²` on the band. -/
def LeafOK : Prop :=
  ∀ lam : ℝ, (c.lo : ℝ) ≤ lam → lam ≤ c.hi →
    alpha c lam * log (1 + lam) + gamma c lam * actQ lam ^ 2 / log (1 + lam) ≤
      (c.D : ℝ) * actQ lam ^ 2

/-- **The entropy facts** (identities (3) and (3a) with binary Pinsker): for `λ > 0`, `T ≥ 0` and
`lmass λ T ≤ Y`: `E ≥ 0`, and `E · y ≥ 2 (p − s)² + (Y − y)(p + y₀ / Y)` (from the exact identity
`E · y = KL(Ber p ‖ Ber s) + (Y − y)(p + y₀/Y)` and `KL ≥ 2 (p − s)²`).  The tree induction uses
`E ≥ 0` (the unselected parent–child pair) and the cell checker uses both as floors for `E`. -/
def EntropyOK : Prop :=
  ∀ lam T Y : ℝ, 0 < lam → 0 ≤ T → lmass lam T ≤ Y →
    0 ≤ coefE lam T Y ∧
      2 * (msg lam Y - msg lam T) ^ 2 + (Y - lmass lam T) * (msg lam Y + lmass lam Y / Y) ≤
        coefE lam T Y * lmass lam T

/-- Side conditions on a band used by the induction (all four bands satisfy them). -/
def BandSide : Prop :=
  (1 / 3 : ℚ) ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ 7 / 3 ∧ 1 ≤ c.D ∧ 0 < c.aCoef ∧ 0 < c.gDen

/-- **The O1 conclusion on a band** (the consumer's form, as in `VarianceBound`): `Var M ≤ D m` for every
forest, every activity of the band and every maximum-weight independent set. -/
def BandVar : Prop :=
  ∀ F : FiniteForest, ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ c.hi → ∀ B, IsMaxWeight F t B →
    (forestMixture F B t).varM ≤ (c.D : ℝ) * (forestMixture F B t).meanM

end Erdos993Lean.Analytic.Reserve
