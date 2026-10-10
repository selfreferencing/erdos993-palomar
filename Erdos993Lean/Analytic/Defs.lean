module

public import Mathlib
public import Erdos993Lean.Ceiling.HardCore

/-!
# The analytic route for forests with at least 61 vertices: shared definitions


This file fixes the interface between the parts of the analytic route; it contains definitions only.

Sources: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*,
v1.1, equations (45)–(46) (the conditional binomial mixture over a maximum-weight independent set);
the notes T1 (the no-valley lemma) and
T23 (the forest inputs).

* `binom M q j` — the binomial point mass `b_M(j; q)`, zero outside `0 ≤ j ≤ M`.
* `Mixture ι` — a finite mixture of shifted binomials: states `σ ∈ S`, weights `w σ`, a free count
  `M σ` and a fixed count `Y σ`; conditionally on `σ` the size is `K = Y σ + Bin(M σ, q)`, so
  `P(K = i) = ∑_σ w σ · b_{M σ}(i − Y σ; q)` (`Mixture.prob`).
* `forestMixture F B t` — the hard-core model of the forest `F` at activity `t`, conditioned on its
  configuration `σ` on `C = Bᶜ`, for an independent set `B`: the states are the independent subsets
  `σ ⊆ C`, with weight `t^|σ| (1 + t)^(M σ) / Z_F(t)`, fixed count `Y σ = |σ|` and free count
  `M σ = #{b ∈ B : b has no neighbour in σ}`.
* `marginal`, `weightW` (`W = ∑_{b ∈ B} π_b`), `hardCoreVar` (`V = Var K`), `IsMaxWeight`.
* `delta q k M Y = k − Y − qM` (Zhang's `δ`), `kappa` (T1's valley kernel `κ = f_L/q + f_R/(1−q)`).
* `NoValleyAt` — the conclusion of T1 Theorem 6.1 for every mixture satisfying the moment inputs.
* `ExplicitThreshold` — T1's explicit threshold condition (Theorem 3.1 + Lemma 5.1 + Theorem 6.1,
  with the fibre lower bound `h` left abstract; T1 Props 4.2/4.3 are one way to supply it).
* `Profile`, the input propositions O1–O5 and `AnalyticInputs`: the open analytic content of the
  route, one proposition per open object.  O4 is the
  no-valley property itself (`ThresholdNoValley`); its bounded-`m` part is discharged by T1 from
  `ThresholdNumerics`.

Activity range: `InRange t ↔ 1/3 ≤ t ≤ 7/3`.  The top activity is `7/3` (open object O6, option (b):
the package's B5 `occupationAt73`), so every input must hold on `[1/3, 7/3]`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic

open Finset

/-! ## Binomial point masses -/

/-- The binomial point mass `b_M(j; q) = C(M, j) q^j (1 − q)^(M − j)`, extended by zero outside
`0 ≤ j ≤ M`. -/
noncomputable def binom (M : ℕ) (q : ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ (M : ℤ) then
    ((M.choose j.toNat : ℕ) : ℝ) * q ^ j.toNat * (1 - q) ^ (M - j.toNat)
  else 0

/-- The activity-to-probability map `q = t / (1 + t)`. -/
noncomputable def actQ (t : ℝ) : ℝ := t / (1 + t)

/-- Zhang's `δ = j − qM` with `j = k − Y`, at rank `k`. -/
noncomputable def delta (q : ℝ) (k : ℤ) (M Y : ℕ) : ℝ := (k : ℝ) - (Y : ℝ) - q * (M : ℝ)

/-- T1's valley kernel `κ(M, j) = f_L(M, j)/q + f_R(M, j)/(1 − q)`, with
`f_L = (1 − q) b_M(j) − q b_M(j − 1)` and `f_R = q b_M(j) − (1 − q) b_M(j + 1)`. -/
noncomputable def kappa (q : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  ((1 - q) * binom M q j - q * binom M q (j - 1)) / q +
    (q * binom M q j - (1 - q) * binom M q (j + 1)) / (1 - q)

/-! ## Finite binomial mixtures -/

/-- A finite mixture of shifted binomials.  Conditionally on the state `σ`, the size is
`K = Y σ + Bin(M σ, q)`. -/
structure Mixture (ι : Type*) where
  /-- the states -/
  S : Finset ι
  /-- the weight of a state -/
  w : ι → ℝ
  /-- the free count (number of free binomial trials) -/
  M : ι → ℕ
  /-- the fixed count -/
  Y : ι → ℕ

namespace Mixture

variable {ι : Type*} (X : Mixture ι)

/-- The weights form a probability distribution on the states. -/
def IsProb : Prop := (∀ σ ∈ X.S, 0 ≤ X.w σ) ∧ ∑ σ ∈ X.S, X.w σ = 1

/-- `E[g(M, Y)]`. -/
noncomputable def expect (g : ℕ → ℕ → ℝ) : ℝ := ∑ σ ∈ X.S, X.w σ * g (X.M σ) (X.Y σ)

/-- `P(K = i) = ∑_σ w σ · b_{M σ}(i − Y σ; q)`. -/
noncomputable def prob (q : ℝ) (i : ℤ) : ℝ :=
  ∑ σ ∈ X.S, X.w σ * binom (X.M σ) q (i - (X.Y σ : ℤ))

/-- `m = E M`. -/
noncomputable def meanM : ℝ := X.expect fun M _ => (M : ℝ)

/-- `Var M = E (M − m)²`. -/
noncomputable def varM : ℝ := X.expect fun M _ => ((M : ℝ) - X.meanM) ^ 2

/-- `P(M ≤ M')`. -/
noncomputable def cdfM (M' : ℕ) : ℝ := ∑ σ ∈ X.S with X.M σ ≤ M', X.w σ

/-- A weak valley of the law of `K` at rank `k`, in the tilted form: `(1 − q) P_k ≤ q P_{k−1}` and
`q P_k ≤ (1 − q) P_{k+1}` (for `P_i = c_i λ^i / Z` these say `c_k ≤ c_{k−1}` and `c_k ≤ c_{k+1}`). -/
def WeakValley (q : ℝ) (k : ℤ) : Prop :=
  (1 - q) * X.prob q k ≤ q * X.prob q (k - 1) ∧ q * X.prob q k ≤ (1 - q) * X.prob q (k + 1)

end Mixture

/-! ## The no-valley property and T1's explicit threshold -/

/-- **The conclusion of the no-valley lemma (T1 Theorem 6.1).**  Every probability mixture with
parameter `q`, `E M = m`, `E δ = 0` and `E δ² ≤ θ q(1 − q) m` at the rank `k`, `Var M ≤ D m` and
`P(M ≤ M') ≤ T M'` for `M' < M1` has no weak valley at `k`. -/
def NoValleyAt (q m θ D : ℝ) (T : ℕ → ℝ) (M1 : ℕ) : Prop :=
  ∀ (ι : Type) (X : Mixture ι) (k : ℤ), X.IsProb → X.meanM = m →
    X.expect (fun M Y => delta q k M Y) = 0 →
    X.expect (fun M Y => delta q k M Y ^ 2) ≤ θ * (q * (1 - q)) * m →
    X.varM ≤ D * m →
    (∀ M' : ℕ, M' < M1 → X.cdfM M' ≤ T M') →
    ¬ X.WeakValley q k

/-- **T1's explicit threshold condition** (T1 Theorem 3.1, Lemma 5.1 and Theorem 6.1, with the fibre
function `h` abstract).  There are a `δ²`-multiplier `ν > 0` (`a μ̃` in T1), a `δ`-multiplier `c`, a
fibre lower bound `h` (pointwise below `κ + cδ + νδ²`; T1 Props 4.2/4.3 supply one), a quadratic
minorant `π(M) = α + β(M − m) − γ(M − m)²` of `h` from `M1` on, and nonnegative nonincreasing tail
prices `S ≥ π − h` below `M1`, such that
`ν θ q(1 − q) m < α − γ D m − ∑_{M' < M1} S(M') (T(M') − T(M' − 1))` (with `T(−1) = 0`). -/
def ExplicitThreshold (q m θ D : ℝ) (T : ℕ → ℝ) (M1 : ℕ) : Prop :=
  ∃ (ν c α β γ : ℝ) (h S : ℕ → ℝ), 0 < ν ∧ 0 ≤ γ ∧
    (∀ (M : ℕ) (j : ℤ),
      h M ≤ kappa q M j + c * ((j : ℝ) - q * M) + ν * ((j : ℝ) - q * M) ^ 2) ∧
    (∀ M : ℕ, M1 ≤ M → α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 ≤ h M) ∧
    (∀ M : ℕ, M < M1 → α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 - h M ≤ S M) ∧
    (∀ M : ℕ, M < M1 → 0 ≤ S M) ∧
    (∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M) ∧
    ν * θ * (q * (1 - q)) * m <
      α - γ * D * m - ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1))

/-- **T1's no-valley lemma in Lean form** (proved in `NoValley/Core.lean`): the explicit threshold condition
implies the no-valley property. -/
def T1Core : Prop :=
  ∀ (q m θ D : ℝ) (T : ℕ → ℝ) (M1 : ℕ), 0 < q → q < 1 →
    ExplicitThreshold q m θ D T M1 → NoValleyAt q m θ D T M1

/-! ## The hard-core model of a forest and its mixture over an independent set -/

variable (F : FiniteForest)

/-- The independent sets of `F`. -/
noncomputable def indepSets : Finset (Finset (Fin F.n)) := by
  classical
  exact univ.filter fun S : Finset (Fin F.n) => F.graph.IsIndepSet (S : Set (Fin F.n))

/-- The hard-core marginal `π_v(t) = P(v ∈ S)` at activity `t`. -/
noncomputable def marginal (t : ℝ) (v : Fin F.n) : ℝ := by
  classical
  exact (∑ S ∈ (indepSets F).filter (fun S => v ∈ S), t ^ S.card) / partitionFn F t

/-- Zhang's weight `W = ∑_{b ∈ B} π_b`. -/
noncomputable def weightW (t : ℝ) (B : Finset (Fin F.n)) : ℝ := ∑ b ∈ B, marginal F t b

/-- The variance `V = Var K` of the size of the hard-core set at activity `t`. -/
noncomputable def hardCoreVar (t : ℝ) : ℝ :=
  (∑ k ∈ range (F.n + 1),
      ((k : ℝ) - hardCoreMean F t) ^ 2 * (independenceCount F k : ℝ) * t ^ k) / partitionFn F t

/-- `B` is a maximum-weight independent set at activity `t` (Zhang's choice in (45)). -/
def IsMaxWeight (t : ℝ) (B : Finset (Fin F.n)) : Prop :=
  F.graph.IsIndepSet (B : Set (Fin F.n)) ∧
    ∀ B' : Finset (Fin F.n), F.graph.IsIndepSet (B' : Set (Fin F.n)) →
      weightW F t B' ≤ weightW F t B

/-- The free count `M(σ) = #{b ∈ B : b has no neighbour in σ}`. -/
noncomputable def freeCount (B σ : Finset (Fin F.n)) : ℕ := by
  classical
  exact (B.filter fun b => ∀ c ∈ σ, ¬ F.graph.Adj b c).card

/-- **The conditional binomial mixture (Zhang (45))** of the hard-core model of `F` at activity
`t`, relative to an independent set `B`: states are the independent subsets `σ` of `C = Bᶜ`, with
weight `t^|σ| (1 + t)^(M σ) / Z_F(t)`, `Y σ = |σ|` and `M σ = freeCount F B σ`. -/
noncomputable def forestMixture (B : Finset (Fin F.n)) (t : ℝ) : Mixture (Finset (Fin F.n)) := by
  classical
  exact
    { S := (univ \ B).powerset.filter fun σ => F.graph.IsIndepSet (σ : Set (Fin F.n))
      w := fun σ => t ^ σ.card * (1 + t) ^ freeCount F B σ / partitionFn F t
      M := freeCount F B
      Y := Finset.card }

/-- **The facts about the forest mixture that the assembly uses** (Zhang (45)–(46); PROVED ON PAPER;
proved in Lean in `HardCore/Mixture.lean`). -/
structure MixtureFacts : Prop where
  exists_maxWeight : ∀ (F : FiniteForest) (t : ℝ), 0 < t → ∃ B, IsMaxWeight F t B
  isProb : ∀ (F : FiniteForest) (t : ℝ) (B : Finset (Fin F.n)), 0 < t →
    F.graph.IsIndepSet (B : Set (Fin F.n)) → (forestMixture F B t).IsProb
  prob_eq : ∀ (F : FiniteForest) (t : ℝ) (B : Finset (Fin F.n)), 0 < t →
    F.graph.IsIndepSet (B : Set (Fin F.n)) → ∀ i : ℕ,
      (forestMixture F B t).prob (actQ t) i = (independenceCount F i : ℝ) * t ^ i / partitionFn F t
  mean_delta : ∀ (F : FiniteForest) (t : ℝ) (B : Finset (Fin F.n)), 0 < t →
    F.graph.IsIndepSet (B : Set (Fin F.n)) → ∀ k : ℕ, hardCoreMean F t = k →
      (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y) = 0
  var_delta : ∀ (F : FiniteForest) (t : ℝ) (B : Finset (Fin F.n)), 0 < t →
    F.graph.IsIndepSet (B : Set (Fin F.n)) → ∀ k : ℕ, hardCoreMean F t = k →
      (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y ^ 2) =
        hardCoreVar F t - actQ t * (1 - actQ t) * (forestMixture F B t).meanM
  weight_eq : ∀ (F : FiniteForest) (t : ℝ) (B : Finset (Fin F.n)), 0 < t →
    F.graph.IsIndepSet (B : Set (Fin F.n)) →
      actQ t * (forestMixture F B t).meanM = weightW F t B

/-! ## The open analytic inputs -/

/-- The activity range of the route: `[1/3, 7/3]` (top activity `7/3`, B5). -/
def InRange (t : ℝ) : Prop := 1 / 3 ≤ t ∧ t ≤ 7 / 3

/-- The quantitative profile carried between the inputs and the threshold numerics.  Each field
summarizes one object (scalarity check): `θb` bounds the second moment of `δ` (through
`V ≤ (1 + θ)(1 − q) W`), `Db` the variance of the free count `M`, `Tb` the lower tail of `M` (from
the Laplace transform of `M`), `M1b` the tail cutoff, `mfloor` the expected free count `m = E M`
(a lower bound valid at every interior rank of every forest with `n ≥ 61`).
Their consumer is the no-valley lemma (`ThresholdNumerics`). -/
structure Profile where
  /-- variance-ratio bound `θ(λ)` (O2) -/
  θb : ℝ → ℝ
  /-- variance bound `D(λ)`: `Var M ≤ D m` (O1) -/
  Db : ℝ → ℝ
  /-- lower-tail bound `T(λ, m, M') ≥ P(M ≤ M')` (O3) -/
  Tb : ℝ → ℝ → ℕ → ℝ
  /-- tail cutoff `M1(λ, m)`: the tail bound is used for `M' < M1` (O3, O4) -/
  M1b : ℝ → ℝ → ℕ
  /-- the floor of the expected free count: `m ≥ mfloor(λ)` at every interior integer-mean rank of
  every forest with `n ≥ 61` (O5) -/
  mfloor : ℝ → ℝ

/-- The activity `t` puts the hard-core mean of `F` exactly at an interior window rank:
`μ_F(t) = k` for an integer `⌈n/4⌉ < k < h_B` (the ranks at which the route excludes a weak valley;
open object O6, option (b)).  The inputs O1–O3 and O5
are needed only at such activities. -/
def AtInteriorRank (F : FiniteForest) (t : ℝ) : Prop :=
  ∃ k : ℕ, (F.n + 3) / 4 < k ∧ k < hB F ∧ hardCoreMean F t = k

variable (P : Profile)

/-- **O1 (the variance bound, T1's (H2)).** `Var M ≤ D(λ) m` for every forest with `n ≥ 61`, every
activity in range at an interior rank (`AtInteriorRank`) and every maximum-weight independent set. -/
def VarianceBound : Prop :=
  ∀ F : FiniteForest, 61 ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    (forestMixture F B t).varM ≤ P.Db t * (forestMixture F B t).meanM

/-- **O2 (the variance-ratio bound, T1's (H1)).** `V ≤ (1 + θ(λ)) (1 − q) W`, i.e.
`E δ² ≤ θ(λ) q(1 − q) m` (Zhang (46) and `qm = W`). -/
def VarianceRatioBound : Prop :=
  ∀ F : FiniteForest, 61 ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    hardCoreVar F t ≤ (1 + P.θb t) * (1 - actQ t) * weightW F t B

/-- **O3 (the tail input, T1's (H3)).** `P(M ≤ M') ≤ T(λ, m, M')` for `M' < M1(λ, m)`. -/
def TailBound : Prop :=
  ∀ F : FiniteForest, 61 ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    ∀ M' : ℕ, M' < P.M1b t (forestMixture F B t).meanM →
      (forestMixture F B t).cdfM M' ≤ P.Tb t (forestMixture F B t).meanM M'

/-- **O5 (the floor of the expected free count).** `m ≥ mfloor(λ)` at every interior rank of every
forest with `n ≥ 61`.  (Not a homogeneous density `m ≥ ρ n`: the valid floors use the integer rank
`k ≥ ⌈n/4⌉ + 1`, `W ≥ μ/2 = k/2`, `m = W/q` and certified affine density records.)
-/
def DensityBound : Prop :=
  ∀ F : FiniteForest, 61 ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    P.mfloor t ≤ (forestMixture F B t).meanM

/-- **O4 (the threshold numerics).** T1's explicit threshold condition holds at every activity in
range and every `m ≥ mfloor(λ)`. -/
def ThresholdNumerics : Prop :=
  ∀ t : ℝ, InRange t → ∀ m : ℝ, P.mfloor t ≤ m →
    ExplicitThreshold (actQ t) m (P.θb t) (P.Db t) (P.Tb t m) (P.M1b t m)

/-- **O4 (the no-valley property on the whole parameter domain).** At every activity in range and
every `m ≥ mfloor(λ)`, every probability mixture with the moment and tail inputs of the profile has no
weak valley at its rank.  Two routes discharge it: on bounded `m`, T1 (`T1Core`) applied to the
threshold numerics (`ThresholdNumerics`, `thresholdNoValley_of_numerics`); on large `m`, a
large-mean no-valley theorem (a binomial Fourier estimate). -/
def ThresholdNoValley : Prop :=
  ∀ t : ℝ, InRange t → ∀ m : ℝ, P.mfloor t ≤ m →
    NoValleyAt (actQ t) m (P.θb t) (P.Db t) (P.Tb t m) (P.M1b t m)

/-- **The open analytic content of the route**, one field per open object (O1–O5; O6 is decided
by option (b) and proved in Lean from B5). -/
structure AnalyticInputs : Prop where
  o1 : VarianceBound P
  o2 : VarianceRatioBound P
  o3 : TailBound P
  o4 : ThresholdNoValley P
  o5 : DensityBound P

end Erdos993Lean.Analytic
