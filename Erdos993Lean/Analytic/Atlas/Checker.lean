module


/-!
# The O4 atlas checker: Boolean checks in exact rational arithmetic

Sources: the atlas proof and the parameter-box proof of the O4 threshold numerics,
and their interval-arithmetic verifier (`uniform_slack`, `certify_box`,
`cover_check`), whose first-order q-uniform bound is re-evaluated here **exactly** (the saved duals are
tight: after the alpha adjustment the worst atoms have slack `10⁻¹²` under that very formula).

This file imports only Lean's core (no Mathlib).



## A box

`q ∈ [ql, qh]`, `m ∈ [ml, mh]`, q-midpoint `q0`, half-width `rad = (qh − ql)/2`; the rational dual
`μ, c, α, β, γ, z_0, z_1, …` centred at `m0` (the box midpoint); `π(M) = α + β(M − m0) − γ(M − m0)²`;
the fibre bound `rhs(M) = π(M) − ∑_{r ≥ M} z_r`.  The checker's hints: the explicit cutoff `N` and
`cm ≤ ⌈ml⌉`.  Since the pointwise checks do not involve `[ml, mh]`, a box may be split in `m` into
pieces keeping the dual and its centre `m0` (the margin (2) is then checked on each piece).

## The checks of a box (`boxOK`)

* `sane`: `0 < ql < qh < 1`, `μ > 0`, `γ > 0`, `z ≥ 0`, `ml ≤ mh`, `cm − 1 < ml`.
* `fibresAll`: for every fibre `M < N`
  - (outside) `rhs(M)` is below the minimum of `μx² + cx` on `(−∞, −2 − ql·M]` and on
    `[M + 2 − qh·M, ∞)` (the kernel vanishes for `j ≤ −2` and `j ≥ M + 2`);
  - (atoms) for `−1 ≤ j ≤ M + 1`, unless the atom skips (`κ ≥ −B` by the Fourier bound for
    `vmin·M ≥ 25`, else `|κ| ≤ 1/vmin`, and `μ(δ + c/(2μ))² ≥ rhs + B + c²/(4μ)` on a verified range),
    the first-order bound: `rhs(M) ≤ κ_{q0}(M, j) − rad·K + qmin`, with
    `K = W_max (|P'|_max + |L|_max |P|_max)` (`0 ≤ j ≤ M`), `K = M(1 − ql)^{M−1}` (`j = −1`),
    `K = M qh^{M−1}` (`j = M + 1`), and `qmin` the exact minimum of `μδ² + cδ` on
    `δ ∈ [j − qh·M, j − ql·M]`; or else the second-order bound (used
    by the upper atlas): `rhs(M) ≤ h(q0) − rad |h'(q0)| − (rad²/2)(K₂ + 2μM²)` with `h = κ + cδ + μδ²`,
    `K₂ = W_max (|P''| + 2|L|_max |P'|_max + (|L|²_max + |L'|_max) |P|_max)` bounding `|κ''|`.  The
    binomial rows at `ql, q0, qh` are carried along `M` as integer rows `N_M(j) = r^M b_M(j; p/r)` by the
    Pascal recurrence `N_{M+1}(j) = (r − p) N_M(j) + p N_M(j − 1)`.
* `tailOK` (every fibre `M ≥ N`): `25 ≤ u := vmin·N`, `π(N) ≤ −(1/(20u) + 1/u²) − c²/(4μ)` and
  `β − 2γ(N − m0) ≤ 0` (the Fourier bound `κ ≥ −(1/(20u) + 1/u²)` for `u = M q(1 − q) ≥ 25`).
* `marginQ > 0`: the expectation margin (2) with the tail bound
  `T̂_r = min(1, min_k U_k ((1 + Λ)/(1 + Λ t_k))^r)` for `r ≤ cm` and `T̂_r = 1` for `r > cm`,
  `U_k = 1/∑_{i < 120} x^i/i! ≥ e^{−x}` at `x = ℓ_k·ml`.  `Λ` is a parameter (the activity whose
  tail base is used).

## The cover (`coverOK`)

Consecutive q-slabs from `qlo` to `qhi`; per slab a chain of boxes containing the slab whose
m-intervals chain from `mlo` to `mhi`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Atlas

/-! ## Rational helpers -/

/-- `|x|` on `Rat`. -/
def qabs (x : Rat) : Rat := if x < 0 then -x else x

/-- `max a b` on `Rat`. -/
def qmax (a b : Rat) : Rat := if a ≤ b then b else a

/-- `min a b` on `Rat`. -/
def qmin (a b : Rat) : Rat := if a ≤ b then a else b

/-- The sum of a list. -/
def sumList : List Rat → Rat
  | [] => 0
  | x :: xs => x + sumList xs

/-! ## Boxes, bands, slabs -/

/-- One atlas box with the rational dual (centred at `m0`) and the checker's hints `N`, `cm`. -/
structure Box where
  ql : Rat
  qh : Rat
  ml : Rat
  mh : Rat
  /-- the centre of the dual's quadratic minorant (the box midpoint; a half of a split box keeps
  the centre of the original box) -/
  m0 : Rat
  mu : Rat
  c : Rat
  alpha : Rat
  beta : Rat
  gamma : Rat
  z : List Rat
  N : Nat
  cm : Nat

/-- The parameters of one activity band `[λ_i, λ_{i+1}]`: the targets `D`, `θ`, the five certified
rates `ℓ_k` (Laplace parameters `t_k ∈ {0, 1/20, 1/10, 1/5, 3/10}`), the band edges and the floor of `m`. -/
structure Band where
  D : Rat
  theta : Rat
  ell : List Rat
  lamLo : Rat
  lamHi : Rat
  mmin : Rat

/-- The Laplace parameters `t_k` of O3. -/
def tvals : List Rat := [0, 1/20, 1/10, 1/5, 3/10]

/-- A q-slab `[lo, hi]` and the chain of box indices covering it in `m`. -/
structure Slab where
  lo : Rat
  hi : Rat
  chain : List Nat

namespace Box

variable (b : Box)

/-- The q-midpoint. -/
def q0 : Rat := (b.ql + b.qh) / 2

/-- The q-half-width. -/
def rad : Rat := (b.qh - b.ql) / 2

/-- The quadratic minorant `π(M) = α + β(M − m0) − γ(M − m0)²`. -/
def piQ (M : Nat) : Rat :=
  b.alpha + b.beta * ((M : Rat) - b.m0) - b.gamma * (((M : Rat) - b.m0) * ((M : Rat) - b.m0))

/-- `∑_{r ≥ M} z_r`. -/
def tailSum (M : Nat) : Rat := sumList (b.z.drop M)

/-- The fibre bound `rhs(M) = π(M) − ∑_{r ≥ M} z_r`. -/
def rhs (M : Nat) : Rat := b.piQ M - b.tailSum M

end Box

/-! ## The quadratic `μx² + cx` -/

/-- `μx² + cx`. -/
def quadV (mu c x : Rat) : Rat := mu * (x * x) + c * x

/-- `μx² + cx` at the clamp of the vertex `−c/(2μ)` to `[lo, hi]` (its minimum there, `μ > 0`). -/
def quadMinI (mu c lo hi : Rat) : Rat :=
  quadV mu c (if -c / (2 * mu) < lo then lo else if hi < -c / (2 * mu) then hi else -c / (2 * mu))

/-- The minimum of `μx² + cx` on `(−∞, a]` (`μ > 0`). -/
def quadMinLeft (mu c a : Rat) : Rat :=
  quadV mu c (if a < -c / (2 * mu) then a else -c / (2 * mu))

/-- The minimum of `μx² + cx` on `[a, ∞)` (`μ > 0`). -/
def quadMinRight (mu c a : Rat) : Rat :=
  quadV mu c (if -c / (2 * mu) < a then a else -c / (2 * mu))

/-! ## Binomial rows -/

/-- A rational `q = p/r ∈ [0, 1]` as naturals: `p = num`, `s = r − p`, `r = den`. -/
structure Zq where
  p : Nat
  s : Nat
  r : Nat

/-- The natural representation of `q`. -/
def zq (q : Rat) : Zq := ⟨q.num.toNat, q.den - q.num.toNat, q.den⟩

/-- One step of the integer binomial row of `q = p/r`: `N_{M+1}(j) = s N_M(j) + p N_M(j − 1)`, so that
`N_M(j) = C(M, j) p^j s^{M−j} = r^M b_M(j; q)` (no normalisation). -/
def zrowStep (z : Zq) (row : Array Nat) : Array Nat :=
  Array.ofFn (n := row.size + 1) fun i =>
    z.s * row.getD i.val 0 + z.p * (if i.val = 0 then 0 else row.getD (i.val - 1) 0)

/-- `b_M(j; q) = N_M(j)/r^M` from the integer row and `rM = r^M`. -/
def bval (row : Array Nat) (rM : Nat) (j : Nat) : Rat := (row.getD j 0 : Rat) / (rM : Rat)

/-- One step of Pascal's triangle. -/
def pascalStep (row : Array Nat) : Array Nat :=
  Array.ofFn (n := row.size + 1) fun i =>
    row.getD i.val 0 + (if i.val = 0 then 0 else row.getD (i.val - 1) 0)

/-! ## The atoms of one fibre -/

/-- The polynomial `P(x) = a(1 − x)² + b x²` with `a = (M + 1 − 2j)/(M − j + 1)`, `b = (2j + 1 − M)/(j + 1)`. -/
def coefA (M j : Nat) : Rat := ((M : Rat) + 1 - 2 * (j : Rat)) / ((M : Rat) - (j : Rat) + 1)

/-- See `coefA`. -/
def coefB (M j : Nat) : Rat := (2 * (j : Rat) + 1 - (M : Rat)) / ((j : Rat) + 1)

/-- `P(x) = a(1 − x)² + b x²`. -/
def pval (a bb x : Rat) : Rat := a * ((1 - x) * (1 - x)) + bb * (x * x)

/-- `P'(x) = −2a + 2(a + b)x`. -/
def dpval (a bb x : Rat) : Rat := -2 * a + 2 * (a + bb) * x

/-- `|P|_max` on `[ql, qh]`: the endpoints and the vertex `a/(a + b)` when interior. -/
def pabs (a bb ql qh : Rat) : Rat :=
  if a + bb ≠ 0 ∧ ql < a / (a + bb) ∧ a / (a + bb) < qh then
    qmax (qmax (qabs (pval a bb ql)) (qabs (pval a bb qh))) (qabs (pval a bb (a / (a + bb))))
  else qmax (qabs (pval a bb ql)) (qabs (pval a bb qh))

/-- `|P'|_max` on `[ql, qh]` (`P'` is linear). -/
def dpabs (a bb ql qh : Rat) : Rat := qmax (qabs (dpval a bb ql)) (qabs (dpval a bb qh))

/-- `L(x) = (j − 1)/u − (M − j − 1)/(1 − v)` at `u, v ∈ {ql, qh}`: a bound of `|W'/W|` on `[ql, qh]`. -/
def lcomb (M j : Nat) (u v : Rat) : Rat := ((j : Rat) - 1) / u - ((M : Rat) - (j : Rat) - 1) / (1 - v)

/-- `|L|_max` on `[ql, qh]` (reciprocal ranges). -/
def labs (M j : Nat) (ql qh : Rat) : Rat :=
  qmax (qmax (qabs (lcomb M j ql ql)) (qabs (lcomb M j ql qh)))
    (qmax (qabs (lcomb M j qh ql)) (qabs (lcomb M j qh qh)))

/-- The stationary point `(j − 1)/(M − 2)` of `W`. -/
def star (M j : Nat) : Rat := ((j : Rat) - 1) / ((M : Rat) - 2)

/-- `W_max` on `[ql, qh]`: `W(x) = b_M(j; x)/(x(1 − x))` at the endpoints (binomial values `fl`, `fh`)
and at the interior stationary point (with the binomial coefficient from Pascal's row). -/
def wmax (M j : Nat) (ql qh : Rat) (fl fh : Nat → Rat) (pas : Array Nat) : Rat :=
  if M ≠ 2 ∧ ql < star M j ∧ star M j < qh then
    qmax (qmax (fl j / (ql * (1 - ql))) (fh j / (qh * (1 - qh))))
      ((pas.getD j 0 : Rat) * star M j ^ j * (1 - star M j) ^ (M - j) / (star M j * (1 - star M j)))
  else qmax (fl j / (ql * (1 - ql))) (fh j / (qh * (1 - qh)))

/-- `κ_{q}(M, j) = b(j) ((1 − q)/q + q/(1 − q)) − b(j − 1) − b(j + 1)` from the binomial values `f` at `q`. -/
def kapRow (q : Rat) (j : Nat) (f : Nat → Rat) : Rat :=
  f j * ((1 - q) / q + q / (1 - q)) - (if j = 0 then 0 else f (j - 1)) - f (j + 1)

/-- `|L'|_max = |j − 1|/ql² + |M − j − 1|/(1 − qh)²` on `[ql, qh]`. -/
def lpabs (M j : Nat) (ql qh : Rat) : Rat :=
  qabs ((j : Rat) - 1) / (ql * ql) + qabs ((M : Rat) - (j : Rat) - 1) / ((1 - qh) * (1 - qh))

/-- The second-order alternative: with `h(q) = κ_q + cδ + μδ²`,
`h(q0) − rad |h'(q0)| − (rad²/2) (|κ''|_max + 2μM²)`, the value and slope at `q0` exact, `δ0 = j − q0 M`. -/
def joint (b : Box) (M : Nat) (j : Int) (kap k1 k2 : Rat) : Rat :=
  let d0 := (j : Rat) - b.q0 * (M : Rat)
  kap + (b.mu * (d0 * d0) + b.c * d0) - b.rad * qabs (k1 - (M : Rat) * (b.c + 2 * b.mu * d0)) -
    b.rad * b.rad * (k2 + 2 * b.mu * ((M : Rat) * (M : Rat))) / 2

/-- The atom `(M, j)`, `0 ≤ j ≤ M`: the first-order bound, or else the second-order one. -/
def atomMid (b : Box) (M j : Nat) (fl f0 fh : Nat → Rat) (pas : Array Nat) (rhs : Rat) : Bool :=
  let a := coefA M j
  let bb := coefB M j
  let wm := wmax M j b.ql b.qh fl fh pas
  let pa := pabs a bb b.ql b.qh
  let dp := dpabs a bb b.ql b.qh
  let la := labs M j b.ql b.qh
  decide (rhs ≤ kapRow b.q0 j f0 - b.rad * (wm * (dp + la * pa)) +
    quadMinI b.mu b.c ((j : Rat) - b.qh * (M : Rat)) ((j : Rat) - b.ql * (M : Rat))) ||
  decide (rhs ≤ joint b M (j : Int) (kapRow b.q0 j f0)
    (f0 j / (b.q0 * (1 - b.q0)) * (dpval a bb b.q0 + lcomb M j b.q0 b.q0 * pval a bb b.q0))
    (wm * (qabs (2 * (a + bb)) + 2 * la * dp + (la * la + lpabs M j b.ql b.qh) * pa)))

/-- The atom `(M, −1)`: `κ = −(1 − q)^M`, `|κ'| ≤ M(1 − ql)^{M−1}`, `|κ''| ≤ M(M − 1)(1 − ql)^{M−2}`. -/
def atomNeg (b : Box) (M : Nat) (rhs : Rat) : Bool :=
  decide (rhs ≤ -((1 - b.q0) ^ M) - b.rad * ((M : Rat) * (1 - b.ql) ^ (M - 1)) +
    quadMinI b.mu b.c (-1 - b.qh * (M : Rat)) (-1 - b.ql * (M : Rat))) ||
  decide (rhs ≤ joint b M (-1) (-((1 - b.q0) ^ M)) ((M : Rat) * (1 - b.q0) ^ (M - 1))
    ((M : Rat) * ((M : Rat) - 1) * (1 - b.ql) ^ (M - 2)))

/-- The atom `(M, M + 1)`: `κ = −q^M`, `|κ'| ≤ M qh^{M−1}`, `|κ''| ≤ M(M − 1) qh^{M−2}`. -/
def atomTop (b : Box) (M : Nat) (rhs : Rat) : Bool :=
  decide (rhs ≤ -(b.q0 ^ M) - b.rad * ((M : Rat) * b.qh ^ (M - 1)) +
    quadMinI b.mu b.c ((M : Rat) + 1 - b.qh * (M : Rat)) ((M : Rat) + 1 - b.ql * (M : Rat))) ||
  decide (rhs ≤ joint b M ((M : Int) + 1) (-(b.q0 ^ M)) (-((M : Rat) * b.q0 ^ (M - 1)))
    ((M : Rat) * ((M : Rat) - 1) * b.qh ^ (M - 2)))

/-- The atom at the integer `j ∈ [−1, M + 1]`. -/
def atomAt (b : Box) (M : Nat) (fl f0 fh : Nat → Rat) (pas : Array Nat) (rhs : Rat) (j : Int) : Bool :=
  if j = -1 then atomNeg b M rhs
  else if j = (M : Int) + 1 then atomTop b M rhs
  else atomMid b M j.toNat fl f0 fh pas rhs

/-- The atoms `lo, lo + 1, …, lo + k − 1`. -/
def atomsFrom (b : Box) (M : Nat) (fl f0 fh : Nat → Rat) (pas : Array Nat) (rhs : Rat) :
    Int → Nat → Bool
  | _, 0 => true
  | lo, k + 1 => atomAt b M fl f0 fh pas rhs lo && atomsFrom b M fl f0 fh pas rhs (lo + 1) k

/-- The kernel lower bound `κ ≥ −B` at the fibre `M`: the Fourier bound for `u = vmin·M ≥ 25`, else
`|κ| ≤ 1/(q(1 − q)) ≤ 1/vmin`. -/
def kapB (b : Box) (M : Nat) : Rat :=
  if 25 ≤ qmin (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh)) * (M : Rat) then
    1 / (20 * (qmin (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh)) * (M : Rat))) +
      1 / ((qmin (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh)) * (M : Rat)) *
        (qmin (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh)) * (M : Rat)))
  else 1 / qmin (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh))

/-- The vertex `−c/(2μ)` of `μδ² + cδ`. -/
def vtx (b : Box) : Rat := -b.c / (2 * b.mu)

/-- `rhs + B + c²/(4μ)`: an atom with `μ(δ − vtx)² ≥` this level needs no binomial value
(`κ + cδ + μδ² ≥ −B + μ(δ − vtx)² − c²/(4μ)`). -/
def skipLev (b : Box) (M : Nat) (rhs : Rat) : Rat := rhs + kapB b M + b.c * b.c / (4 * b.mu)

/-- The distance `ql·M + vtx − (jlo − 1)` covered on the left of `jlo`. -/
def leftY (b : Box) (M : Nat) (jlo : Int) : Rat := b.ql * (M : Rat) + vtx b - ((jlo : Rat) - 1)

/-- The distance `(jhi + 1) − qh·M − vtx` covered on the right of `jhi`. -/
def rightY (b : Box) (M : Nat) (jhi : Int) : Rat := ((jhi : Rat) + 1) - b.qh * (M : Rat) - vtx b

/-- A radius `R ≥ √(lev/μ)` (heuristic; the skip conditions are verified exactly). -/
def skipRad (b : Box) (lev : Rat) : Int :=
  ((Float.ofInt (Rat.ceil (lev / b.mu))).sqrt.ceil.toUInt64.toNat : Int) + 1

/-- The first enumerated atom: `jlo` if the left skip condition holds there, else `−1`. -/
def jloOf (b : Box) (M : Nat) (lev : Rat) : Int :=
  let jlo := Rat.floor (b.ql * (M : Rat) + vtx b) - skipRad b lev
  if decide (0 ≤ leftY b M jlo) && decide (lev ≤ b.mu * (leftY b M jlo * leftY b M jlo)) then max jlo (-1)
  else -1

/-- The last enumerated atom: `jhi` if the right skip condition holds there, else `M + 1`. -/
def jhiOf (b : Box) (M : Nat) (lev : Rat) : Int :=
  let jhi := Rat.ceil (b.qh * (M : Rat) + vtx b) + skipRad b lev
  if decide (0 ≤ rightY b M jhi) && decide (lev ≤ b.mu * (rightY b M jhi * rightY b M jhi)) then
    min jhi ((M : Int) + 1)
  else (M : Int) + 1

/-- The whole fibre `M` (binomial values `fl`, `f0`, `fh` at `ql`, `q0`, `qh`): the half-lines, then either
every atom skips (`lev ≤ 0`) or the atoms between `jloOf` and `jhiOf` are checked (the others skip). -/
def fibreOK (b : Box) (M : Nat) (fl f0 fh : Nat → Rat) (pas : Array Nat) : Bool :=
  let rhs := b.rhs M
  let lev := skipLev b M rhs
  decide (rhs ≤ quadMinLeft b.mu b.c (-2 - b.ql * (M : Rat))) &&
  decide (rhs ≤ quadMinRight b.mu b.c ((M : Rat) + 2 - b.qh * (M : Rat))) &&
  (decide (lev ≤ 0) ||
    atomsFrom b M fl f0 fh pas rhs (jloOf b M lev) (jhiOf b M lev - jloOf b M lev + 1).toNat)

/-- The fibres `M, M + 1, …, M + k − 1`, carrying the integer rows at `ql, q0, qh`, the powers `r^M` and
Pascal's row. -/
def fibresLoop (b : Box) (zl z0 zh : Zq) : Nat → Nat → Array Nat → Array Nat → Array Nat →
    Nat → Nat → Nat → Array Nat → Bool
  | 0, _, _, _, _, _, _, _, _ => true
  | k + 1, M, rl, r0, rh, rlM, r0M, rhM, pas =>
    fibreOK b M (bval rl rlM) (bval r0 r0M) (bval rh rhM) pas &&
      fibresLoop b zl z0 zh k (M + 1) (zrowStep zl rl) (zrowStep z0 r0) (zrowStep zh rh)
        (rlM * zl.r) (r0M * z0.r) (rhM * zh.r) (pascalStep pas)

/-- Every fibre `M < N`. -/
def fibresAll (b : Box) : Bool :=
  fibresLoop b (zq b.ql) (zq b.q0) (zq b.qh) b.N 0 #[1] #[1] #[1] 1 1 1 #[1]

/-! ## The tail `M ≥ N`, the sanity checks and the margin -/

/-- `min(ql(1 − ql), qh(1 − qh))`. -/
def Box.vmin (b : Box) : Rat := qmin (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh))

/-- `max_{q ∈ [ql, qh]} q(1 − q)`. -/
def Box.vmax (b : Box) : Rat :=
  if b.ql ≤ 1 / 2 ∧ 1 / 2 ≤ b.qh then 1 / 4 else qmax (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh))

/-- The fibres `M ≥ N` by the Fourier bound (`u ≥ 25`) and monotonicity. -/
def tailOK (b : Box) : Bool :=
  decide (25 ≤ b.vmin * (b.N : Rat)) &&
  decide (b.piQ b.N ≤
    -(1 / (20 * (b.vmin * (b.N : Rat))) + 1 / ((b.vmin * (b.N : Rat)) * (b.vmin * (b.N : Rat)))) -
      b.c * b.c / (4 * b.mu)) &&
  decide (b.beta - 2 * b.gamma * ((b.N : Rat) - b.m0) ≤ 0)

/-- Sanity of the data. -/
def sane (b : Box) : Bool :=
  decide (0 < b.ql) && decide (b.ql < b.qh) && decide (b.qh < 1) && decide (0 < b.mu) &&
  decide (0 < b.gamma) && b.z.all (fun x => decide (0 ≤ x)) && decide (0 < b.ml) &&
  decide (b.ml ≤ b.mh) && decide ((b.cm : Rat) < b.ml + 1)

/-- `∑_{i < n} x^i/i!` (`n` terms). -/
def expPartial (x : Rat) : Nat → Rat
  | n => (go n 0 1 0).2
where
  /-- `go k i term acc`: add `k` more terms, `term = x^i/i!`. -/
  go : Nat → Nat → Rat → Rat → Rat × Rat
    | 0, _, term, acc => (term, acc)
    | k + 1, i, term, acc => go k (i + 1) (term * x / ((i : Rat) + 1)) (acc + term)

/-- The rational upper bound `1/∑_{i < 120} x^i/i!` of `e^{−x}` (`x ≥ 0`). -/
def expNegUpper (x : Rat) : Rat := 1 / expPartial x 120

/-- The five upper bounds `U_k ≥ e^{−ℓ_k ml}`. -/
def uList (band : Band) (ml : Rat) : List Rat :=
  (List.range 5).map fun k => expNegUpper (band.ell.getD k 0 * ml)

/-- The tail bound `T̂_r = min(1, min_k U_k ((1 + Λ)/(1 + Λ t_k))^r)`. -/
def tailHat (U : List Rat) (Λ : Rat) (r : Nat) : Rat :=
  (List.range 5).foldl (fun acc k =>
    qmin acc (U.getD k 0 * ((1 + Λ) / (1 + Λ * tvals.getD k 0)) ^ r)) 1

/-- The tail cost `∑_r z_r T̂'_r` with `T̂'_r = T̂_r` for `r ≤ cm` and `1` beyond. -/
def costFrom (U : List Rat) (Λ : Rat) (cm : Nat) : Nat → List Rat → Rat
  | _, [] => 0
  | r, x :: xs => x * (if r ≤ cm then tailHat U Λ r else 1) + costFrom U Λ cm (r + 1) xs

/-- The expectation margin (2), with the tail cost `costFrom`. -/
def marginQ (band : Band) (Λ : Rat) (b : Box) : Rat :=
  b.alpha + qmin (b.beta * (b.ml - b.m0)) (b.beta * (b.mh - b.m0)) -
    b.gamma * (band.D * b.mh + qmax ((b.ml - b.m0) * (b.ml - b.m0)) ((b.mh - b.m0) * (b.mh - b.m0))) -
    b.mu * band.theta * b.vmax * b.mh - costFrom (uList band b.ml) Λ b.cm 0 b.z

/-- **All checks of one box**, with the tail base activity `Λ ≥ 0`. -/
def boxOK (band : Band) (Λ : Rat) (b : Box) : Bool :=
  sane b && decide (0 ≤ Λ) && tailOK b && decide (0 < marginQ band Λ b) && fibresAll b

/-! ## The cover -/

/-- The boxes of `chain` contain the q-slab `[lo, hi]` and their m-intervals cover `[s, target]`. -/
def chainOK (boxes : List Box) (lo hi : Rat) : Rat → Rat → List Nat → Bool
  | _, _, [] => false
  | s, target, i :: rest =>
    match boxes[i]? with
    | some b =>
      decide (b.ql ≤ lo) && decide (hi ≤ b.qh) && decide (b.ml ≤ s) &&
        (decide (target ≤ b.mh) || chainOK boxes lo hi b.mh target rest)
    | none => false

/-- The slabs cover `[start, qhi]` in `q`, each on `[mlo, mhi]` in `m`. -/
def slabsOK (boxes : List Box) (qhi mlo mhi : Rat) : Rat → List Slab → Bool
  | _, [] => false
  | start, sl :: rest =>
    decide (sl.lo ≤ start) && chainOK boxes sl.lo sl.hi mlo mhi sl.chain &&
      (decide (qhi ≤ sl.hi) || slabsOK boxes qhi mlo mhi sl.hi rest)

/-- **The cover of `[qlo, qhi] × [mlo, mhi]`** by the boxes, slab by slab. -/
def coverOK (boxes : List Box) (qlo qhi mlo mhi : Rat) (slabs : List Slab) : Bool :=
  slabsOK boxes qhi mlo mhi qlo slabs

/-! ## One band -/

/-- `q = λ/(1 + λ)`. -/
def actQQ (lam : Rat) : Rat := lam / (1 + lam)

/-- The band parameters are nonnegative (`D`, `θ`, the five rates). -/
def bandSane (band : Band) : Bool :=
  decide (0 ≤ band.D) && decide (0 ≤ band.theta) && (List.range 5).all fun k => decide (0 ≤ band.ell.getD k 0)

/-- **All checks of one band**: the parameters, every box with tail base `tailLam b`, and the cover
of `[q(λ_i), q(λ_{i+1})] × [mmin, mcap]`. -/
def bandOK (band : Band) (tailLam : Box → Rat) (mcap : Rat) (boxes : List Box) (slabs : List Slab) :
    Bool :=
  bandSane band && boxes.all (fun b => boxOK band (tailLam b) b) &&
    coverOK boxes (actQQ band.lamLo) (actQQ band.lamHi) band.mmin mcap slabs

/-- The tail base of the corrected profile: the box's upper activity `λ_h = qh/(1 − qh)`. -/
def lamBox (b : Box) : Rat := b.qh / (1 - b.qh)

end Erdos993Lean.Analytic.Atlas
