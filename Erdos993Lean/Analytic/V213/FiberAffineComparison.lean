module

public import Erdos993Lean.Analytic.V213.FiberAffineMiddle
public import Erdos993Lean.Analytic.V213.FiberAffineSupportBinding
public import Erdos993Lean.Analytic.V213.FiberAffineTangent

/-!
Literal Theorem6.15, full natural-width/integer-rank assembly.
The large-offset, small-ratio (including M=0), middle-ratio and tangent
branches discharge every analytic and numerical condition. Only the
printed mean, skew, b/beta and actual w<=gamma hypotheses remain.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_uniform_affine_comparison {q mu b beta : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hrl : 4 / 25 ≤ fiberSkew q)
    (hmu : 40 ≤ mu) (hb0 : 0 ≤ b) (hbh : b ≤ 2 / 5)
    (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1) (M : ℕ) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ fiberBonus q M) :
    fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1) + 1 / 28 ≤
      fiberF q mu M j := by
  have hqpos : 0 < q := by linarith only [hq0]
  have hqone : q < 1 := by linarith only [hqh]
  have hm0 : 0 < mu := by linarith only [hmu]
  by_cases hsmall : (M : ℝ) / mu ≤ 1 / 2
  · exact fiber_affine_small_ratio hqpos hqone hm0 hbh hbeta0 M j hsmall hw
  have htl : 1 / 2 ≤ (M : ℝ) / mu := le_of_lt (lt_of_not_ge hsmall)
  by_cases hlarge : 3 / 2 ≤ fiberSquareOffset q M j
  · exact fiber_affine_large_offset hqpos hqone hm0 hbh hbeta0 hbetah M j hlarge hw
  have hwh : fiberSquareOffset q M j ≤ 3 / 2 := le_of_lt (lt_of_not_ge hlarge)
  by_cases hmiddle : (M : ℝ) / mu ≤ 3 / 4
  · exact fiber_affine_middle_comparison hq0 hqh hrl hmu hbh hbeta0 M j htl hmiddle hwh
  have htr : 3 / 4 ≤ (M : ℝ) / mu := le_of_lt (lt_of_not_ge hmiddle)
  have hw0 := fiber_square_offset_nonneg hqpos hqone M j
  have hl := fiber_affine_support_actual (beta := beta) hq0 hqh hrl hmu hbh M j htr hwh
  have hmargin := fiber_affine_support_margin (beta := beta) htr hw0 hwh hbeta0 hbetah
  linarith only [hl,hmargin]

theorem fiber_uniform_affine_comparison_skew {r mu b beta : ℝ}
    (hrl : 4 / 25 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 40 ≤ mu)
    (hb0 : 0 ≤ b) (hbh : b ≤ 2 / 5) (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1)
    (M : ℕ) (j : ℤ)
    (hw : fiberSquareOffset ((1 + r) / 2) M j ≤ fiberBonus ((1 + r) / 2) M) :
    fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1) + 1 / 28 ≤
      fiberF ((1 + r) / 2) mu M j := by
  have hr0 : 0 ≤ r := by linarith only [hrl]
  have he : fiberSkew ((1 + r) / 2) = r := by unfold fiberSkew; ring
  exact fiber_uniform_affine_comparison (by linarith only [hr0]) (by linarith only [hrh])
    (by simpa only [he] using hrl) hmu hb0 hbh hbeta0 hbetah M j hw

end Erdos993Lean.Analytic.V213
