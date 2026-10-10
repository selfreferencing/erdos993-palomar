module

public import Erdos993Lean.Analytic.V213.FiberAffineMassMinorant
public import Erdos993Lean.Analytic.V213.FiberAffineBranches
public import Erdos993Lean.Analytic.V213.FiberLowerQuadratic

/-!
Middle-ratio test on every closed t in[1/2,3/4] and w in[0,3/2].
The actual Eq85 minorant, positive exponential factors and inverse power
are consumed before unnormalizing with B>=t. The printed477/320,
139/120 and319/1920 bounds retain all endpoint and integer-rank cases.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_affine_inverse_power_middle {t : ℝ} (htl : 1 / 2 ≤ t) (hth : t ≤ 3 / 4) :
    (2 : ℝ) ≤ t ^ (-(5 / 2 : ℝ)) := by
  have ht : 0 < t := by linarith only [htl]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs2 := Real.sq_sqrt ht.le
  have hsh : Real.sqrt t ≤ 8 / 9 := by nlinarith only [hs2,hth,hs.le]
  have ht2 : t ^ 2 ≤ (9 / 16 : ℝ) := by nlinarith only [ht.le,hth]
  have hp := mul_le_mul ht2 hsh hs.le (by norm_num : (0 : ℝ) ≤ 9 / 16)
  have hroot := fiber_lower_rpow_half_nat ht 5
  norm_num only [Nat.cast_ofNat] at hroot
  rw [hroot]
  apply (le_div_iff₀ (pow_pos hs 5)).2
  have hpow : Real.sqrt t ^ 5 = t ^ 2 * Real.sqrt t := by
    calc
      _ = (Real.sqrt t ^ 2) ^ 2 * Real.sqrt t := by ring
      _ = _ := by rw [hs2]
  rw [hpow]
  nlinarith only [hp]

theorem fiber_affine_middle_scalar {t w : ℝ} (htl : 1 / 2 ≤ t) (hth : t ≤ 3 / 4)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    (477 / 320 : ℝ) ≤ w + t ^ (-(5 / 2 : ℝ)) *
      (fiberAffineG t - w) * Real.exp (1 / 5 - (8 / 15 : ℝ) * w) := by
  have hpow := fiber_affine_inverse_power_middle htl hth
  have hg : (3 / 2 : ℝ) - w ≤ fiberAffineG t - w := by
    unfold fiberAffineG
    linarith only [htl]
  have hcoeff : 0 ≤ (3 / 2 : ℝ) - w := by linarith only [hwh]
  have hg0 : 0 ≤ fiberAffineG t - w := hcoeff.trans hg
  have hx : 0 ≤ 6 / 5 - (8 / 15 : ℝ) * w := by linarith only [hwh]
  have hexp : 6 / 5 - (8 / 15 : ℝ) * w ≤ Real.exp (1 / 5 - (8 / 15 : ℝ) * w) := by
    convert Real.add_one_le_exp (1 / 5 - (8 / 15 : ℝ) * w) using 1 <;> ring
  have hleft := mul_le_mul hpow hg hcoeff (by linarith only [hpow] : 0 ≤ t ^ (-(5 / 2 : ℝ)))
  have hprod := mul_le_mul hleft hexp hx (mul_nonneg (by positivity) hg0)
  have he : w + 2 * (3 / 2 - w) * (6 / 5 - (8 / 15 : ℝ) * w) =
      (16 / 15 : ℝ) * (w - 45 / 32) ^ 2 + 477 / 320 := by ring
  nlinarith only [hprod,he,sq_nonneg (w - 45 / 32)]

theorem fiber_affine_middle_target {t b beta : ℝ}
    (htl : 1 / 2 ≤ t) (hth : t ≤ 3 / 4) (hb : b ≤ 2 / 5) (hbeta0 : 0 ≤ beta) :
    fiberPsi t + b + beta * (t - 1) ≤ (139 / 120 : ℝ) * t := by
  have hbeta : beta * (t - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbeta0 (by linarith only [hth])
  have hp : 0 ≤ (3 - 4 * t) * (164 - 135 * t) :=
    mul_nonneg (by linarith only [hth]) (by linarith only [hth])
  unfold fiberPsi
  nlinarith only [hp,hb,hbeta]

theorem fiber_affine_middle_comparison {q mu b beta : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hrl : 4 / 25 ≤ fiberSkew q)
    (hmu : 40 ≤ mu) (hb : b ≤ 2 / 5) (hbeta0 : 0 ≤ beta) (M : ℕ) (j : ℤ)
    (htl : 1 / 2 ≤ (M : ℝ) / mu) (hth : (M : ℝ) / mu ≤ 3 / 4)
    (hw : fiberSquareOffset q M j ≤ 3 / 2) :
    fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1) + 1 / 28 ≤ fiberF q mu M j := by
  have hm0 : 0 < mu := by linarith only [hmu]
  have hM := fiber_affine_width22 hmu htl
  have hw0 := fiber_square_offset_nonneg (by linarith : 0 < q) (by linarith : q < 1) M j
  have hgain := (fiber_affine_middle_scalar htl hth hw0 hw).trans
    (fiber_affine_eq85_first hM hq0 hqh hrl hmu htl j hw)
  have hB : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hclear := (le_div_iff₀ hB).mp hgain
  have hBt : (M : ℝ) / mu ≤ ((M : ℝ) + 2) / mu :=
    div_le_div_of_nonneg_right (by linarith) hm0.le
  have hl := mul_le_mul_of_nonneg_left hBt (by norm_num : (0 : ℝ) ≤ 477 / 320)
  have htarget := fiber_affine_middle_target htl hth hb hbeta0
  have hmargin : (319 / 1920 : ℝ) ≤ (319 / 960 : ℝ) * ((M : ℝ) / mu) := by linarith only [htl]
  nlinarith only [hclear,hl,htarget,hmargin]

end Erdos993Lean.Analytic.V213
