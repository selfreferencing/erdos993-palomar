module

public import Erdos993Lean.Analytic.V213.FiberWindowComparison
public import Erdos993Lean.Analytic.V213.FiberAffineReflection
public import Erdos993Lean.Analytic.V213.FiberRayDefinitions

/-!
Eq103: the actual unweighted window deficit. Both signs of the
printed X are retained. The full all-integer lower-offset branch is
discharged by accepted Theorem6.15, including reflected probabilities;
the upper branch uses the actual Eq102 window minorant. The numerical
X test and the printed window parameters are consumed separately.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberWindowPrice (b beta l h N0 X : ℝ) : ℝ :=
  max 0 (fiberPsi h + b + beta * (h-1) -
    (if 0 ≤ X then l * X else h * N0 * X / (N0-2)))

theorem fiber_window_target_mono {b beta t h : ℝ}
    (hbeta : 0 ≤ beta) (ht0 : 0 ≤ t) (hth : t ≤ h) (hh : h ≤ 69/100) :
    fiberPsi t + b + beta * (t-1) ≤ fiberPsi h + b + beta * (h-1) := by
  have hc : 0 ≤ 10 + beta - 9/2*(h+t) := by linarith only [hbeta,ht0,hth,hh]
  have hp := mul_nonneg (sub_nonneg.mpr hth) hc
  unfold fiberPsi
  nlinarith only [hp]

theorem fiber_window_B_bounds {N0 l h mu : ℝ} {M : ℕ}
    (hN0 : 2 < N0) (hN : N0 ≤ (M : ℝ)+2) (hmu : 0 < mu)
    (htl : l ≤ (M : ℝ)/mu) (hth : (M : ℝ)/mu ≤ h) :
    l ≤ ((M : ℝ)+2)/mu ∧ ((M : ℝ)+2)/mu ≤ h*N0/(N0-2) := by
  have hM : 0 < (M : ℝ) := by linarith only [hN0,hN]
  have hden : 0 < N0-2 := by linarith only [hN0]
  have ht0 : 0 ≤ (M : ℝ)/mu := by positivity
  have hh0 : 0 ≤ h := ht0.trans hth
  have hr : ((M : ℝ)+2)/(M : ℝ) ≤ N0/(N0-2) := by
    apply (div_le_div_iff₀ hM hden).2
    nlinarith only [hN]
  have hp := mul_le_mul hth hr (by positivity : 0 ≤ ((M : ℝ)+2)/(M : ℝ)) hh0
  have he : ((M : ℝ)/mu)*(((M : ℝ)+2)/(M : ℝ)) = ((M : ℝ)+2)/mu := by
    field_simp [hM.ne',hmu.ne']
  rw [he] at hp
  exact ⟨htl.trans (div_le_div_of_nonneg_right (by linarith) hmu.le),by
    simpa only [mul_div_assoc] using hp⟩

/-- Literal Eq103, with its exact rational-test premise kept explicit for
the subsequent named F13 consumer, and no truncated rank domain. -/
theorem fiber_window_deficit_bound {a rmax N0 l h v q mu b beta X : ℝ} {M : ℕ}
    (hql : 1/4 ≤ q) (hqh : q ≤ 3/4) (ha : 23/100 ≤ a)
    (har : a ≤ |fiberSkew q|) (hrb : |fiberSkew q| ≤ rmax) (hrmax : rmax ≤ 1/2)
    (hN0 : 14 ≤ N0) (hN : N0 ≤ (M : ℝ)+2)
    (hl : 0 < l) (hv : 0 < v) (hmu40 : 40 ≤ mu)
    (htl : l ≤ (M : ℝ)/mu) (hth : (M : ℝ)/mu ≤ h) (hh : h ≤ 69/100)
    (hb0 : 0 ≤ b) (hbh : b ≤ 2/5) (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1)
    (hX : X ≤ fiberWindowX a rmax N0 l v) :
    fiberDeficit q mu (fun t => b + beta*(t-1)) M ≤ fiberWindowPrice b beta l h N0 X := by
  have hmu : 0 < mu := by linarith only [hmu40]
  have hq0 : 0 < q := by linarith only [hql]
  have hq1 : q < 1 := by linarith only [hqh]
  have ht0 : 0 ≤ (M : ℝ)/mu := by positivity
  have htarget := fiber_window_target_mono (b := b) hbeta0 ht0 hth hh
  have hB := fiber_window_B_bounds (by linarith only [hN0] : 2 < N0) hN hmu htl hth
  have hB0 : 0 ≤ ((M : ℝ)+2)/mu := by positivity
  have hp0 : 0 ≤ fiberWindowPrice b beta l h N0 X := le_max_left _ _
  have hpoint (j : ℤ) :
      fiberPsi ((M : ℝ)/mu) + (b+beta*((M : ℝ)/mu-1)) -
        fiberWindowPrice b beta l h N0 X ≤ fiberF q mu M j := by
    by_cases hw : fiberSquareOffset q M j ≤ fiberBonus q M
    · have hlow := fiber_uniform_affine_comparison_reflected hql hqh
        (by linarith only [ha,har] : 4/25 ≤ |fiberSkew q|)
        hmu40 hb0 hbh hbeta0 hbetah M j hw
      linarith only [hlow,hp0]
    have hupper := fiber_window_upper_all_q hql hqh ha har hrb hrmax hN0 hN hl hv htl hmu j
      (le_of_lt (lt_of_not_ge hw))
    have hmul := mul_le_mul_of_nonneg_left hX hB0
    have hFX : ((M : ℝ)+2)/mu*X ≤ fiberF q mu M j := hmul.trans hupper
    have hprice := le_max_right (0 : ℝ)
      (fiberPsi h+b+beta*(h-1)-(if 0 ≤ X then l*X else h*N0*X/(N0-2)))
    change fiberPsi h+b+beta*(h-1)-(if 0 ≤ X then l*X else h*N0*X/(N0-2)) ≤
      fiberWindowPrice b beta l h N0 X at hprice
    by_cases hx0 : 0 ≤ X
    · have hscale := mul_le_mul_of_nonneg_right hB.1 hx0
      rw [if_pos hx0] at hprice
      linarith only [hscale,hprice,hFX,htarget]
    · have hscale := mul_le_mul_of_nonpos_right hB.2 (le_of_lt (lt_of_not_ge hx0))
      have he : (h*N0/(N0-2))*X = h*N0*X/(N0-2) := by ring
      rw [he] at hscale
      rw [if_neg hx0] at hprice
      linarith only [hscale,hprice,hFX,htarget]
  have hdef := fiber_deficit_pointwise (g := fun t => b+beta*(t-1))
    (L := fiberWindowPrice b beta l h N0 X) hq0 hq1 hmu M hpoint
  rwa [max_eq_right hp0] at hdef

end Erdos993Lean.Analytic.V213
