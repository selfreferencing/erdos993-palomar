module

public import Erdos993Lean.Analytic.V213.FiberOuterStartPropagation

/-!
Literal Lemma6.17(ii), all four printed rows. The actual natural
width and integer rank, closed skew/threshold endpoints and both signs of
the target are preserved. Endpoint and numerical premises have all been
discharged by the canonical checks and whole-domain propagation proofs.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_outer_named_comparison (id : FiberOuterStartIdentity)
    {M : ℕ} {q mu b beta : ℝ}
    (hN : lowMeanFractionReal (fiberOuterStartById id).n ≤ (M : ℝ) + 2)
    (hra : lowMeanFractionReal (fiberOuterStartById id).a ≤ fiberSkew q)
    (hrh : fiberSkew q ≤ 2 / 5) (hmu : 0 < mu)
    (hb0 : 0 ≤ b) (hb : b ≤ lowMeanFractionReal (fiberOuterStartById id).b0)
    (hbeta : lowMeanFractionReal (fiberOuterStartById id).beta0 ≤ beta) (hbetah : beta ≤ 1)
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j)
    (ht : lowMeanFractionReal (fiberOuterStartById id).sigma ≤ (M : ℝ) / mu) :
    fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1) ≤ fiberF q mu M j := by
  let n := lowMeanFractionReal (fiberOuterStartById id).n
  let a := lowMeanFractionReal (fiberOuterStartById id).a
  let t := (M : ℝ) / mu
  have hn := fiber_outer_start_guard_sound id .nMin
  have ha := fiber_outer_start_guard_sound id .aPos
  have hs := fiber_outer_start_guard_sound id .sigmaPos
  change 17 ≤ n at hn
  change 0 < a at ha
  change 0 < lowMeanFractionReal (fiberOuterStartById id).sigma at hs
  have hr0 : 0 ≤ fiberSkew q := (ha.trans_le hra).le
  have hqh : q ≤ 3 / 4 := by unfold fiberSkew at hrh; linarith only [hrh]
  have hq0 : 1 / 2 ≤ q := by unfold fiberSkew at hr0; linarith only [hr0]
  have hyr : fiberSkew q ^ 2 ≤ (4 / 25 : ℝ) := by nlinarith only [hr0,hrh]
  have hR : 0 < fiberOuterR ((M : ℝ) + 2) (fiberSkew q ^ 2) := by
    linarith only [fiber_outer_R_pos (hn.trans hN) (sq_nonneg (fiberSkew q)) hyr]
  have he := fiber_outer_actual_envelope (hn.trans hN) hq0 hqh hmu hR j hw
  have hp := fiber_outer_named_region id hN hra hrh hb hbeta hbetah ht
  have hz := fiber_upper_size_ratio_sandwich (by linarith only [hn] : 10 ≤ n) hN
  have htarget := fiber_upper_signed_target (f := fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t)
    hz.1 hz.2
  have hbound := htarget.trans (hp.trans he)
  have hB : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hmul := (le_div_iff₀ hB).mp hbound
  have heq : (M : ℝ) / ((M : ℝ) + 2) *
      fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t * (((M : ℝ) + 2) / mu) =
      t * fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t := by
    dsimp [t]
    field_simp [hmu.ne',(by positivity : (M : ℝ) + 2 ≠ 0)]
  rw [heq,fiber_outer_target_identity (hs.trans_le ht)] at hmul
  exact hmul

end Erdos993Lean.Analytic.V213
