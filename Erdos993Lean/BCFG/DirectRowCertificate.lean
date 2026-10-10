module

public import Erdos993Lean.BCFG.Certificate
public import Erdos993Lean.BCFG.DirectNormalizedRows

/-!
Explicit consumer adaptation for direct normalization-row checks.
Only the normalization-check premise is reorganized. The supplied polynomial,
closed domain, lower coefficients, interval identities, and sign checks are
unchanged. No dependency on the whole-list normalization check is used.

-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG

/-- Same polynomial/domain conclusion as sourceEval_pos_of_certificate, using
all N+1 separately checked direct normalization rows. -/
theorem sourceEval_pos_of_direct_row_certificate
    (N M : Nat) (p A : Bi) (lower : List Rat) (Is : List IntervalCertificate)
    (l h a b : Rat) (hl : 0 ≤ l) (hlh : l < h) (hb : 0 < b)
    (hnormRows : ∀ i < N+1,
      Uni.checkEq
        (Bi.normalizedRow N p (activityCenterRat l h) (activityRadiusRat l h) a b i)
        (Uni.bernVector M (A.getD i [])) = true)
    (hlower : lowerEqCheck N M A lower = true)
    (hintervals : intervalsCheck M lower Is = true)
    (hcover : coverCheck 0 1 Is = true)
    {lambda y : ℝ}
    (hlambda : (l : ℝ) ≤ lambda ∧ lambda ≤ (h : ℝ))
    (hy : (a : ℝ) ≤ y ∧ y ≤ (a : ℝ)+(b : ℝ)) :
    0 < Bi.sourceEval N p lambda y := by
  have hlReal : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlhReal : (l : ℝ) < (h : ℝ) := by exact_mod_cast hlh
  have hbReal : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hlambda0 : 0 ≤ lambda := le_trans hlReal hlambda.1
  let q := activityQ lambda
  let s := activityS (l : ℝ) (h : ℝ) lambda
  let z := (y-(a : ℝ))/(b : ℝ)
  obtain ⟨hr, hq0, hq1, hs⟩ := activity_coordinates hlReal hlhReal hlambda
  obtain ⟨hz, hyrec⟩ := chart_coordinate hbReal hy
  have hqdef : q = (activityCenterRat l h : ℝ)+(activityRadiusRat l h : ℝ)*s := by
    rw [activityCenterRat_cast, activityRadiusRat_cast]
    exact (activityQ_reconstruct (l : ℝ) (h : ℝ) lambda (ne_of_gt hr)).symm
  have hexp := Bi.checked_expansion_directRows N M p A
    (activityCenterRat l h) (activityRadiusRat l h) a b hnormRows s z q hqdef
    (ne_of_lt hq1)
  have hlow := lower_positive_of_checks N M A lower Is hlower hintervals hcover hz
  have hpos := activity_norm_positive (Bi.sourceEval N p) N M
    (fun i j => ((A.getD i []).getD j 0 : ℝ)) q (a : ℝ) (b : ℝ) s z
    hq1 hexp hs hz hlow
  change 0 < Bi.sourceEval N p (activityQ lambda/(1-activityQ lambda))
    ((a : ℝ)+(b : ℝ)*((y-(a : ℝ))/(b : ℝ))) at hpos
  rw [activityQ_inverse hlambda0, hyrec] at hpos
  exact hpos

end Erdos993Lean.BCFG
