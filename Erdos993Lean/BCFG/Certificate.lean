module

public import Erdos993Lean.BCFG.BernsteinListBridge
public import Erdos993Lean.BCFG.Bivariate
public import Erdos993Lean.BCFG.ActivityCoordinates

/-!
Generic finite-certificate consumer for the BCFG packet. The assumptions of
sourceEval_pos_of_certificate are exact finite checks and domain membership;
no analytic payment or forest assumption is used. Shape and custody checks
remain independent obligations when identifying a data list with the packet.

-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

open scoped BigOperators

/-- All intervals for a polynomial use its common Bernstein degree M. -/
structure IntervalCertificate where
  lo : Rat
  hi : Rat
  coeffs : List Rat
  deriving DecidableEq

/-- Check the literal lower vector against the norm formula at every j≤M. -/
def lowerEqCheck (N M : Nat) (A : Bi) (lower : List Rat) : Bool :=
  (List.range (M+1)).all (fun j => decide
    (lower.getD j 0 = rationalNormLower N (fun i j => (A.getD i []).getD j 0) j))

theorem lowerEqCheck_sound (N M : Nat) (A : Bi) (lower : List Rat)
    (h : lowerEqCheck N M A lower = true) (j : Nat) (hj : j ≤ M) :
    lower.getD j 0 = rationalNormLower N (fun i j => (A.getD i []).getD j 0) j := by
  unfold lowerEqCheck at h
  exact of_decide_eq_true (List.all_eq_true.mp h j
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hj)))

theorem lowerEqCheck_cast (N M : Nat) (A : Bi) (lower : List Rat)
    (h : lowerEqCheck N M A lower = true) (j : Nat) (hj : j ≤ M) :
    (lower.getD j 0 : ℝ) =
      normLower N (fun i j => ((A.getD i []).getD j 0 : ℝ)) j := by
  have hc := congrArg (fun x : Rat => (x : ℝ)) (lowerEqCheck_sound N M A lower h j hj)
  try dsimp only at hc
  rw [rationalNormLower_cast] at hc
  exact hc

theorem lower_value_eq (N M : Nat) (A : Bi) (lower : List Rat)
    (h : lowerEqCheck N M A lower = true) (z : ℝ) :
    Uni.evalReal (Uni.bernVector M lower) z =
      bernsteinSum M (normLower N (fun i j => ((A.getD i []).getD j 0 : ℝ))) z := by
  rw [Uni.evalReal_bernVector_eq_bernsteinSum]
  unfold bernsteinSum
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [lowerEqCheck_cast N M A lower h j
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

/-- The lower polynomial is already represented in Bernstein coefficients;
restrict its polynomial, then compare to this interval's Bernstein vector. -/
def intervalCheck (M : Nat) (lower : List Rat) (I : IntervalCertificate) : Bool :=
  decide (I.lo < I.hi) &&
    (Uni.checkEq
      (Uni.comp (Uni.bernVector M lower) [I.lo, I.hi-I.lo])
      (Uni.bernVector M I.coeffs) &&
      positiveCoefficients M (fun j => I.coeffs.getD j 0))

def intervalsCheck (M : Nat) (lower : List Rat) (Is : List IntervalCertificate) : Bool :=
  Is.all (intervalCheck M lower)

theorem intervalCheck_sound (M : Nat) (lower : List Rat) (I : IntervalCertificate)
    (h : intervalCheck M lower I = true) {z : ℝ}
    (hz : (I.lo : ℝ) ≤ z ∧ z ≤ (I.hi : ℝ)) :
    0 < Uni.evalReal (Uni.bernVector M lower) z := by
  change (decide (I.lo < I.hi) &&
    (Uni.checkEq (Uni.comp (Uni.bernVector M lower) [I.lo, I.hi-I.lo])
      (Uni.bernVector M I.coeffs) &&
      positiveCoefficients M (fun j => I.coeffs.getD j 0))) = true at h
  rcases Bool.and_eq_true_iff.mp h with ⟨horder, hrest⟩
  rcases Bool.and_eq_true_iff.mp hrest with ⟨hidentity, hpositive⟩
  exact Uni.positive_on_interval_of_checks (Uni.bernVector M lower) M I.coeffs
    I.lo I.hi (of_decide_eq_true horder) hidentity hpositive hz

/-- A finite chain of closed intervals covers [start,stop]. Overlap is allowed;
a gap is not. Once an interval reaches stop, later intervals are irrelevant to
coverage (but intervalsCheck still checks every listed certificate). -/
def coverCheck : Rat → Rat → List IntervalCertificate → Bool
  | _, _, [] => false
  | start, stop, I :: Is =>
      decide (I.lo ≤ start) && (decide (stop ≤ I.hi) || coverCheck I.hi stop Is)

theorem coverCheck_sound (Is : List IntervalCertificate) (start stop : Rat)
    (h : coverCheck start stop Is = true) {z : ℝ}
    (hz : (start : ℝ) ≤ z ∧ z ≤ (stop : ℝ)) :
    ∃ I ∈ Is, (I.lo : ℝ) ≤ z ∧ z ≤ (I.hi : ℝ) := by
  induction Is generalizing start with
  | nil => simp [coverCheck] at h
  | cons I Is ih =>
      change (decide (I.lo ≤ start) &&
        (decide (stop ≤ I.hi) || coverCheck I.hi stop Is)) = true at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hleft, hrest⟩
      have hleftRat : I.lo ≤ start := of_decide_eq_true hleft
      by_cases hzi : z ≤ (I.hi : ℝ)
      · refine ⟨I, by simp, ?_, hzi⟩
        exact le_trans (by exact_mod_cast hleftRat) hz.1
      · have hnext : coverCheck I.hi stop Is = true := by
          rcases Bool.or_eq_true_iff.mp hrest with hstop | hnext
          · have hstopRat : stop ≤ I.hi := of_decide_eq_true hstop
            exact False.elim (hzi (le_trans hz.2 (by exact_mod_cast hstopRat)))
          · exact hnext
        obtain ⟨J, hJ, hzJ⟩ := ih I.hi hnext
          ⟨le_of_lt (lt_of_not_ge hzi), hz.2⟩
        exact ⟨J, List.mem_cons_of_mem I hJ, hzJ⟩

/-- Positivity uses an explicit finite cover of the full closed z-domain. -/
theorem lower_positive_of_checks (N M : Nat) (A : Bi) (lower : List Rat)
    (Is : List IntervalCertificate)
    (hlower : lowerEqCheck N M A lower = true)
    (hintervals : intervalsCheck M lower Is = true)
    (hcover : coverCheck 0 1 Is = true) {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    0 < bernsteinSum M
      (normLower N (fun i j => ((A.getD i []).getD j 0 : ℝ))) z := by
  obtain ⟨I, hI, hzI⟩ := coverCheck_sound Is 0 1 hcover (by simpa using hz)
  have hIcheck : intervalCheck M lower I = true :=
    List.all_eq_true.mp hintervals I hI
  have hpos := intervalCheck_sound M lower I hIcheck hzI
  rw [lower_value_eq N M A lower hlower] at hpos
  exact hpos

/-- Rational row coordinates; the cast lemmas identify the real coordinates
without assuming a nonzero denominator at the definition level. -/
def activityQRat (x : Rat) : Rat := x/(1+x)
def activityCenterRat (l h : Rat) : Rat := (activityQRat l + activityQRat h)/2
def activityRadiusRat (l h : Rat) : Rat := (activityQRat h - activityQRat l)/2

@[simp] theorem activityQRat_cast (x : Rat) :
    (activityQRat x : ℝ) = activityQ (x : ℝ) := by
  simp [activityQRat, activityQ]

@[simp] theorem activityCenterRat_cast (l h : Rat) :
    (activityCenterRat l h : ℝ) = activityCenter (l : ℝ) (h : ℝ) := by
  simp [activityCenterRat, activityCenter]

@[simp] theorem activityRadiusRat_cast (l h : Rat) :
    (activityRadiusRat l h : ℝ) = activityRadius (l : ℝ) (h : ℝ) := by
  simp [activityRadiusRat, activityRadius]

/-- Closed-domain positivity of the bounded supplied polynomial, from exact
finite checks. There is no analytic or graph-theoretic hypothesis here. -/
theorem sourceEval_pos_of_certificate
    (N M : Nat) (p A : Bi) (lower : List Rat) (Is : List IntervalCertificate)
    (l h a b : Rat) (hl : 0 ≤ l) (hlh : l < h) (hb : 0 < b)
    (hnorm : Bi.checkEq
      (Bi.normalized N p (activityCenterRat l h) (activityRadiusRat l h) a b)
      (Bi.fromNorm N M A) = true)
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
  have hexp := Bi.checked_expansion N M p A
    (activityCenterRat l h) (activityRadiusRat l h) a b hnorm s z q hqdef
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
