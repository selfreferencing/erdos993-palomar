module

public import Erdos993Lean.Analytic.V213.LowMeanEquationSixty
public import Erdos993Lean.Analytic.V213.LowMeanWidth

/-!
Equation-51 target semantics and the printed width propagation conditions.
The exact potential uses the attained maximum of q(1-q) on the whole Q.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

structure LowMeanWidthPair where
  certificate : ℕ
  t : ℕ
  r : ℕ
  slope : ℕ
  deriving DecidableEq

noncomputable def lowMeanCertificatePotential (c : LowMeanCertificateInput) (m : ℕ) : ℝ :=
  lowMeanV (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
    (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta)
    (lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h))
    (lowMeanFractionReal c.z) (lowMeanFractionReal c.l) m

def lowMeanShapeCertificatePotential (c : LowMeanCertificateInput) (m : ℕ) : LowMeanIntegerShape :=
  lowMeanShapeSub (.add (lowMeanCertificatePsi c (lowMeanShapeInt m))
    (.mul (.mul (.atom c.eta) (lowMeanCertificateVariance c)) (lowMeanShapeInt m)))
    (.mul (.atom c.z) (.pow (lowMeanShapeSub (lowMeanShapeInt 1) (.atom c.l)) m))

def lowMeanDirectWidth (ps : List LowMeanWidthPair) (certificate M : ℕ) : Bool :=
  decide (M ≤ (lowMeanCertificateAt (certificate - 1)).T) &&
    !(ps.any fun p => decide (p.certificate = certificate ∧ p.t < M ∧ M ≤ p.r))

def lowMeanDirectTargetR (ps : List LowMeanWidthPair) (certificate M : ℕ) : ℕ :=
  ((ps.find? fun p => decide (p.certificate = certificate ∧ p.t = M)).map LowMeanWidthPair.r).getD M

def lowMeanWidthPairCheck (p : LowMeanWidthPair) : Bool :=
  decide (0 < p.certificate ∧ p.certificate ≤ 28 ∧ 3 ≤ p.t ∧ p.t < p.r ∧
    p.r ≤ (lowMeanCertificateAt (p.certificate - 1)).T ∧ p.slope < 12 ∧
    (lowMeanSlopeAt p.slope).1 = lowMeanCertificateAt (p.certificate - 1) ∧
    p.r ≤ (lowMeanSlopeAt p.slope).2.2.2)

structure LowMeanDirectTargetInput where
  R : ℕ
  expr : LowMeanIntegerExpr

structure LowMeanDirectSeedInput where
  record : ℕ
  positions : List LowMeanSeedBudgetChoice
  target : LowMeanDirectTargetInput

def lowMeanDirectTargetShape (f : LowMeanFiberInput) (w : LowMeanDirectTargetInput) : LowMeanIntegerShape :=
  lowMeanShapeSub (.add (.atom (1, 100000)) (lowMeanShapeCertificatePotential (lowMeanFiberCertificate f) w.R))
    (lowMeanShapeCertificatePotential (lowMeanFiberCertificate f) f.M)

def lowMeanDirectTargetCheck (ps : List LowMeanWidthPair) (f : LowMeanFiberInput)
    (w : LowMeanDirectTargetInput) : Bool :=
  decide (lowMeanDirectWidth ps f.certificate f.M = true ∧
    w.R = lowMeanDirectTargetR ps f.certificate f.M ∧ f.M ≤ w.R ∧
    lowMeanFractionValid f.zeta ∧ lowMeanFractionLE (1, 100000) f.zeta) &&
  lowMeanIntegerEqualityCheck w.expr (lowMeanDirectTargetShape f w) f.zeta

noncomputable def lowMeanDirectSeedCheck (ps : List LowMeanWidthPair) (f : LowMeanFiberInput)
    (s : LowMeanDirectSeedInput) : Bool :=
  lowMeanFiberBudgetCheck { fiber := f, positions := s.positions } &&
    lowMeanDirectTargetCheck ps f s.target

def lowMeanSeedChoiceIndices (w : LowMeanSeedBudgetChoice) : List ℕ :=
  if w.mode = 1 then [w.left, w.right] else [w.left]

@[simp] theorem lowMean_shape_certificatePotential (c : LowMeanCertificateInput) (m : ℕ) :
    lowMeanIntegerShapeReal (lowMeanShapeCertificatePotential c m) = lowMeanCertificatePotential c m := by
  simp [lowMeanShapeCertificatePotential, lowMeanCertificatePotential, lowMeanV,
    lowMeanIntegerShapeReal]

theorem lowMean_directTarget_exact (ps : List LowMeanWidthPair) (f : LowMeanFiberInput)
    (w : LowMeanDirectTargetInput) (h : lowMeanDirectTargetCheck ps f w = true) :
    lowMeanFractionReal f.zeta = (1 / 100000 : ℝ) +
      lowMeanCertificatePotential (lowMeanFiberCertificate f) w.R -
      lowMeanCertificatePotential (lowMeanFiberCertificate f) f.M := by
  simp only [lowMeanDirectTargetCheck, Bool.and_eq_true] at h
  have he := lowMean_integerEquality_sound h.2
  simpa [lowMeanDirectTargetShape, lowMeanIntegerShapeReal, lowMeanFractionReal] using he.symm

theorem lowMean_directTarget_epsilon (ps : List LowMeanWidthPair) (f : LowMeanFiberInput)
    (w : LowMeanDirectTargetInput) (h : lowMeanDirectTargetCheck ps f w = true) :
    (1 / 100000 : ℝ) ≤ lowMeanFractionReal f.zeta := by
  simp only [lowMeanDirectTargetCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa [lowMeanFractionReal] using (lowMean_fraction_le_iff (x := (1, 100000)) (by decide) h.1.2.2.2.1).mp h.1.2.2.2.2

theorem lowMean_directSeed_strong (ps : List LowMeanWidthPair) (f : LowMeanFiberInput)
    (s : LowMeanDirectSeedInput) (hc : lowMeanFiberCheck f = true)
    (h : lowMeanDirectSeedCheck ps f s = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanFiberCertificate f).l)
      (lowMeanFractionReal (lowMeanFiberCertificate f).h)) (j : ℤ) :
    (1 / 100000 : ℝ) + lowMeanCertificatePotential (lowMeanFiberCertificate f) s.target.R -
      lowMeanCertificatePotential (lowMeanFiberCertificate f) f.M ≤
      lowMeanCertificateSlack (lowMeanFiberCertificate f) f.M j q := by
  simp only [lowMeanDirectSeedCheck, Bool.and_eq_true] at h
  rw [← lowMean_directTarget_exact ps f s.target h.2]
  exact lowMean_fiber_seed { fiber := f, positions := s.positions } hc h.1 hq j

theorem lowMean_directSeed_epsilon (ps : List LowMeanWidthPair) (f : LowMeanFiberInput)
    (s : LowMeanDirectSeedInput) (hc : lowMeanFiberCheck f = true)
    (h : lowMeanDirectSeedCheck ps f s = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanFiberCertificate f).l)
      (lowMeanFractionReal (lowMeanFiberCertificate f).h)) (j : ℤ) :
    (1 / 100000 : ℝ) ≤ lowMeanCertificateSlack (lowMeanFiberCertificate f) f.M j q := by
  have hd := h
  simp only [lowMeanDirectSeedCheck, Bool.and_eq_true] at hd
  exact le_trans (lowMean_directTarget_epsilon ps f s.target hd.2)
    (lowMean_fiber_seed { fiber := f, positions := s.positions } hc hd.1 hq j)

theorem lowMean_widthPair_conditions (p : LowMeanWidthPair) (h : lowMeanWidthPairCheck p = true) :
    let c := lowMeanCertificateAt (p.certificate - 1)
    (1 - lowMeanFractionReal c.l) / lowMeanFractionReal c.l ≤ (p.t : ℝ) ∧
    2 * lowMeanFractionReal c.gamma * ((p.r : ℝ) - lowMeanFractionReal c.m0) ≤
      lowMeanFractionReal c.beta + lowMeanFractionReal c.gamma + lowMeanFractionReal c.eta *
        lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) := by
  simp only [lowMeanWidthPairCheck, decide_eq_true_eq] at h
  rcases h with ⟨hc0, hc28, ht3, _, _, hsi, hsc, hrmax⟩
  have hi : p.certificate - 1 < 28 := by omega
  obtain ⟨hl, _, _⟩ := lowMean_certificate_interval_facts _ hi
  have hgamma := (lowMean_certificate_signs _ hi).2.2.2.1
  have hs := lowMean_slopes_explicit p.slope hsi
  rw [hsc] at hs
  have hr : (p.r : ℝ) ≤ (lowMeanSlopeAt p.slope).2.2.2 := by exact_mod_cast hrmax
  have hp := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hgamma)
  have ht : (3 : ℝ) ≤ p.t := by exact_mod_cast ht3
  constructor
  · apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hl)).mpr
    have hm := mul_le_mul_of_nonneg_right ht (le_trans (by norm_num) hl)
    linarith
  · linarith

theorem lowMean_certificate_strongSeed (i : ℕ) (hi : i < 28)
    {q : ℝ} (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) {t r M : ℕ}
    (htr : t < r) (ht : (1 - lowMeanFractionReal (lowMeanCertificateAt i).l) /
      lowMeanFractionReal (lowMeanCertificateAt i).l ≤ (t : ℝ))
    (hslope : 2 * lowMeanFractionReal (lowMeanCertificateAt i).gamma *
      ((r : ℝ) - lowMeanFractionReal (lowMeanCertificateAt i).m0) ≤
      lowMeanFractionReal (lowMeanCertificateAt i).beta + lowMeanFractionReal (lowMeanCertificateAt i).gamma +
      lowMeanFractionReal (lowMeanCertificateAt i).eta * lowMeanVarianceMaximum
        (lowMeanFractionReal (lowMeanCertificateAt i).l) (lowMeanFractionReal (lowMeanCertificateAt i).h))
    (hseed : ∀ j : ℤ, (1 / 100000 : ℝ) + lowMeanCertificatePotential (lowMeanCertificateAt i) r -
      lowMeanCertificatePotential (lowMeanCertificateAt i) t ≤ lowMeanCertificateSlack (lowMeanCertificateAt i) t j q)
    (htm : t ≤ M) (hmr : M ≤ r) (j : ℤ) :
    (1 / 100000 : ℝ) ≤ lowMeanCertificateSlack (lowMeanCertificateAt i) M j q := by
  obtain ⟨hl, hh, _⟩ := lowMean_certificate_interval_facts i hi
  obtain ⟨_, _, heta, hgamma, hz, _⟩ := lowMean_certificate_signs i hi
  apply lowMean_strongSeed (t := t) (r := r)
    (lt_of_lt_of_le (by norm_num) hl) (lt_of_le_of_lt hh (by norm_num)) hq
    heta.le hgamma hz (lowMean_varianceMaximum_bound hq) htr ht hslope
    (by simpa only [lowMeanCertificatePotential, lowMeanCertificateSlack] using hseed) htm hmr j

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_directTarget_exact
#print axioms Erdos993Lean.Analytic.V213.lowMean_certificate_strongSeed
