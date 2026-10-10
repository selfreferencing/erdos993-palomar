module

public import Erdos993Lean.Analytic.V213.LowMeanCoreGeometry
public import Erdos993Lean.Analytic.V213.LowMeanIntegerOrder
public import Erdos993Lean.Analytic.V213.LowMeanCertificateFacts

/-!
All-integer core checker soundness. Both exact finite maxima,
two tail sides and two tail distances are checked once per fiber. Every
rank in the finite window has a proved membership or exclusion witness.
Together these checks prove equality with the printed core on all integers.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

structure LowMeanCoreRankWitness where
  j : ℤ
  state : ℕ
  first : LowMeanIntegerExpr
  second : LowMeanIntegerExpr
structure LowMeanFiberInput where
  record : ℕ
  certificate : ℕ
  M : ℕ
  zeta : lowMeanFraction
  lo : ℤ
  hi : ℤ
  gL : lowMeanFraction
  gR : lowMeanFraction
  core : List ℤ
  gLExpr : LowMeanIntegerExpr
  gRExpr : LowMeanIntegerExpr
  leftSide : LowMeanIntegerExpr
  rightSide : LowMeanIntegerExpr
  leftTail : LowMeanIntegerExpr
  rightTail : LowMeanIntegerExpr
  ranks : List LowMeanCoreRankWitness

def lowMeanFiberCertificate (f : LowMeanFiberInput) : LowMeanCertificateInput := lowMeanCertificateAt (f.certificate - 1)
def lowMeanCoreRankAt (f : LowMeanFiberInput) (k : ℕ) : LowMeanCoreRankWitness :=
  f.ranks.getD k { j := 0, state := 0, first := .atom (0, 1), second := .atom (0, 1) }
noncomputable def lowMeanFiberCore (f : LowMeanFiberInput) : Set ℤ :=
  let c := lowMeanFiberCertificate f
  lowMeanCore f.M (lowMeanFractionReal c.wL) (lowMeanFractionReal c.wR) (lowMeanFractionReal c.xi)
    (lowMeanFractionReal c.eta) (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta)
    (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0) (lowMeanFractionReal c.z)
    (lowMeanFractionReal f.zeta) (lowMeanFractionReal c.l) (lowMeanFractionReal c.h)

def lowMeanFiberMetaCheck (f : LowMeanFiberInput) : Bool :=
  decide (0 < f.certificate ∧ f.certificate ≤ 28 ∧ f.lo < -1 ∧ (f.M : ℤ) + 1 < f.hi ∧
    f.ranks.length = (f.hi - f.lo).toNat + 1 ∧ lowMeanFractionValid f.zeta ∧ 0 ≤ f.zeta.1 ∧ f.core.Nodup) &&
  f.core.all (fun j => decide (f.lo ≤ j ∧ j ≤ f.hi))
def lowMeanFiberGeometryCheck (f : LowMeanFiberInput) : Bool :=
  let c := lowMeanFiberCertificate f
  lowMeanIntegerEqualityCheck f.gLExpr (lowMeanShapeClosedMaximum f.M (.atom c.l)) f.gL &&
  lowMeanIntegerEqualityCheck f.gRExpr (lowMeanShapeClosedMaximum f.M (lowMeanShapeSub (lowMeanShapeInt 1) (.atom c.h))) f.gR &&
  lowMeanIntegerLowerCheck f.leftSide (lowMeanShapeCoreLeftSide c f.M f.lo) (0, 1) &&
  lowMeanIntegerLowerCheck f.rightSide (lowMeanShapeCoreRightSide c f.M f.hi) (0, 1) &&
  lowMeanIntegerLowerCheck f.leftTail (lowMeanShapeCoreLeftTail c f.M f.lo f.zeta) (0, 1) &&
  lowMeanIntegerLowerCheck f.rightTail (lowMeanShapeCoreRightTail c f.M f.hi f.zeta) (0, 1)
def lowMeanCoreRankCheck (f : LowMeanFiberInput) (w : LowMeanCoreRankWitness) : Bool :=
  let c := lowMeanFiberCertificate f
  decide (w.state ≤ 2) &&
  if w.state = 0 then lowMeanIntegerLowerCheck w.first (.neg (lowMeanShapeCoreFirst c f.M w.j f.zeta f.gL f.gR)) (0, 1)
  else if w.state = 1 then lowMeanIntegerLowerCheck w.second (.neg (lowMeanShapeCoreSecond c f.M w.j f.zeta)) (0, 1)
  else lowMeanIntegerPositiveCheck w.first (lowMeanShapeCoreFirst c f.M w.j f.zeta f.gL f.gR) (0, 1) &&
    lowMeanIntegerPositiveCheck w.second (lowMeanShapeCoreSecond c f.M w.j f.zeta) (0, 1)
def lowMeanFiberWindowCheck (f : LowMeanFiberInput) : Bool :=
  (List.range f.ranks.length).all fun k =>
    let w := lowMeanCoreRankAt f k
    decide (w.j = f.lo + (k : ℤ) ∧ (w.state = 2 ↔ w.j ∈ f.core)) && lowMeanCoreRankCheck f w

def lowMeanFiberCheck (f : LowMeanFiberInput) : Bool :=
  lowMeanFiberMetaCheck f && lowMeanFiberGeometryCheck f && lowMeanFiberWindowCheck f

theorem lowMean_fiber_probability_domain (f : LowMeanFiberInput)
    (hmeta : lowMeanFiberMetaCheck f = true) :
    0 < lowMeanFractionReal (lowMeanFiberCertificate f).l ∧
      lowMeanFractionReal (lowMeanFiberCertificate f).h < 1 ∧
      lowMeanFractionReal (lowMeanFiberCertificate f).l < lowMeanFractionReal (lowMeanFiberCertificate f).h := by
  simp only [lowMeanFiberMetaCheck, Bool.and_eq_true, decide_eq_true_eq] at hmeta
  have hi : f.certificate - 1 < 28 := by omega
  have h := lowMean_certificate_interval_facts (f.certificate - 1) hi
  exact ⟨lt_of_lt_of_le (by norm_num) h.1, lt_of_le_of_lt h.2.1 (by norm_num), h.2.2⟩

theorem lowMean_fiber_g_values (f : LowMeanFiberInput)
    (hmeta : lowMeanFiberMetaCheck f = true) (hgeo : lowMeanFiberGeometryCheck f = true) :
    lowMeanFractionReal f.gL = lowMeanClosedMaximum f.M (lowMeanFractionReal (lowMeanFiberCertificate f).l) ∧
    lowMeanFractionReal f.gR = lowMeanClosedMaximum f.M (1 - lowMeanFractionReal (lowMeanFiberCertificate f).h) := by
  obtain ⟨hl, hh, hlh⟩ := lowMean_fiber_probability_domain f hmeta
  simp only [lowMeanFiberGeometryCheck, Bool.and_eq_true] at hgeo
  have hL := lowMean_integerEquality_sound hgeo.1.1.1.1.1
  have hR := lowMean_integerEquality_sound hgeo.1.1.1.1.2
  rw [lowMean_shape_closedMaximum f.M (.atom (lowMeanFiberCertificate f).l)
    (by simpa only [lowMeanIntegerShapeReal] using hl)
    (by simpa only [lowMeanIntegerShapeReal] using lt_of_lt_of_le hlh hh.le)] at hL
  have hr0 : 0 < lowMeanIntegerShapeReal (lowMeanShapeSub (lowMeanShapeInt 1) (.atom (lowMeanFiberCertificate f).h)) := by
    simpa only [lowMean_shape_sub, lowMean_shape_int, lowMeanIntegerShapeReal, Int.cast_one] using sub_pos.mpr hh
  have hr1 : lowMeanIntegerShapeReal (lowMeanShapeSub (lowMeanShapeInt 1) (.atom (lowMeanFiberCertificate f).h)) < 1 := by
    have hr : (1 : ℝ) - lowMeanFractionReal (lowMeanFiberCertificate f).h < 1 := by linarith
    simpa only [lowMean_shape_sub, lowMean_shape_int, lowMeanIntegerShapeReal, Int.cast_one] using hr
  rw [lowMean_shape_closedMaximum _ _ hr0 hr1] at hR
  exact ⟨by simpa only [lowMeanIntegerShapeReal] using hL.symm,
    by simpa only [lowMean_shape_sub, lowMean_shape_int, lowMeanIntegerShapeReal, Int.cast_one] using hR.symm⟩

theorem lowMean_fiber_core_shape (f : LowMeanFiberInput) (j : ℤ)
    (hgL : lowMeanFractionReal f.gL = lowMeanClosedMaximum f.M (lowMeanFractionReal (lowMeanFiberCertificate f).l))
    (hgR : lowMeanFractionReal f.gR = lowMeanClosedMaximum f.M (1 - lowMeanFractionReal (lowMeanFiberCertificate f).h)) :
    j ∈ lowMeanFiberCore f ↔
      0 < lowMeanIntegerShapeReal (lowMeanShapeCoreFirst (lowMeanFiberCertificate f) f.M j f.zeta f.gL f.gR) ∧
      0 < lowMeanIntegerShapeReal (lowMeanShapeCoreSecond (lowMeanFiberCertificate f) f.M j f.zeta) := by
  rw [lowMean_shape_coreFirst _ _ _ _ _ _ hgL hgR, lowMean_shape_coreSecond]
  change (_ < _ ∧ _ + _ < _) ↔ (0 < _ - _ ∧ 0 < _ - _ - _)
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem lowMean_fiber_rank_membership (f : LowMeanFiberInput) (w : LowMeanCoreRankWitness)
    (hgL : lowMeanFractionReal f.gL = lowMeanClosedMaximum f.M (lowMeanFractionReal (lowMeanFiberCertificate f).l))
    (hgR : lowMeanFractionReal f.gR = lowMeanClosedMaximum f.M (1 - lowMeanFractionReal (lowMeanFiberCertificate f).h))
    (h : lowMeanCoreRankCheck f w = true) :
    w.state = 2 ↔ w.j ∈ lowMeanFiberCore f := by
  rw [lowMean_fiber_core_shape f w.j hgL hgR]
  simp only [lowMeanCoreRankCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hs : w.state ≤ 2 := h.1
  have hz : lowMeanFractionReal (0, 1) = (0 : ℝ) := by simp [lowMeanFractionReal]
  interval_cases ht : w.state
  · simp only [ite_true] at h
    have hn := lowMean_integerLower_sound h.2
    rw [hz] at hn
    change 0 ≤ -lowMeanIntegerShapeReal (lowMeanShapeCoreFirst (lowMeanFiberCertificate f) f.M w.j f.zeta f.gL f.gR) at hn
    constructor
    · intro hx; omega
    · intro hx; linarith [hx.1]
  · simp only [show ¬ (1 : ℕ) = 0 by decide, ite_false, ite_true] at h
    have hn := lowMean_integerLower_sound h.2
    rw [hz] at hn
    change 0 ≤ -lowMeanIntegerShapeReal (lowMeanShapeCoreSecond (lowMeanFiberCertificate f) f.M w.j f.zeta) at hn
    constructor
    · intro hx; omega
    · intro hx; linarith [hx.2]
  · simp only [show ¬ (2 : ℕ) = 0 by decide, show ¬ (2 : ℕ) = 1 by decide, ite_false, Bool.and_eq_true] at h
    exact ⟨fun _ => ⟨by simpa only [hz] using lowMean_integerPositive_sound h.2.1,
      by simpa only [hz] using lowMean_integerPositive_sound h.2.2⟩, fun _ => rfl⟩

/-- Explicit boundary checks prove the finite window sufficient for every
integer rank, including both infinite tails. -/
theorem lowMean_fiber_core_in_range (f : LowMeanFiberInput)
    (hmeta : lowMeanFiberMetaCheck f = true) (hgeo : lowMeanFiberGeometryCheck f = true)
    {j : ℤ} (hj : j ∈ lowMeanFiberCore f) : f.lo < j ∧ j < f.hi := by
  have hm := hmeta
  simp only [lowMeanFiberMetaCheck, Bool.and_eq_true, decide_eq_true_eq] at hm
  have hi : f.certificate - 1 < 28 := by omega
  have heta := (lowMean_certificate_signs _ hi).2.2.1
  change 0 < lowMeanFractionReal (lowMeanFiberCertificate f).eta at heta
  simp only [lowMeanFiberGeometryCheck, Bool.and_eq_true] at hgeo
  have hls := lowMean_integerLower_sound hgeo.1.1.1.2
  have hrs := lowMean_integerLower_sound hgeo.1.1.2
  have hlt := lowMean_integerLower_sound hgeo.1.2
  have hrt := lowMean_integerLower_sound hgeo.2
  have hz : lowMeanFractionReal (0, 1) = (0 : ℝ) := by simp [lowMeanFractionReal]
  simp only [hz, lowMean_shape_coreLeftSide] at hls
  simp only [hz, lowMean_shape_coreRightSide] at hrs
  simp only [hz, lowMean_shape_coreLeftTail] at hlt
  simp only [hz, lowMean_shape_coreRightTail] at hrt
  apply lowMean_core_in_range f.M f.lo f.hi heta hm.1.2.2.1 hm.1.2.2.2.1
    (by linarith) (by linarith) (by linarith) (by linarith) hj

theorem lowMean_fiber_window_row (f : LowMeanFiberInput) (h : lowMeanFiberWindowCheck f = true)
    (k : ℕ) (hk : k < f.ranks.length) :
    (lowMeanCoreRankAt f k).j = f.lo + (k : ℤ) ∧
      ((lowMeanCoreRankAt f k).state = 2 ↔ (lowMeanCoreRankAt f k).j ∈ f.core) ∧
      lowMeanCoreRankCheck f (lowMeanCoreRankAt f k) = true := by
  have hr := Erdos993Lean.F4Fast.forall_lt_of_range_all h k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  exact ⟨hr.1.1, hr.1.2, hr.2⟩

/-- Every checked core list equals the printed analytic core over ℤ.
The generated finite window is discharged by the preceding tail theorem. -/
theorem lowMean_fiber_core_exact (f : LowMeanFiberInput) (h : lowMeanFiberCheck f = true) (j : ℤ) :
    j ∈ lowMeanFiberCore f ↔ j ∈ f.core := by
  simp only [lowMeanFiberCheck, Bool.and_eq_true] at h
  obtain ⟨hgl, hgr⟩ := lowMean_fiber_g_values f h.1.1 h.1.2
  have hm := h.1.1
  simp only [lowMeanFiberMetaCheck, Bool.and_eq_true, decide_eq_true_eq] at hm
  have hrow (hjlo : f.lo ≤ j) (hjhi : j ≤ f.hi) : j ∈ lowMeanFiberCore f ↔ j ∈ f.core := by
    let k := (j - f.lo).toNat
    have hkI : (k : ℤ) = j - f.lo := Int.toNat_of_nonneg (by omega)
    have hlen := hm.1.2.2.2.2.1
    have hk : k < f.ranks.length := by rw [hlen]; omega
    obtain ⟨hkey, hcore, hcheck⟩ := lowMean_fiber_window_row f h.2 k hk
    have hjkey : (lowMeanCoreRankAt f k).j = j := by omega
    have hr := lowMean_fiber_rank_membership f (lowMeanCoreRankAt f k) hgl hgr hcheck
    rw [hjkey] at hr hcore
    exact hr.symm.trans hcore
  constructor
  · intro hj
    have hr := lowMean_fiber_core_in_range f h.1.1 h.1.2 hj
    exact (hrow hr.1.le hr.2.le).mp hj
  · intro hj
    have hr : f.lo ≤ j ∧ j ≤ f.hi := of_decide_eq_true (List.all_eq_true.mp hm.2 j hj)
    exact (hrow hr.1 hr.2).mpr hj

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_fiber_core_exact
