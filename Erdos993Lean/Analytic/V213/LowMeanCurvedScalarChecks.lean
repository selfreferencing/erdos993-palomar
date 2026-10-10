module

public import Erdos993Lean.Analytic.V213.LowMeanCurvedScalarData
public import Erdos993Lean.Analytic.V213.LowMeanCertificateFacts

/-!
The six exact printed curved fractions and three eq62 ratio floors.
Both families use grouped Int/Nat kernel decisions. The switch comparison
is consumed only when the interval meets its low limit.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanCurvedAt (i : ℕ) : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × ℕ :=
  lowMeanCurvedRecords.getD i (lowMeanCertificate01, .atom (0, 1), (0, 1), 0)
def lowMeanCurvedRecordShape (r : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × ℕ) : LowMeanIntegerShape :=
  if r.2.2.2 = 2 then lowMeanCertificateCurvedHD r.1 (.atom r.1.l)
  else lowMeanCertificateCurvedH r.1 (.atom (if r.2.2.2 = 1 then r.1.h else r.1.l))
noncomputable def lowMeanCurvedRecordValue (r : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × ℕ) : ℝ :=
  let c := r.1
  if r.2.2.2 = 2 then lowMeanCurvedHD (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
    (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D) (lowMeanFractionReal c.l)
  else lowMeanCurvedH (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
    (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D)
    (lowMeanFractionReal (if r.2.2.2 = 1 then c.h else c.l))

@[simp] theorem lowMean_curvedRecord_real (r : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × ℕ) :
    lowMeanIntegerShapeReal (lowMeanCurvedRecordShape r) = lowMeanCurvedRecordValue r := by
  unfold lowMeanCurvedRecordShape lowMeanCurvedRecordValue
  dsimp only
  split_ifs <;> simp [lowMeanIntegerShapeReal]

def lowMeanCurvedCheck (i : ℕ) : Bool :=
  let r := lowMeanCurvedAt i
  lowMeanIntegerEqualityCheck r.2.1 (lowMeanCurvedRecordShape r) r.2.2.1 &&
    decide (lowMeanFractionValid r.2.2.1 ∧ if i < 4 then r.2.2.1.1 < 0 else 0 < r.2.2.1.1)

theorem lowMean_curved_kernel : (List.range 6).all lowMeanCurvedCheck = true := by
  decide +kernel

theorem lowMean_curved_values_exact (i : ℕ) (hi : i < 6) :
    lowMeanCurvedRecordValue (lowMeanCurvedAt i) = lowMeanFractionReal (lowMeanCurvedAt i).2.2.1 := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_curved_kernel i hi
  simp only [lowMeanCurvedCheck, Bool.and_eq_true] at h
  simpa only [lowMean_curvedRecord_real] using lowMean_integerEquality_sound h.1

theorem lowMean_curved_signs (i : ℕ) (hi : i < 6) :
    if i < 4 then lowMeanCurvedRecordValue (lowMeanCurvedAt i) < 0 else 0 < lowMeanCurvedRecordValue (lowMeanCurvedAt i) := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_curved_kernel i hi
  simp only [lowMeanCurvedCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [lowMean_curved_values_exact i hi]
  have hd := lowMean_fraction_den_pos h.2.1
  split_ifs with hn
  · have hv : (lowMeanCurvedAt i).2.2.1.1 < 0 := by simpa [hn] using h.2.2
    exact div_neg_of_neg_of_pos (by exact_mod_cast hv) hd
  · have hv : 0 < (lowMeanCurvedAt i).2.2.1.1 := by simpa [hn] using h.2.2
    exact div_pos (by exact_mod_cast hv) hd

def lowMeanRatioAt (i : ℕ) : LowMeanCertificateInput × lowMeanFraction × LowMeanIntegerExpr × LowMeanIntegerExpr × ℕ :=
  lowMeanRatioRecords.getD i (lowMeanCertificate01, (0, 1), .atom (0, 1), .atom (0, 1), 1)
def lowMeanRatioCheck (i : ℕ) : Bool :=
  let r := lowMeanRatioAt i
  decide (0 < r.2.2.2.2 ∧ r.2.2.2.2 ≤ 28 ∧ r.1 = lowMeanCertificateAt (r.2.2.2.2 - 1) ∧
    lowMeanFractionValid r.2.1 ∧ 0 ≤ r.2.1.1) &&
    lowMeanIntegerLowerCheck r.2.2.1 (lowMeanCertificateRatioHigh r.1 r.2.1) (0, 1) &&
    (if lowMeanFractionLT r.1.l (3, 7) ∧ lowMeanFractionLE (3, 7) r.1.h then
      lowMeanIntegerLowerCheck r.2.2.2.1 (lowMeanCertificateRatioSwitch r.2.1) (0, 1) else true)

theorem lowMean_ratios_kernel : (List.range 3).all lowMeanRatioCheck = true := by
  decide +kernel

/-- The three actual equation-62 floors on their complete closed intervals,
including the switch's actual upper branch. -/
theorem lowMean_ratio_floors (i : ℕ) (hi : i < 3) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanRatioAt i).1.l) (lowMeanFractionReal (lowMeanRatioAt i).1.h)) :
    lowMeanFractionReal (lowMeanRatioAt i).2.1 ≤ lowMeanRate q / q := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_ratios_kernel i hi
  simp only [lowMeanRatioCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hk := h.1.1
  have hidx : (lowMeanRatioAt i).2.2.2.2 - 1 < 28 := by omega
  have hc := hk.2.2.1
  obtain ⟨hl, hh, _⟩ := lowMean_certificate_interval_facts _ hidx
  rw [← hc] at hl hh
  have hhigh := lowMean_integerLower_sound h.1.2
  simp only [lowMean_certificate_ratioHigh_real, show lowMeanFractionReal (0, 1) = (0 : ℝ) by simp [lowMeanFractionReal]] at hhigh
  apply lowMean_rateRatio_floor hl (by linarith) hq (by linarith)
  intro hllow hhswitch
  have hlv : lowMeanFractionValid (lowMeanRatioAt i).1.l := by
    rw [hc]
    exact lowMean_certificate_fraction_valid _ hidx _ (by simp [lowMeanCertificateFractions])
  have hhv : lowMeanFractionValid (lowMeanRatioAt i).1.h := by
    rw [hc]
    exact lowMean_certificate_fraction_valid _ hidx _ (by simp [lowMeanCertificateFractions])
  have hgl := (lowMean_fraction_lt_iff hlv (show lowMeanFractionValid (3, 7) by decide)).mpr
    (show lowMeanFractionReal (lowMeanRatioAt i).1.l < lowMeanFractionReal (3, 7) by simpa [lowMeanFractionReal] using hllow)
  have hgh := (lowMean_fraction_le_iff (show lowMeanFractionValid (3, 7) by decide) hhv).mpr
    (show lowMeanFractionReal (3, 7) ≤ lowMeanFractionReal (lowMeanRatioAt i).1.h by simpa [lowMeanFractionReal] using hhswitch)
  have hsw := h.2
  rw [ite_eq_left ⟨hgl, hgh⟩] at hsw
  have hs := lowMean_integerLower_sound hsw
  simp only [lowMean_certificate_ratioSwitch_real, show lowMeanFractionReal (0, 1) = (0 : ℝ) by simp [lowMeanFractionReal]] at hs
  linarith

theorem lowMean_ratio_nonnegative (i : ℕ) (hi : i < 3) : 0 ≤ lowMeanFractionReal (lowMeanRatioAt i).2.1 := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_ratios_kernel i hi
  simp only [lowMeanRatioCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact div_nonneg (by exact_mod_cast h.1.1.2.2.2.2) (lowMean_fraction_den_pos h.1.1.2.2.2.1).le

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_curved_signs
#print axioms Erdos993Lean.Analytic.V213.lowMean_ratio_floors
